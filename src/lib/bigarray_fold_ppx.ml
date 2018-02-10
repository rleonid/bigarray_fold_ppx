(* Copyright {2016-2018} {Leonid Rozenberg}

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

open Ast_404
open Asttypes
open Parsetree
open Ast_mapper
open Ast_helper

open Printf
open Bigarray

(* Utilities *)
let split c s =
  let rec loop o =
    try
      let i = String.index_from s o c in
      (String.sub s o (i - o)) :: (loop (i + 1))
    with Not_found ->
      [String.sub s o (String.length s - o)]
  in
  loop 0

let location_error ?(sub=[]) ?(if_highlight="") ~loc fmt =
  Printf.ksprintf (fun msg ->
    raise Location.(Error { loc; msg; sub; if_highlight; }))
    fmt

(* Bigarray specific transforms *)
type k = K : ('a, 'b) kind -> k

let parse_kind ~loc = function
  | "float32"         -> K Float32
  | "float64"         -> K Float64
  | "complex32"       -> K Complex32
  | "complex64"       -> K Complex64
  | "int8_signed"     -> K Int8_signed
  | "int8_unsigned"   -> K Int8_unsigned
  | "int16_signed"    -> K Int16_signed
  | "int16_unsigned"  -> K Int16_unsigned
  | "int32"           -> K Int32
  | "int64"           -> K Int64
  | "int"             -> K Int
  | "nativeint"       -> K Nativeint
  | "char"            -> K Char
  | ks                -> location_error ~loc "Unrecognized kind: %s" ks

let kind_to_types = function
  | K Float32         -> "float", "float32_elt"
  | K Float64         -> "float", "float64_elt"
  | K Int8_signed     -> "int", "int8_signed_elt"
  | K Int8_unsigned   -> "int", "int8_unsigned_elt"
  | K Int16_signed    -> "int", "int16_signed_elt"
  | K Int16_unsigned  -> "int", "int16_unsigned_elt"
  | K Int32           -> "int32", "int32_elt"
  | K Int64           -> "int64", "int64_elt"
  | K Int             -> "int", "int_elt"
  | K Nativeint       -> "nativeint", "nativeint_elt"
  | K Complex32       -> "Complex.t","complex32_elt"
  | K Complex64       -> "Complex.t","complex64_elt"
  | K Char            -> "char", "int8_unsigned_elt"

type l = L : 'a layout -> l

let to_fold_params = function
  | L Fortran_layout -> "fortran_layout", 1, false
  | L C_layout       -> "c_layout", 0, true

(* AST construction helpers *)
let to_str s = Location.mkloc s Location.none

let lid s = Location.mkloc (Longident.parse s) Location.none

let ex_id s = Exp.ident (lid s)

let opened ~open_ s =
  if open_ then s else "Array1." ^ s

let constrain_vec ~open_ kind layout_s vec_var =
  let t1, t2 = kind_to_types kind in
  let econstr s = Typ.constr (lid s) [] in
  Pat.constraint_ (Pat.var (to_str vec_var))
    (Typ.constr (lid (opened ~open_ "t"))
       [ econstr t1; econstr t2; econstr layout_s])

let make_let ?layout ?(arg="a") ~open_ kind fold_var exp1 app =
  let to_body ls = Exp.fun_ Nolabel None (constrain_vec ~open_ kind ls arg) exp1 in
  let body =
    match layout with
    | None    -> Exp.newtype "l" (to_body "l")
    | Some ls -> to_body ls
  in
  Exp.let_ Nonrecursive [ Vb.mk (Pat.var (to_str fold_var)) body] app

let unlabeled lst =
  List.map (fun ex -> Nolabel, ex) lst

let make_ref var init exp =
  Exp.let_ Nonrecursive
    [ Vb.mk (Pat.var (to_str var))
        (Exp.apply (ex_id "ref") (unlabeled [init]))]
    exp

let lookup_ref var =
  Exp.apply (ex_id "!") (unlabeled [ex_id var])

(* This is an operator! *)
let assign_ref var val_exp =
  Exp.apply (ex_id ":=") (unlabeled [ex_id var; val_exp])

let get_array1 ~open_ arr index_ex =
  Exp.apply (ex_id (opened ~open_ "unsafe_get"))
    (unlabeled [ex_id arr; index_ex])

let set_array1 ~open_ arr index_ex new_value_ex =
  Exp.apply (ex_id (opened ~open_ "unsafe_set"))
    (unlabeled [ex_id arr; index_ex; new_value_ex])

let apply_f fold_f args =
  Exp.apply fold_f (unlabeled args)

let make_for_loop index ~start_exp ~end_exp upto body_exp =
  if upto
  then Exp.for_ (Pat.var (to_str index)) start_exp end_exp Upto body_exp
  else Exp.for_ (Pat.var (to_str index)) end_exp start_exp Downto body_exp

let const_int n = Pconst_integer (string_of_int n, None)

let mo_exp ~minus_one exp =
  if minus_one then
    Exp.apply (ex_id "-")
      (unlabeled [ exp ; Exp.constant (const_int 1) ])
  else
    exp

let length_expr ~open_ ~minus_one arr =
  let edim = ex_id (opened ~open_ "dim") in
  let arr_len_e = Exp.apply edim (unlabeled [ex_id arr]) in
  mo_exp ~minus_one arr_len_e

type e = Parsetree.expression

type operation =
  (* 'acc -> 'a -> 'acc *)
  | Fold of { open_ : bool
            ; i     : bool
            ; left  : bool
            ; f     : e
            ; init  : e option    (* None -> reduce *)
            ; v     : e
            }  (* upto, f, init, v*)
  (* 'a -> unit *)
  | Iter of { open_ : bool    (* Inside Array1? *)
            ; i     : bool    (* Add the index ?*)
            ; f     : e
            ; v     : e
            }
  (* 'a -> 'b, value <- 'b *)
  | Modify of { open_ : bool
              ; i : bool
              ; f : e
              ; v : e
              }

let fold_apply_f ~open_ ~i ~upto fun_exp ~ref ~arr ~index =
  let index_ex = ex_id index in
  if i then
    if upto then
      apply_f fun_exp [ lookup_ref ref; index_ex; get_array1 ~open_ arr index_ex]
    else
      apply_f fun_exp [ index_ex; get_array1 ~open_ arr index_ex; lookup_ref ref]
  else
    if upto then
      apply_f fun_exp [ lookup_ref ref; get_array1 ~open_ arr index_ex]
    else
      apply_f fun_exp [ get_array1 ~open_ arr index_ex; lookup_ref ref]

(* TODO:
 * Generalize the variable naming mechanism, such that if a user passes an
 * initialial value as 'r' or an function as 'i' (for example), this will
 * still compile.
 * *)

let fold_body ?(vec_arg="a") ~open_ ~i ~upto ~start ~minus_one fun_exp init =
  let start_exp = Exp.constant (const_int start) in
  let end_exp = length_expr ~open_ ~minus_one vec_arg in
  make_ref "r" init
    (Exp.sequence
      (make_for_loop "i" ~start_exp ~end_exp upto
        (assign_ref "r"
          (fold_apply_f ~open_ ~i ~upto fun_exp ~ref:"r" ~arr:vec_arg ~index:"i")))
      (lookup_ref "r"))

let reduce_body ?(vec_arg="a") ~open_ ~i ~upto ~start ~minus_one fun_exp =
  let first_index, start_exp, end_exp, dir =
    let li = length_expr ~open_ ~minus_one vec_arg in
    let fi = Exp.constant (const_int start) in
    if upto then
      fi
      , Exp.constant (const_int (start + 1))
      , li
      , Upto
    else
      li
      , (mo_exp ~minus_one:true li)
      , fi
      , Downto
  in
  make_ref "r" (get_array1 ~open_ vec_arg first_index)
    (Exp.sequence
      (Exp.for_ (Pat.var (to_str "i")) start_exp end_exp dir
        (assign_ref "r"
          (fold_apply_f ~open_ ~i ~upto fun_exp ~ref:"r" ~arr:vec_arg ~index:"i")))
      (lookup_ref "r"))

let gen_fold_body ?vec_arg ~open_ ~i ~upto ~start ~minus_one fun_exp = function
  | None      -> reduce_body ?vec_arg ~open_ ~i ~upto ~start ~minus_one fun_exp
  | Some init -> fold_body ?vec_arg ~open_ ~i ~upto ~start ~minus_one fun_exp init

let let_unit exp =
  let unit_l = lid "()" in
  Exp.let_ Nonrecursive [ Vb.mk (Pat.construct unit_l None) exp]
    (Exp.construct unit_l None)

let iter_body ?(vec_arg="a") ~open_ ~i ~upto ~start ~minus_one fun_exp =
  let index_c = "i" in
  let index_ex = ex_id index_c in
  make_for_loop index_c
    ~start_exp:(Exp.constant (const_int start))
    ~end_exp:(length_expr ~open_ ~minus_one vec_arg)
    upto
    (let_unit
      (if i then
        apply_f fun_exp [index_ex; get_array1 ~open_ vec_arg index_ex]
      else
        apply_f fun_exp [get_array1 ~open_ vec_arg index_ex]))

let modify_body ?(vec_arg="a") ~open_ ~i ~upto ~start ~minus_one fun_exp =
  let index_c = "i" in
  let index_ex = ex_id index_c in
  let new_value_exp =
    if i then
       apply_f fun_exp [index_ex; get_array1 ~open_ vec_arg index_ex]
     else
       apply_f fun_exp [get_array1 ~open_ vec_arg index_ex]
  in
  make_for_loop index_c
    ~start_exp:(Exp.constant (const_int start))
    ~end_exp:(length_expr ~open_ ~minus_one vec_arg)
    upto
    (set_array1 ~open_ vec_arg index_ex new_value_exp)

let fold_to_name i init left =
  sprintf "%s%s_%s"
    (match init with | None -> "reduce" | Some _ -> "fold")
    (if i then "i" else "")
    (if left then "left" else "right")

let operation_to_name = function
  | Iter { i = false }     -> "iter"
  | Iter { i = true }      -> "iteri"
  | Fold { i; init; left } -> fold_to_name i init left
  | Modify { i = false }   -> "modify"
  | Modify { i = true }    -> "modifyi"

let array_value = function
  | Iter { v } -> v
  | Fold { v } -> v
  | Modify { v } -> v

let operation_to_body = function
  | Iter { open_; i; f; v }             -> iter_body ~open_ ~i ~upto:true f
  | Fold { open_; i; left; f; init; v } -> gen_fold_body ~open_ ~i ~upto:left f init
  | Modify { open_; i; f; v }           -> modify_body ~open_ ~i ~upto:true f

(* Create a fast iter/fold using a reference and for-loop. *)
let create_layout_specific ~open_ op kind layout =
  let open Ast_helper in
  let layout, start, minus_one = to_fold_params layout in
  let name = operation_to_name op in
  let body = operation_to_body op in
  let v = array_value op in
  make_let ~layout ~open_ kind name (body ~start ~minus_one)
    (Exp.apply (ex_id name) (unlabeled [v]))

(* Create a layout agnostic fold/iter function. *)
let create ~open_ op kind =
  let name = operation_to_name op in
  let body = operation_to_body op in
  let v = array_value op in
  let name_f = name ^ "_fortran" in
  let name_c = name ^ "_c" in
  make_let ~arg:"b" ~open_ kind name
    (let layout, start, minus_one = to_fold_params (L Fortran_layout) in
    make_let ~layout ~open_ kind name_f (body ~start ~minus_one)
      (* intended variable masking *)
      (let layout, start, minus_one = to_fold_params (L C_layout) in
      make_let ~layout ~open_ kind name_c (body ~start ~minus_one)
        (Exp.match_ (Exp.apply (ex_id (opened ~open_ "layout")) [ Nolabel, (ex_id "b")])
          [ Exp.case (Pat.construct (lid "Fortran_layout") None)
              (Exp.apply (ex_id name_f) [ Nolabel, (ex_id "b")])
          ; Exp.case (Pat.construct (lid "C_layout") None)
              (Exp.apply (ex_id name_c) [ Nolabel, (ex_id "b")])])))
    (Exp.apply (ex_id name) [ Nolabel, v])

let to_fs = function | true -> "fold_left" | false -> "fold_right"

let parse_fold_args loc ~open_ ~i left lst =
  match List.assoc (Labelled "f") lst with
  | f ->
      begin match List.assoc (Labelled "init") lst with
      | init ->
          begin match List.assoc Nolabel lst with
          | v -> Fold { open_; i; left; f; init = Some init; v }
          | exception Not_found ->
              location_error ~loc "Missing unlabeled array1 argument to %s."
                (to_fs left)
          end
      | exception Not_found ->
          location_error ~loc "Missing labeled init argument to %s." (to_fs left)
      end
  | exception Not_found ->
      let n = List.length lst in
      if n < 3 then
        location_error ~loc "Missing %s arguments." (to_fs left)
      else if n > 3 then
        location_error ~loc "Too many arguments to %s." (to_fs left)
      else
        begin match lst with
        | [ Nolabel, f
          ; Nolabel, init
          ; Nolabel, v
          ] -> Fold { open_; i; left; f; init = Some init; v}
        | _ ->
          location_error ~loc "Missing labeled f argument to %s." (to_fs left)
        end

let parse_initless_args loc lst funs k =
  match List.assoc (Labelled "f") lst with
  | f ->
      begin match List.assoc Nolabel lst with
      | v -> k f v
      | exception Not_found ->
          location_error ~loc "Missing unlabeled array1 argument to %s." funs
      end
  | exception Not_found  ->
      let n = List.length lst in
      if n < 2 then
        location_error ~loc "Missing %s arguments" funs
      else if n > 2 then
        location_error ~loc "Too many argument to %s" funs
      else
        begin match lst with
        | [ Nolabel, f
          ; Nolabel, v
          ] -> k f v
        | _ ->
          location_error ~loc "Missing unlabeled \"f\" argument to %s." funs
        end

let parse_iter_args loc ~open_ ~i lst =
  parse_initless_args loc lst "iter"
    (fun f v -> Iter {open_; i; f; v})

let parse_modify_args loc ~open_ ~i lst =
  parse_initless_args loc lst "modify"
    (fun f v -> Modify {open_; i; f; v})

let parse_reduce_args loc ~open_ ~i left lst =
  parse_initless_args loc lst "reduce"
    (fun f v -> Fold {open_; i; f; v; left; init = None})

let parse_payload ~loc ~open_ = function
  | [ { pstr_desc =
        Pstr_eval
          ( { pexp_desc =
              Pexp_apply ( { pexp_desc =
                Pexp_ident {txt = Longident.Lident f}}, args)}, _)}] ->
      begin match f with
      | "fold_left"     -> parse_fold_args loc ~open_ ~i:false true args
      | "fold_right"    -> parse_fold_args loc ~open_ ~i:false false args
      | "foldi_left"    -> parse_fold_args loc ~open_ ~i:true true args
      | "foldi_right"   -> parse_fold_args loc ~open_ ~i:true false args
      | "reduce_left"   -> parse_reduce_args loc ~open_ ~i:false true args
      | "reduce_right"  -> parse_reduce_args loc ~open_ ~i:false false args
      | "reducei_left"  -> parse_reduce_args loc ~open_ ~i:true true args
      | "reducei_right" -> parse_reduce_args loc ~open_ ~i:true false args
      | "iter"          -> parse_iter_args loc ~open_ ~i:false args
      | "iteri"         -> parse_iter_args loc ~open_ ~i:true args
      | "modify"        -> parse_modify_args loc ~open_ ~i:false args
      | "modifyi"       -> parse_modify_args loc ~open_ ~i:true args
      | operation       -> location_error ~loc "Unrecognized command: %s" operation
      end
  | [] -> location_error ~loc "Missing fold_left, fold_right or iter invocation."
  | _  -> location_error ~loc "Incorrect fold_left, fold_right or iter invocation."

let parse_layout ~loc = function
  | None            -> None
  | Some "fortran"  -> Some (L Fortran_layout)
  | Some "c"        -> Some (L C_layout)
  | Some ls         -> location_error ~loc "Unrecognized layout: %s" ls

let parse ?layout loc ~open_ ~kind payload =
  try
    let kind   = parse_kind ~loc kind in
    let op     = parse_payload ~loc ~open_ payload in
    match parse_layout ~loc layout with
    | None   -> create ~open_ op kind
    | Some l -> create_layout_specific ~open_ op kind l
  with Location.Error e ->
    Exp.extension ~loc (extension_of_error e)

let transform loc txt payload def =
  match split '.' txt with
  | [ "array1"; kind ]          -> parse loc ~open_:false ~kind payload
  | [ "array1"; kind; layout ]  -> parse ~layout loc ~open_:false ~kind payload
  | [ "open1"; kind ]           -> parse loc ~open_:true ~kind payload
  | [ "open1"; kind; layout ]   -> parse ~layout loc ~open_:true ~kind payload
  | _ -> def ()

let bigarray_fold_mapper =
  { default_mapper with
    expr = fun mapper expr ->
      match expr with
      | { pexp_desc = Pexp_extension ({ txt }, PStr payload)} ->
          transform expr.pexp_loc txt payload (fun () -> default_mapper.expr mapper expr)
      | other -> default_mapper.expr mapper other; }

let rewriter _config _cookies =
  bigarray_fold_mapper

(* Registration *)

let () =
  let open Migrate_parsetree in
  Driver.register ~name:"bigarray_fold_ppx" Versions.ocaml_404 rewriter
