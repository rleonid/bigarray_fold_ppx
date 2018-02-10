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

let get ~open_ arr index_ex =
  Exp.apply (ex_id (opened ~open_ "unsafe_get"))
    (unlabeled [ex_id arr; index_ex])

let set ~open_ arr index_ex new_value_ex =
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

let let_unit exp =
  let unit_l = lid "()" in
  Exp.let_ Nonrecursive [ Vb.mk (Pat.construct unit_l None) exp]
    (Exp.construct unit_l None)

type config =
  { open_ : bool                        (* Is the function invocation in an open
                                                          (ex. Array1) place? *)
  ; with_index  : bool            (* Pass the position index to the function? *)
  ; lambda      : Parsetree.expression               (* The function/lambda . *)
  }

let fold_apply_f { open_; with_index; lambda } ~upto ~ref_ ~index arr =
  let index_ex = ex_id index in
  if with_index then
    if upto then
      apply_f lambda [ lookup_ref ref_; index_ex; get ~open_ arr index_ex]
    else
      apply_f lambda [ index_ex; get ~open_ arr index_ex; lookup_ref ref_]
  else
    if upto then
      apply_f lambda [ lookup_ref ref_; get ~open_ arr index_ex]
    else
      apply_f lambda [ get ~open_ arr index_ex; lookup_ref ref_]

(* TODO:
 * Generalize the variable naming mechanism, such that if a user passes an
 * initialial value as 'r' or an function as 'i' (for example), this will
 * still compile.
 * *)
let fold_body ?(arr_arg="a") ?(ref_="r") ?(index="i") c
    ~upto ~start ~minus_one init =
  let start_exp = Exp.constant (const_int start) in
  let end_exp = length_expr ~open_:c.open_ ~minus_one arr_arg in
  make_ref ref_ init
    (Exp.sequence
      (make_for_loop index ~start_exp ~end_exp upto
        (assign_ref ref_
          (fold_apply_f c ~upto ~ref_ ~index arr_arg)))
      (lookup_ref ref_))

let reduce_body ?(arr_arg="a") ?(ref_="r") ?(index="i") c
    ~upto ~start ~minus_one =
  let first_index, start_exp, end_exp, dir =
    let li = length_expr ~open_:c.open_ ~minus_one arr_arg in
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
  make_ref ref_ (get ~open_:c.open_ arr_arg first_index)
    (Exp.sequence
      (Exp.for_ (Pat.var (to_str index)) start_exp end_exp dir
        (assign_ref ref_
          (fold_apply_f c ~upto ~ref_ ~index arr_arg)))
      (lookup_ref ref_))

let gen_fold_body c ~upto ~start ~minus_one = function
  | None      -> reduce_body c ~upto ~start ~minus_one
  | Some init -> fold_body c ~upto ~start ~minus_one init

let iter_body ?(arr_arg="a") ?(index="i")
  { open_; with_index; lambda } ~upto ~start ~minus_one =
  let index_ex = ex_id index in
  make_for_loop index
    ~start_exp:(Exp.constant (const_int start))
    ~end_exp:(length_expr ~open_ ~minus_one arr_arg)
    upto
    (let_unit
      (if with_index then
        apply_f lambda [index_ex; get ~open_ arr_arg index_ex]
      else
        apply_f lambda [get ~open_ arr_arg index_ex]))

let modify_body ?(arr_arg="a") ?(index="i")
  { open_; with_index; lambda } ~upto ~start ~minus_one =
  let index_ex = ex_id index in
  let new_value_exp =
    if with_index then
       apply_f lambda [index_ex; get ~open_ arr_arg index_ex]
     else
       apply_f lambda [get ~open_ arr_arg index_ex]
  in
  make_for_loop index
    ~start_exp:(Exp.constant (const_int start))
    ~end_exp:(length_expr ~open_ ~minus_one arr_arg)
    upto
    (set ~open_ arr_arg index_ex new_value_exp)

module Operation = struct

  type t =
    (* 'acc -> 'a -> 'acc *)
    | Fold of { config  : config
              ; left    : bool
              (* fold_ left or right? *)
              ; init    : Parsetree.expression option
              (* optional init value,without one create a reduce instead. *)
              }

    (* 'a -> unit *)
    | Iter of config

    (* 'a -> 'b, value <- 'b *)
    | Modify of config

  let fold_to_name with_index init left =
    sprintf "%s%s_%s"
      (match init with | None -> "reduce" | Some _ -> "fold")
      (if with_index then "i" else "")
      (if left then "left" else "right")

  let to_name = function
    | Iter { with_index = false }   -> "iter"
    | Iter { with_index = true }    -> "iteri"
    | Fold { config; init; left }   -> fold_to_name config.with_index init left
    | Modify { with_index = false } -> "modify"
    | Modify { with_index = true }  -> "modifyi"

  let to_body = function
    | Iter config                -> iter_body config ~upto:true
    | Modify config              -> modify_body config ~upto:true
    | Fold { config; left; init} -> gen_fold_body config ~upto:left init

  let open_ = function
    | Iter config | Modify config | Fold { config; _ } -> config.open_

end (* Operation *)


(* Create a fast iter/fold using a reference and for-loop. *)
module Create = struct

  let layout_specific ~open_ op array1 kind layout =
    let open Ast_helper in
    let layout, start, minus_one = to_fold_params layout in
    let name = Operation.to_name op in
    let body = Operation.to_body op in
    make_let ~layout ~open_ kind name (body ~start ~minus_one)
      (Exp.apply (ex_id name) (unlabeled [array1]))

  (* Create a layout agnostic fold/iter function. *)
  let layout_agnostic ~open_ op array1 kind =
    let name = Operation.to_name op in
    let body = Operation.to_body op in
    let open_ = Operation.open_ op in
    let name_f = name ^ "_fortran" in
    let name_c = name ^ "_c" in
    (* This variable renaming isn't necessary, it just makes the code, as output
    * -dsource, eaiser to read. *)
    let arg = "b" in
    let arg_ex = [Nolabel, ex_id arg] in
    make_let ~arg ~open_ kind name
      (let layout, start, minus_one = to_fold_params (L Fortran_layout) in
      make_let ~layout ~open_ kind name_f (body ~start ~minus_one)
        (* intended variable masking *)
        (let layout, start, minus_one = to_fold_params (L C_layout) in
        make_let ~layout ~open_ kind name_c (body ~start ~minus_one)
          (Exp.match_ (Exp.apply (ex_id (opened ~open_ "layout")) arg_ex)
            [ Exp.case (Pat.construct (lid "Fortran_layout") None)
                (Exp.apply (ex_id name_f) arg_ex)
            ; Exp.case (Pat.construct (lid "C_layout") None)
                (Exp.apply (ex_id name_c) arg_ex)])))
      (Exp.apply (ex_id name) [ Nolabel, array1])

end (* Create *)

module Parse = struct

  let to_fs = function | true -> "fold_left" | false -> "fold_right"

  let fold_args_unlabled loc ~open_ ~with_index left lst =
    let n = List.length lst in
    if n < 3 then
      location_error ~loc "Missing %s arguments." (to_fs left)
    else if n > 3 then
      location_error ~loc "Too many arguments to %s." (to_fs left)
    else
      match lst with
      | [ Nolabel, lambda; Nolabel, init; Nolabel, v ] ->
          let config = {open_; with_index; lambda} in
          Operation.Fold { config; left; init = Some init}, v
      | _ ->
        location_error ~loc "Missing labeled f argument to %s." (to_fs left)

  let fold_args loc ~open_ ~with_index left lst =
    match List.assoc (Labelled "f") lst with
    | lambda ->
        begin match List.assoc (Labelled "init") lst with
        | init ->
            begin match List.assoc Nolabel lst with
            | v -> let config = {open_; with_index; lambda} in
                   Operation.Fold { config ; left; init = Some init}, v
            | exception Not_found ->
                location_error ~loc "Missing unlabeled array1 argument to %s."
                  (to_fs left)
            end
        | exception Not_found ->
            location_error ~loc "Missing labeled init argument to %s." (to_fs left)
        end
    | exception Not_found ->
        fold_args_unlabled loc ~open_ ~with_index left lst

  let initless_args loc lst funs k =
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

  let iter_args loc ~open_ ~with_index lst =
    initless_args loc lst "iter"
      (fun lambda v -> Operation.Iter {open_; with_index; lambda}, v)

  let modify_args loc ~open_ ~with_index lst =
    initless_args loc lst "modify"
      (fun lambda v -> Operation.Modify {open_; with_index; lambda}, v)

  let reduce_args loc ~open_ ~with_index left lst =
    initless_args loc lst "reduce"
      (fun lambda v ->
         let config = {open_; with_index; lambda} in
         Operation.Fold { config; left; init = None}, v)

  let payload ~loc ~open_ = function
    | [ { pstr_desc =
          Pstr_eval
            ( { pexp_desc =
                Pexp_apply ( { pexp_desc =
                  Pexp_ident {txt = Longident.Lident f}}, args)}, _)}] ->
        begin match f with
        | "fold_left"     -> fold_args loc ~open_ ~with_index:false true args
        | "fold_right"    -> fold_args loc ~open_ ~with_index:false false args
        | "foldi_left"    -> fold_args loc ~open_ ~with_index:true true args
        | "foldi_right"   -> fold_args loc ~open_ ~with_index:true false args
        | "reduce_left"   -> reduce_args loc ~open_ ~with_index:false true args
        | "reduce_right"  -> reduce_args loc ~open_ ~with_index:false false args
        | "reducei_left"  -> reduce_args loc ~open_ ~with_index:true true args
        | "reducei_right" -> reduce_args loc ~open_ ~with_index:true false args
        | "iter"          -> iter_args loc ~open_ ~with_index:false args
        | "iteri"         -> iter_args loc ~open_ ~with_index:true args
        | "modify"        -> modify_args loc ~open_ ~with_index:false args
        | "modifyi"       -> modify_args loc ~open_ ~with_index:true args
        | operation       -> location_error ~loc "Unrecognized command: %s" operation
        end
    | [] -> location_error ~loc "Missing fold_left, fold_right or iter invocation."
    | _  -> location_error ~loc "Incorrect fold_left, fold_right or iter invocation."

  let layout ~loc = function
    | None            -> None
    | Some "fortran"  -> Some (L Fortran_layout)
    | Some "c"        -> Some (L C_layout)
    | Some ls         -> location_error ~loc "Unrecognized layout: %s" ls

  let kind ~loc = function
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

end (* Parse *)

let create loc ~open_ ~kind payload layout =
  try
    let kind       = Parse.kind ~loc kind in
    let op, array1 = Parse.payload ~loc ~open_ payload in
    match Parse.layout ~loc layout with
    | None   -> Create.layout_agnostic ~open_ op array1 kind
    | Some l -> Create.layout_specific ~open_ op array1 kind l
  with Location.Error e ->
    Exp.extension ~loc (extension_of_error e)

let transform loc txt payload def =
  match split '.' txt with
  | [ "array1"; kind ]     -> create loc ~open_:false ~kind payload None
  | [ "array1"; kind; l ]  -> create loc ~open_:false ~kind payload (Some l)
  | [ "open1"; kind ]      -> create loc ~open_:true  ~kind payload None
  | [ "open1"; kind; l ]   -> create loc ~open_:true  ~kind payload (Some l)
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
