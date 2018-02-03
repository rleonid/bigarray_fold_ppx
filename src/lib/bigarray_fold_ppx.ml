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

let constrain_vec kind layout_s vec_var =
  let t1, t2 = kind_to_types kind in
  let econstr s = Typ.constr (lid s) [] in
  Pat.constraint_ (Pat.var (to_str vec_var))
    (Typ.constr (lid "Array1.t")
       [ econstr t1; econstr t2; econstr layout_s])

let make_let ?layout ?(arg="a") kind fold_var exp1 app =
  let to_body ls = Exp.fun_ Nolabel None (constrain_vec kind ls arg) exp1 in
  let body =
    match layout with
(*#if OCAML_VERSION >= (4, 05, 0)
    | None    -> let loc = { exp1.pexp_loc with Location.loc_ghost = true } in
                 Exp.newtype (Location.mkloc "l" loc) (to_body "l")
#else*)
    | None    -> Exp.newtype "l" (to_body "l")
(*#endif*)
    | Some ls -> to_body ls
  in
  Exp.let_ Nonrecursive [ Vb.mk (Pat.var (to_str fold_var)) body] app

let make_ref var init exp =
  Exp.let_ Nonrecursive
    [ Vb.mk (Pat.var (to_str var))
        (Exp.apply (ex_id "ref") [Nolabel, init])]
    exp

let lookup_ref var =
  Exp.apply (ex_id "!") [Nolabel, (ex_id var)]

(* This is an operator! *)
let assign_ref var val_exp =
  Exp.apply (ex_id ":=") [(Nolabel, (ex_id var)); (Nolabel, val_exp)]

let get_array1 arr index =
  Exp.apply (ex_id "Array1.unsafe_get") [(Nolabel, (ex_id arr)); (Nolabel, (ex_id index))]

let apply_f fold_f args =
  Exp.apply fold_f (List.map (fun e -> Nolabel,e) args)

(*let apply_f ~upto fold_f var arr index =
  if upto
  then Exp.apply fold_f [("", lookup_ref var); ("", get_array1 arr index)]
  else Exp.apply fold_f [("", get_array1 arr index); ("", lookup_ref var)] *)

let make_for_loop index start_exp end_exp upto body_exp =
  if upto
  then Exp.for_ (Pat.var (to_str index)) start_exp end_exp Upto body_exp
  else Exp.for_ (Pat.var (to_str index)) end_exp start_exp Downto body_exp

let const_int n = Pconst_integer (string_of_int n, None)

let length_expr ~minus_one arr =
  if minus_one then
    Exp.apply (ex_id "-")
      [ Nolabel, (Exp.apply (ex_id "Array1.dim") [Nolabel,(ex_id arr)])
      ; Nolabel, (Exp.constant (const_int 1))]
  else
    Exp.apply (ex_id "Array1.dim") [Nolabel, (ex_id arr)]

type e = Parsetree.expression

type operation =
  | Iter of e * e               (* f and v *)
  | Fold of (bool * e * e * e)  (* upto, f, init, v*)

let fold_apply_f ~upto fun_exp ~ref ~arr ~index =
  if upto then
    apply_f fun_exp [ lookup_ref ref; get_array1 arr index]
  else
    apply_f fun_exp [ get_array1 arr index; lookup_ref ref]

let fold_body ?(vec_arg="a") ~upto ~start ~minus_one fun_exp init =
  (make_ref "r" init
     (Exp.sequence
        (make_for_loop "i"
          (Exp.constant (const_int start))
          (length_expr ~minus_one vec_arg)
          upto
          (assign_ref "r"
            (fold_apply_f ~upto fun_exp ~ref:"r" ~arr:vec_arg ~index:"i")))
        (lookup_ref "r")))

let iter_body ?(vec_arg="a") ~upto ~start ~minus_one fun_exp =
  make_for_loop "i"
    (Exp.constant (const_int start))
    (length_expr ~minus_one vec_arg)
    upto
    (apply_f fun_exp [get_array1 vec_arg "i"])

let operation_to_name_n_body = function
  | Iter (f, v)              -> "iter",       (iter_body ~upto:true f),       v
  | Fold (true, f, init, v)  -> "fold_left",  (fold_body ~upto:true f init),  v
  | Fold (false, f, init, v) -> "fold_right", (fold_body ~upto:false f init), v

(* Create a fast iter/fold using a reference and for-loop. *)
let create_layout_specific op kind layout =
  let open Ast_helper in
  let layout, start, minus_one = to_fold_params layout in
  let name, body, v = operation_to_name_n_body op in
  make_let ~layout kind name (body ~start ~minus_one) (Exp.apply (ex_id name) [Nolabel, v])

(* Create a layout agnostic fold/iter function. *)
let create op kind =
  let name, body, v = operation_to_name_n_body op in
  let name_f = name ^ "_fortran" in
  let name_c = name ^ "_c" in
  make_let ~arg:"b" kind name
    (let layout, start, minus_one = to_fold_params (L Fortran_layout) in
    make_let ~layout kind name_f (body ~start ~minus_one)
      (* intended variable masking *)
      (let layout, start, minus_one = to_fold_params (L C_layout) in
      make_let ~layout kind name_c (body ~start ~minus_one)
        (Exp.match_ (Exp.apply (ex_id "Array1.layout") [Nolabel, (ex_id "b")])
          [ Exp.case (Pat.construct (lid "Fortran_layout") None)
              (Exp.apply (ex_id name_f) [Nolabel, (ex_id "b")])
          ; Exp.case (Pat.construct (lid "C_layout") None)
              (Exp.apply (ex_id name_c) [Nolabel, (ex_id "b")])])))
    (Exp.apply (ex_id name) [Nolabel, v])

let to_fs = function | true -> "fold_left" | false -> "fold_right"

let parse_fold_args loc d lst =
  match List.assoc (Labelled "f") lst with
  | fun_exp ->
      begin match List.assoc (Labelled "init") lst with
      | init_exp ->
          begin match List.assoc Nolabel lst with
          | array_exp -> Fold (d, fun_exp, init_exp, array_exp)
          | exception Not_found ->
              location_error ~loc "Missing unlabeled array1 argument to %s."
                (to_fs d)
          end
      | exception Not_found ->
          location_error ~loc "Missing labeled init argument to %s." (to_fs d)
      end
  | exception Not_found ->
      let n = List.length lst in
      if n < 3 then
        location_error ~loc "Missing %s arguments." (to_fs d)
      else if n > 3 then
        location_error ~loc "Too many arguments to %s." (to_fs d)
      else
        begin match lst with
        | [ (Nolabel, fun_exp)
          ; (Nolabel, init_exp)
          ; (Nolabel, array_exp)
          ] -> Fold (d, fun_exp, init_exp, array_exp)
        | _ ->
          location_error ~loc "Missing labeled f argument to %s." (to_fs d)
        end

let parse_iter_args loc lst =
  match List.assoc (Labelled "f") lst with
  | fun_exp ->
      begin match List.assoc Nolabel lst with
      | array_exp -> Iter (fun_exp, array_exp)
      | exception Not_found ->
          location_error ~loc "Missing unlabeled array1 argument to iter."
      end
  | exception Not_found  ->
      let n = List.length lst in
      if n < 2 then
        location_error ~loc "Missing iter arguments"
      else if n > 2 then
        location_error ~loc "Too many argument to iter"
      else
        begin match lst with
        | [ (Nolabel, fun_exp)
          ; (Nolabel, array_exp)
          ] -> Iter (fun_exp, array_exp)
        | _ ->
          location_error ~loc "Missing unlabeled \"f\" argument to iter."
        end

let parse_payload ~loc = function
  | [{pstr_desc =
        Pstr_eval
          ({pexp_desc =
              Pexp_apply ({pexp_desc =
                Pexp_ident {txt = Longident.Lident f}}, args)}, _)}] ->
      begin match f with
        | "fold_left"  -> parse_fold_args loc true args
        | "fold_right" -> parse_fold_args loc false args
        | "iter"       -> parse_iter_args loc args
        | operation    -> location_error ~loc "Unrecognized command: %s" operation
      end
  | [] -> location_error ~loc "Missing fold_left, fold_right or iter invocation."
  | _  -> location_error ~loc "Incorrect fold_left, fold_right or iter invocation."

let parse_layout ~loc = function
  | None            -> None
  | Some "fortran"  -> Some (L Fortran_layout)
  | Some "c"        -> Some (L C_layout)
  | Some ls         -> location_error ~loc "Unrecognized layout: %s" ls

let parse ?layout loc ~kind payload =
  try
    let kind   = parse_kind ~loc kind in
    let op     = parse_payload ~loc payload in
    match parse_layout ~loc layout with
    | None   -> create op kind
    | Some l -> create_layout_specific op kind l
  with Location.Error e ->
    Exp.extension ~loc (extension_of_error e)

let transform loc txt payload def =
  match split '.' txt with
  | ["array1"; kind]         -> parse loc ~kind payload
  | ["array1"; kind; layout] -> parse ~layout loc ~kind payload
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