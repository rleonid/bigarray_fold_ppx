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

let location_error ?(sub=[]) ?(if_highlight="") ~loc fmt =
  Printf.ksprintf (fun msg ->
    raise Location.(Error { loc; msg; sub; if_highlight; }))
    fmt

(* Bigarray specific transforms *)
module K = struct

  type t = K : ('a, 'b) kind -> t

  let to_constraint_types = function
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

  let to_string = function
    | K Float32         -> "float32"
    | K Float64         -> "float64"
    | K Int8_signed     -> "int8_signed"
    | K Int8_unsigned   -> "int8_unsigned"
    | K Int16_signed    -> "int16_signed"
    | K Int16_unsigned  -> "int16_unsigned"
    | K Int32           -> "int32"
    | K Int64           -> "int64"
    | K Int             -> "int"
    | K Nativeint       -> "nativeint"
    | K Complex32       -> "complex32"
    | K Complex64       -> "complex64"
    | K Char            -> "char"

end (* K *)

type index_offset =
  | Aligned
  | AddOne
  | SubOne

module L = struct

  (* We rename and shorten the layout options so that matching against the can
   * be faster. *)
  type t =
    | F                                                     (* Fortran_layout *)
    | C                                                           (* C_layout *)

  (* layout name for constraint,
  * starting index,
  * minus one for ending point
  * suffix *)

  let loc = !Ast_helper.default_loc

  let start = function
    | F -> [%expr 1]
    | C -> [%expr 0]

  let minus_one = function
    | F -> false
    | C -> true

  let constraint_name = function
    | F -> "fortran_layout"
    | C -> "c_layout"

  let to_pattern_case = function
    | F -> "Fortran_layout"
    | C -> "C_layout"

  let to_name_suffix = function
    | F -> "_fortran"
    | C -> "_c"

  let to_index_offsets layout1 layout2 =
    match layout1, layout2 with
    | C, C -> Aligned
    | F, F -> Aligned
    | F, C -> SubOne
    | C, F -> AddOne

end (* L *)

(* AST construction helpers *)
let to_str s = Location.mkloc s Location.none

let lid s = Location.mkloc (Longident.parse s) Location.none

let e s = Exp.ident (lid s)

let unlabeled lst =
  List.map (fun ex -> Nolabel, ex) lst

let make_ref var init exp =
  Exp.let_ Nonrecursive
    [ Vb.mk (Pat.var (to_str var))
        (Exp.apply (e "ref") (unlabeled [init]))]
    exp

let lookup_ref var =
  Exp.apply (e "!") (unlabeled [e var])

(* This is an operator! *)
let assign_ref var val_exp =
  Exp.apply (e ":=") (unlabeled [e var; val_exp])

let apply f args =
  Exp.apply f (unlabeled args)

let let_unit exp =
  let unit_l = lid "()" in
  Exp.let_ Nonrecursive [ Vb.mk (Pat.construct unit_l None) exp]
    (Exp.construct unit_l None)

let constrain_vec t kind layout_s vec_var =
  let t1, t2 = K.to_constraint_types kind in
  let econstr s = Typ.constr (lid s) [] in
    Pat.constraint_ (Pat.var (to_str vec_var))
    (Typ.constr (lid t) [ econstr t1; econstr t2; econstr layout_s])
  (*[%pat? ([%p (to_str vec_var)] : [%type: ([%t t1], [%t t2], [%t layout_s]) [%t t]])] *)

let efor i s u e b =
  let loc = !Ast_helper.default_loc in
  if u then
    [%expr for [%p i] = [%e s] to [%e e] do [%e b] done]
  else
    [%expr for [%p i] = [%e e] downto [%e s] do [%e b] done]

module Common_config = struct

  type 'a t =
    { open_ : bool                        (* Is the function invocation in an open
                                                            (ex. Array1) place? *)
    ; with_index  : bool            (* Pass the position index to the function? *)
    ; lambda      : 'a                                 (* The function/lambda . *)
    }

  let init ~open_ ~with_index =
    { open_; with_index; lambda = () }

  let overwrite_lambda { open_ ; with_index; _ } lambda =
    { open_; with_index; lambda }

end (* Common_config *)

module Cc = Common_config

let remove_and_assoc el list =
  let rec loop acc = function
    | []                      -> raise Not_found
    | (e, v) :: t when e = el -> v, (List.rev acc @ t)
    | h :: t                  -> loop (h :: acc) t
  in
  loop [] list

module Common_parse = struct

  let layout ?(what="layout") ~loc = function
    | "fortran"  -> L.F
    | "c"        -> L.C
    | ls         -> location_error ~loc "Unrecognized %s: %s" what ls

  let kind ~loc = function
    | "float32"         -> K.K Float32
    | "float64"         -> K.K Float64
    | "complex32"       -> K.K Complex32
    | "complex64"       -> K.K Complex64
    | "int8_signed"     -> K.K Int8_signed
    | "int8_unsigned"   -> K.K Int8_unsigned
    | "int16_signed"    -> K.K Int16_signed
    | "int16_unsigned"  -> K.K Int16_unsigned
    | "int32"           -> K.K Int32
    | "int64"           -> K.K Int64
    | "int"             -> K.K Int
    | "nativeint"       -> K.K Nativeint
    | "char"            -> K.K Char
    | ks                -> location_error ~loc "Unrecognized kind: %s" ks

  let kind_or_layout ~loc s =
    try
      `K (kind ~loc s)
    with Location.Error _ ->
      `L (layout ~what:"kind or layout" ~loc s)

end (* Common_parse *)

module type Dimension_dependent = sig

  val opened : open_: bool
             -> string
             -> string

  type index_representation
  type index_expression

  val init_ir : index_representation

  val ie_of_ir : index_representation -> index_expression

  val ie_to_elist : index_expression -> Parsetree.expression list

  val offset : index_expression -> index_offset -> index_expression

  val first : L.t
            -> index_expression

  val dim : open_:bool
          -> variable:string
          -> index_expression

  val make_for_loop : index_representation
                    -> open_:bool
                    -> skip_first:bool
                    -> upto:bool
                    -> L.t
                    -> string
                    -> Parsetree.expression                           (* body *)
                    -> Parsetree.expression

end (* Dimension_dependent *)

module A1d : Dimension_dependent = struct

  let loc = !Ast_helper.default_loc

  let opened ~open_ s =
    if open_ then s else "Array1." ^ s

  type index_representation = string
  type index_expression = Parsetree.expression

  (* TODO:
   * Generalize the variable naming mechanism, such that if a user passes an
   * initialial value or a function as 'i',  this will still compile.
   *)
  let init_ir = "i"
  let ie_of_ir i1 = e i1
  let ie_to_elist ie = [ie]

  let offset ie = function
    | Aligned -> ie
    | SubOne  -> [%expr [%e ie] - 1]
    | AddOne  -> [%expr [%e ie] + 1]

  let first = L.start

  let second layout =
    [%expr [%e (first layout)] + 1]

  let dim ~open_ ~variable =
    let edim = e (opened ~open_ "dim") in
    Exp.apply edim (unlabeled [e variable])

  let last ~open_ ~variable layout =
    let d = dim ~open_ ~variable in
    if L.minus_one layout then
      [%expr [%e d] - 1]
    else
      d

  let penultimate ~open_ ~variable layout =
    [%expr [%e (last ~open_ ~variable layout)] - 1]

  let make_for_loop index ~open_ ~skip_first ~upto layout arr body =
    let iv = Pat.var (to_str index) in
    let first = first layout in
    let last  = last ~open_ ~variable:arr layout in
    if skip_first
    then begin
      let sec = second layout in
      let pen = penultimate ~open_ ~variable:arr layout in
      if upto
      then [%expr for [%p iv] = [%e sec] to [%e last] do [%e body] done]
      else [%expr for [%p iv] = [%e pen] downto [%e first] do [%e body] done]
    end else begin
      if upto
      then [%expr for [%p iv] = [%e first] to [%e last] do [%e body] done]
      else [%expr for [%p iv] = [%e last] downto [%e first] do [%e body] done]
    end

end (* A1d *)

module A2d : Dimension_dependent = struct

  let loc = !Ast_helper.default_loc

  let opened ~open_ s =
    if open_ then s else "Array2." ^ s

  type index_representation = string * string
  type index_expression = Parsetree.expression * Parsetree.expression

  let init_ir = "i", "j"
  let ie_of_ir (i1, i2) = e i1, e i2
  let ie_to_elist (ie1, ie2) = [ie1; ie2]

  let offset (ie1, ie2) = function
    | Aligned -> ie1, ie2
    | SubOne  -> [%expr [%e ie1] - 1]
               , [%expr [%e ie2] - 1]
    | AddOne  -> [%expr [%e ie1] + 1]
               , [%expr [%e ie2] + 1]


  let first layout =
    L.start layout, L.start layout

  let second layout =
    let s = L.start layout in
    match layout with
    | L.F -> [%expr [%e s] + 1], s
    | L.C -> s, [%expr [%e s] + 1]

  let dim ~open_ ~variable =
    let edim1 = e (opened ~open_ "dim1") in
    let e1 = Exp.apply edim1 (unlabeled [e variable]) in
    let edim2 = e (opened ~open_ "dim2") in
    let e2 = Exp.apply edim2 (unlabeled [e variable]) in
    e1, e2

  let last ~open_ ~variable layout =
    let d1, d2 = dim ~open_ ~variable in
    if L.minus_one layout then
      [%expr [%e d1] - 1], [%expr [%e d2] - 1]
    else
      d1, d2

  let penultimate ~open_ ~variable layout =
    let d1, d2 = last ~open_ ~variable layout in
    match layout with
    | L.F -> [%expr [%e d1] - 1], d2
    | L.C -> d1, [%expr [%e d2] - 1]

  let make_for_loop (i1, i2) ~open_ ~skip_first ~upto layout arr body =
    let iv1 = Pat.var (to_str i1) in
    let iv2 = Pat.var (to_str i2) in
    let f1, f2 = first layout in
    let l1, l2 = last ~open_ ~variable:arr layout in
    let s1, s2 = second layout in
    let p1, p2 = penultimate ~open_ ~variable:arr layout in
    if skip_first
    then begin
      match upto, layout with
      | true, L.F ->
          Exp.let_ Nonrecursive [ Vb.mk iv2 f2] (Exp.sequence
            (efor iv1 s1 true l1 body)
            (efor iv2 s2 true l2 (efor iv1 f1 true l1 body)))
      | true, L.C ->
          Exp.let_ Nonrecursive [ Vb.mk iv1 f1] (Exp.sequence
            (efor iv2 s2 true l2 body)
            (efor iv1 s1 true l1 (efor iv2 f2 true l2 body)))
      | false, L.F ->
          Exp.let_ Nonrecursive [ Vb.mk iv2 l2] (Exp.sequence
            (efor iv1 f1 false p1 body)
            (efor iv2 f2 false p2 (efor iv1 f1 false l1 body)))
      | false, L.C ->
          Exp.let_ Nonrecursive [ Vb.mk iv1 l1] (Exp.sequence
            (efor iv2 f2 false p2 body)
            (efor iv1 f1 false p1 (efor iv2 f2 false l2 body)))
    end else begin
      match layout with
      | L.F -> efor iv2 f2 upto l2 (efor iv1 f1 upto l1 body)
      | L.C -> efor iv1 f1 upto l1 (efor iv2 f2 upto l2 body)
    end

end (* A2d *)

module A3d : Dimension_dependent = struct

  let loc = !Ast_helper.default_loc

  let opened ~open_ s =
    if open_ then s else "Array3." ^ s

  type index_representation = string * string * string
  type index_expression =
    Parsetree.expression * Parsetree.expression * Parsetree.expression

  let init_ir = "i", "j", "k"
  let ie_of_ir (i1, i2, i3) = e i1, e i2, e i3
  let ie_to_elist (ie1, ie2, ie3) = [ie1; ie2; ie3]

  let offset (ie1, ie2, ie3) = function
    | Aligned -> ie1, ie2, ie3
    | SubOne  -> [%expr [%e ie1] - 1], [%expr [%e ie2] - 1], [%expr [%e ie3] - 1]
    | AddOne  -> [%expr [%e ie1] + 1], [%expr [%e ie2] + 1], [%expr [%e ie3] + 1]

  let first layout =
    L.start layout, L.start layout, L.start layout

  let second layout =
    let s = L.start layout in
    match layout with
    | L.F -> [%expr [%e s] + 1], s, s
    | L.C -> s, s, [%expr [%e s] + 1]

  let dim ~open_ ~variable =
    let edim1 = e (opened ~open_ "dim1") in
    let e1 = Exp.apply edim1 (unlabeled [e variable]) in
    let edim2 = e (opened ~open_ "dim2") in
    let e2 = Exp.apply edim2 (unlabeled [e variable]) in
    let edim3 = e (opened ~open_ "dim3") in
    let e3 = Exp.apply edim3 (unlabeled [e variable]) in
    e1, e2, e3

  let last ~open_ ~variable layout =
    let d1, d2, d3 = dim ~open_ ~variable in
    if L.minus_one layout then
      [%expr [%e d1] - 1], [%expr [%e d2] - 1], [%expr [%e d3] - 1]
    else
      d1, d2, d3

  let penultimate ~open_ ~variable layout =
    let d1, d2, d3 = last ~open_ ~variable layout in
    match layout with
    | L.F -> [%expr [%e d1] - 1], d2, d3
    | L.C -> d1, d2, [%expr [%e d3] - 1]

  let make_for_loop (i1, i2, i3) ~open_ ~skip_first ~upto layout arr body =
    let iv1 = Pat.var (to_str i1) in
    let iv2 = Pat.var (to_str i2) in
    let iv3 = Pat.var (to_str i3) in
    let f1, f2, f3 = first layout in
    let l1, l2, l3 = last ~open_ ~variable:arr layout in
    if skip_first
    then begin
      let s1, s2, s3 = second layout in
      let p1, p2, p3 = penultimate ~open_ ~variable:arr layout in
      match upto, layout with
      | true, L.F ->
          Exp.let_ Nonrecursive [ Vb.mk iv3 f3] (Exp.sequence
            (efor iv2 s2 true l2 (efor iv1 s1 true l1 body))
            (efor iv3 s3 true l3 (efor iv2 f2 true l2 (efor iv1 f1 true l1 body))))
      | true, L.C ->
          Exp.let_ Nonrecursive [ Vb.mk iv1 f1] (Exp.sequence
            (efor iv2 s2 true l2 (efor iv3 s3 true l3 body))
            (efor iv1 s1 true l1 (efor iv2 f2 true l2 (efor iv3 s3 true l3 body))))
      | false, L.F ->
          Exp.let_ Nonrecursive [ Vb.mk iv3 l3] (Exp.sequence
            (efor iv2 f2 false p2 (efor iv1 f1 false p1 body))
            (efor iv3 f3 false p3 (efor iv2 f2 false p2 (efor iv1 f1 false p1 body))))
      | false, L.C ->
          Exp.let_ Nonrecursive [ Vb.mk iv1 l1] (Exp.sequence
              (efor iv2 f2 false p2 (efor iv3 f3 false p3 body))
              (efor iv1 f1 false p1 (efor iv2 f2 false p2 (efor iv3 f3 false p3 body))))
    end else begin
      match layout with
      | L.F -> efor iv3 f3 upto l3 (efor iv2 f2 upto l2 (efor iv1 f1 upto l1 body))
      | L.C -> efor iv1 f1 upto l1 (efor iv2 f2 upto l2 (efor iv3 f3 upto l3 body))
    end

end (* A3d *)

module Make (D : Dimension_dependent) = struct

  let create ~open_ ~variable ~kind ~layout ~size exp =
    Exp.let_ Nonrecursive
      [ Vb.mk (Pat.var (to_str variable))
          (Exp.apply (e (D.opened ~open_ "create"))
            (unlabeled (kind :: layout :: size)))]
      exp

  let get ~open_ arr ~index =
    Exp.apply (e (D.opened ~open_ "unsafe_get"))
      (unlabeled (e arr :: D.ie_to_elist index))

  let set ~open_ arr ~index new_value_ex =
    Exp.apply (e (D.opened ~open_ "unsafe_set"))
      (unlabeled (e arr :: (D.ie_to_elist index) @ [new_value_ex]))

  module Single = struct

    module Body = struct                             (* Ie. Function body terms *)

      open Common_config

      let fold_apply_f { open_; with_index; lambda } ~upto ~ref_ ~index arr =
        let arg_list =
          if with_index then
            if upto then
              (lookup_ref ref_) :: (D.ie_to_elist index) @ [get ~open_ arr ~index]
            else
              (D.ie_to_elist index) @ [get ~open_ arr ~index] @ [lookup_ref ref_]
          else
            if upto then
              (lookup_ref ref_) :: [get ~open_ arr ~index]
            else
              (get ~open_ arr ~index) :: [lookup_ref ref_]
        in
        apply lambda arg_list

      let fold ?(arr_arg="a") ?(ref_="r") c ~upto layout init =
        let index    = D.init_ir in
        let index_ie = D.ie_of_ir index in
        let open_    = c.open_ in
        make_ref ref_ init
          (Exp.sequence
            (D.make_for_loop index ~open_ ~skip_first:false ~upto layout arr_arg
              (assign_ref ref_ (fold_apply_f c ~upto ~ref_ ~index:index_ie arr_arg)))
            (lookup_ref ref_))

      let reduce ?(arr_arg="a") ?(ref_="r") c ~upto layout =
        let index    = D.init_ir  in
        let index_ie = D.ie_of_ir index in
        let open_    = c.open_ in
        make_ref ref_ (get ~open_ arr_arg ~index:(D.first layout))
          (Exp.sequence
             (D.make_for_loop index ~open_ ~skip_first:true ~upto layout arr_arg
              (assign_ref ref_ (fold_apply_f c ~upto ~ref_ ~index:index_ie arr_arg)))
            (lookup_ref ref_))

      let iter_apply_f { open_; with_index; lambda } ~modify arr_arg index =
        if modify then
          let new_value_exp =
            if with_index then
              apply lambda ((D.ie_to_elist index) @ [get ~open_ arr_arg ~index])
            else
              apply lambda [get ~open_ arr_arg ~index]
            in
            set ~open_ arr_arg ~index new_value_exp
        else
          let_unit
            (if with_index then
              apply lambda ((D.ie_to_elist index) @ [get ~open_ arr_arg ~index])
            else
              apply lambda [get ~open_ arr_arg ~index])

      let iter ?(arr_arg="a") c ~modify layout =
        let index    = D.init_ir  in
        let index_ie = D.ie_of_ir index in
        let open_    = c.open_ in
        let inside_ex = iter_apply_f c ~modify arr_arg index_ie in
        D.make_for_loop index ~open_ ~skip_first:false ~upto:true
          layout arr_arg inside_ex

    end (* Body *)

    module Operation = struct

      type 'a t =
        (* 'acc -> 'a -> 'acc *)
        | Fold of { config  : 'a Common_config.t
                  ; left    : bool                    (* fold_ left or right? *)
                  ; init    : 'a                (*Parsetree.expression option *)
                  }

        | Reduce of { config  : 'a Common_config.t
                    ; left    : bool                 (* reduce left or right? *)
                    }

        (* 'a -> unit *)
        | Iter of { config  : 'a Common_config.t
                  ; modify  : bool
                  (* Assign the value back to position. *)
                  }

      let fr_to_name f_o_r with_index left =
        sprintf "%s%s_%s"
          f_o_r
          (if with_index then "i" else "")
          (if left then "left" else "right")

      let addi name = function
        | true  -> name ^ "i"
        | false -> name

      let to_name = function
        | Iter { modify = false; config } -> addi "iter" config.with_index
        | Iter { modify = true;  config } -> addi "modify" config.with_index
        | Fold { config; left }           -> fr_to_name "fold" config.with_index left
        | Reduce { config; left }         -> fr_to_name "reduce" config.with_index left

      let to_body layout = function
        | Iter { config; modify }    -> Body.iter config ~modify layout
        | Fold { config; left; init} -> Body.fold config ~upto:left layout init
        | Reduce { config; left }    -> Body.reduce config ~upto:left layout

      let open_ = function
        | Iter { config } | Fold { config } | Reduce { config }-> config.open_

    end (* Operation *)

    (* Create a fast iter/fold using a reference and for-loop. *)
    module Create = struct

      let make_let ?layout ?(arg="a") ?(layout_arg="l") ~open_ kind let_name
          expression application_expression =
        let to_body array_layout =
          let t = D.opened "t" ~open_ in
          Exp.fun_ Nolabel None (constrain_vec t kind array_layout arg)
            expression
        in
        let body =
          match layout with
          | None    -> Exp.newtype layout_arg (to_body layout_arg)
          | Some ls -> to_body ls
        in
        Exp.let_ Nonrecursive [ Vb.mk (Pat.var (to_str let_name)) body]
          application_expression

      let layout_specific_without_app kind op layout app =
        let name = Operation.to_name op ^ L.to_name_suffix layout in
        let open_ = Operation.open_ op in
        let body = Operation.to_body layout op in
        make_let ~layout:(L.constraint_name layout) ~open_ kind name
          body (app name)

      let layout_specific kind op arr layout =
        layout_specific_without_app kind op layout
          (fun name -> Exp.apply (e name) (unlabeled [arr]))

      let layout_agnostic kind op arr =
        let name = Operation.to_name op in
        let open_ = Operation.open_ op in
        (* This variable renaming isn't necessary, it just makes the code, as output
        * -dsource, eaiser to read. *)
        let arg = "b" in
        let arg_ex = [Nolabel, e arg] in
        make_let ~arg ~open_ kind name
          (layout_specific_without_app kind op (L.F)
            (fun name_f ->
              layout_specific_without_app kind op (L.C)
                (fun name_c ->
                  Exp.match_ (Exp.apply (e (D.opened ~open_ "layout")) arg_ex)
                    [ Exp.case (Pat.construct (lid "Fortran_layout") None)
                        (Exp.apply (e name_f) arg_ex)
                    ; Exp.case (Pat.construct (lid "C_layout") None)
                        (Exp.apply (e name_c) arg_ex)])))
          (Exp.apply (e name) [ Nolabel, arr])

    end (* Create *)

    module Parse = struct

      let to_fs = function | true -> "fold_left" | false -> "fold_right"

      let fold_args_unlabled loc c left lst =
        let n = List.length lst in
        if n < 3 then
          location_error ~loc "Missing %s arguments." (to_fs left)
        else if n > 3 then
          location_error ~loc "Too many arguments to %s." (to_fs left)
        else
          match lst with
          | [ Nolabel, lambda; Nolabel, init; Nolabel, v ] ->
              let config = Cc.overwrite_lambda c lambda in
              Operation.Fold { config; left; init = init }, v
          | _ ->
            location_error ~loc "Missing labeled f argument to %s." (to_fs left)

      let fold loc c left lst =
        match remove_and_assoc (Labelled "f") lst with
        | lambda, lst ->
            begin match remove_and_assoc (Labelled "init") lst with
            | init, lst ->
                begin match remove_and_assoc Nolabel lst with
                | v, [] -> let config = Cc.overwrite_lambda c lambda in
                          Operation.Fold { config ; left; init = init}, v
                | v, ls -> location_error ~loc "Extra arguments to %s."
                            (to_fs left)
                | exception Not_found ->
                    location_error ~loc "Missing unlabeled array1 argument to %s."
                      (to_fs left)
                end
            | exception Not_found ->
                location_error ~loc "Missing labeled init argument to %s." (to_fs left)
            end
        | exception Not_found ->
            fold_args_unlabled loc c left lst

      let initless loc lst funs k =
        match remove_and_assoc (Labelled "f") lst with
        | f, lst ->
            begin match remove_and_assoc Nolabel lst with
            | v, [] -> k f v
            | v, ls -> location_error ~loc "Extra arguments to %s." funs
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

      let iter loc c modify lst =
        initless loc lst "iter"
          (fun lambda v ->
            let config = Cc.overwrite_lambda c lambda in
            Operation.Iter { config; modify }, v)

      let reduce loc c left lst =
        initless loc lst "reduce"
          (fun lambda v ->
            let config = Cc.overwrite_lambda c lambda in
            Operation.Reduce { config; left }, v)

      let op_and_payload ~loc ~open_ = function
        | [ { pstr_desc =
              Pstr_eval
                ( { pexp_desc =
                    Pexp_apply ({pexp_desc =
                      Pexp_ident {txt = Longident.Lident f}}, args)}, _)}] ->
            begin match f with
            | "fold_left"     ->
                Ok (fold loc (Cc.init ~open_ ~with_index:false) true args)
            | "fold_right"    ->
                Ok (fold loc (Cc.init ~open_ ~with_index:false) false args)
            | "foldi_left"    ->
                Ok (fold loc (Cc.init ~open_ ~with_index:true) true args)
            | "foldi_right"   ->
                Ok (fold loc (Cc.init ~open_ ~with_index:true) false args)
            | "reduce_left"   ->
                Ok (reduce loc (Cc.init ~open_ ~with_index:false) true args)
            | "reduce_right"  ->
                Ok (reduce loc (Cc.init ~open_ ~with_index:false) false args)
            | "reducei_left"  ->
                Ok (reduce loc (Cc.init ~open_ ~with_index:true) true args)
            | "reducei_right" ->
                Ok (reduce loc (Cc.init ~open_ ~with_index:true) false args)
            | "iter"          ->
                Ok (iter loc (Cc.init ~open_ ~with_index:false) false args)
            | "iteri"         ->
                Ok (iter loc (Cc.init ~open_ ~with_index:true) false args)
            | "modify"        ->
                Ok (iter loc (Cc.init ~open_ ~with_index:false) true args)
            | "modifyi"       ->
                Ok (iter loc (Cc.init ~open_ ~with_index:true) true args)
            | s               ->
                Error s
            end
        | [] -> location_error ~loc "Missing fold, reduce, iter or modify invocation."
        | _  -> location_error ~loc "Incorrect fold, reduce, iter or modify invocation."

    end (* Parse *)

    let maybe ~open_ ~loc r p =
      match Parse.op_and_payload ~open_ ~loc p with
      | Error s         -> Error s
      | Ok (op, arr1) ->
          let rec has_kind = function
            | []        -> location_error ~loc "Missing kind string"
            | kstr :: t -> let kind = Common_parse.kind ~loc kstr in
                          is_layout kind t
          and is_layout kind = function
            | []             -> execute_op kind op arr1 None
            | lstr :: []     -> let layout = Common_parse.layout ~loc lstr in
                                execute_op kind op arr1 (Some layout)
            | lstr :: l :: _ -> location_error ~loc "Errant string %S after layout." l
          and execute_op ?layout kind op arr1 = function
            | None   -> Create.layout_agnostic kind op arr1
            | Some l -> Create.layout_specific kind op arr1 l
          in
          Ok (has_kind r)   (* Fail via exceptions. *)

  end (* Single *)

  module Double = struct

    (* Unlike the single case we won't support reduce2,
    * do we reduce to the first or second type? *)

    module Body = struct

      open Common_config

      let fold_apply_f { open_; with_index; lambda } ~upto ~ref_ ~index
          arr1 arr2 io =
        let arg_list =
          if with_index then
            if upto then
                ( lookup_ref ref_ )
                :: ( D.ie_to_elist index )
                @ [ get ~open_ arr1 ~index
                  ; get ~open_ arr2 ~index:(D.offset index io)
                  ]
            else
                ( D.ie_to_elist index )
                @ [ get ~open_ arr1 ~index
                  ; get ~open_ arr2 ~index:(D.offset index io)
                  ; lookup_ref ref_
                  ]
          else
            if upto then
              [ lookup_ref ref_
              ; get ~open_ arr1 ~index
              ; get ~open_ arr2 ~index:(D.offset index io)
              ]
            else
              [ get ~open_ arr1 ~index
              ; get ~open_ arr2 ~index:(D.offset index io)
              ; lookup_ref ref_
              ]
        in
        apply lambda arg_list

      let fold ?(arr_arg1="a") ?(arr_arg2="b") ?(ref_="r")
        c ~upto layout init ~index_offset =
        let index    = D.init_ir in
        let index_ie = D.ie_of_ir index in
        let open_    = c.open_ in
        let inside_ex =
          assign_ref ref_
            (fold_apply_f c ~upto ~ref_ ~index:index_ie
              arr_arg1 arr_arg2 index_offset)
        in
        make_ref ref_ init
          (Exp.sequence
            (D.make_for_loop index ~open_ ~skip_first:false ~upto layout
            (* We're passing ONLY the first array into the for-loop construction
             * part, so we'll use it for the sizes, offsets against that index
             * are determined via index_offset above. But more importantly,
             * we're NOT checking that the 2 arrays are the same size here. *)
               arr_arg1 inside_ex)
            (lookup_ref ref_))

      let iter_apply_f { open_; with_index; lambda } arr1 arr2 index io =
        let gets =
          [ get ~open_ arr1 ~index
          ; get ~open_ arr2 ~index:(D.offset index io)
          ]
        in
        let arg_list =
          if with_index then (D.ie_to_elist index) @ gets else gets
        in
        let_unit (apply lambda arg_list)

      let iter ?(arr_arg1="a") ?(arr_arg2="b") c layout ~index_offset =
        let index    = D.init_ir in
        let index_ie = D.ie_of_ir index in
        let open_    = c.open_ in
        let inside_ex = iter_apply_f c arr_arg1 arr_arg2 index_ie index_offset in
        D.make_for_loop index ~open_ ~skip_first:false ~upto:true layout
          arr_arg1 inside_ex

      let map ?(arr_arg1="a") ?(arr_arg2="b") ?layout2  (* Target layout *)
        { open_; with_index; lambda } layout target_kind =
        let index    = D.init_ir in
        let index_ie = D.ie_of_ir index in
        let inside_ex, tlayout_ex =
          let index2_ie, tlayout_ex =
            match layout2 with
            | None               ->
                index_ie
                , Exp.apply (e (D.opened ~open_ "layout"))
                    (unlabeled [e arr_arg1])
            | Some target_layout ->
                D.offset index_ie (L.to_index_offsets layout target_layout)
                , e (L.constraint_name target_layout)
          in
          let arg_list =
            if with_index then
              (D.ie_to_elist index_ie)
              @ [ get ~open_ arr_arg1 ~index:index_ie ]
            else
              [ get ~open_ arr_arg1 ~index:index_ie ]
          in
          set ~open_ arr_arg2 ~index:index2_ie (apply lambda arg_list)
          , tlayout_ex
        in
        let tkind_ex = e (K.to_string target_kind) in
        let size     = D.(dim ~open_ ~variable:arr_arg1 |> ie_to_elist) in
        create ~open_ ~variable:arr_arg2 ~kind:tkind_ex ~layout:tlayout_ex ~size
          (Exp.sequence
            (D.make_for_loop index ~open_ ~skip_first:false ~upto:true
               layout arr_arg1 inside_ex)
            (e arr_arg2))

    end (* Body *)

    module Operation = struct

      (* Unlike the single case we'll wrap the Array1's that we're operating
      * on inside the operation since there is a difference between 1 or 2
      * actual arrays that we apply to. *)
      type 'a t =
        (* 'acc -> 'a -> 'acc *)
        | Fold of { config  : 'a Common_config.t
                  ; left    : bool                      (* fold_ left or right? *)
                  ; init    : 'a
                  ; arr1    : 'a
                  ; arr2    : 'a
                  }
        (* 'a -> unit *)
        | Iter of { config  : 'a Common_config.t
                  ; arr1    : 'a
                  ; arr2    : 'a
                  }
        (* 'a -> kind *)
        | Map of { config   : 'a Common_config.t
                 ; arr      : 'a
                 }

      let fold_to_name with_index left =
        sprintf "fold%s_%s2"
          (if with_index then "i" else "")
          (if left then "left" else "right")

      let add_i n c =
        if c.Cc.with_index then n ^ "i" else n

      let to_name = function
        | Iter { config }             -> (add_i "iter" config) ^ "2"
        | Map { config }              -> add_i "map" config
        | Fold { config; init; left } -> fold_to_name config.with_index left

      let open_ = function
        | Iter { config } | Map { config } | Fold { config } -> config.Cc.open_

    end (* Operation *)

    module Create = struct

      (* So similar to the one in Single but we need the extra constraint. *)
      let make_let_single ?layout ?(arg="a") ?(layout_arg="l") ~open_ kind
          ?constraint_kind
          let_name expression application_expression =
        let t = D.opened "t" ~open_ in
        let to_args array_layout =
          match constraint_kind with
          | None ->
              Exp.fun_ Nolabel None (constrain_vec t kind array_layout arg)
                expression
          | Some k ->
              let t1, t2 = K.to_constraint_types k in
              let econstr s = Typ.constr (lid s) [] in
              let ct = Typ.constr (lid t)
                  [ econstr t1; econstr t2; econstr array_layout]
              in
              Exp.fun_ Nolabel None (constrain_vec t kind array_layout arg)
                (Exp.constraint_ expression ct)
        in
        let args =
          match layout with
          | None    -> Exp.newtype layout_arg (to_args layout_arg)
          | Some ls -> to_args ls
        in
        let vb_pat = Pat.var (to_str let_name) in
        Exp.let_ Nonrecursive [ Vb.mk vb_pat args] application_expression

      let make_let_double ?layout
          ?(arg1="a") ?(arg2="b")
          ?(layout_arg1="l1") ?(layout_arg2="l2")
          ~open_
          kind1 kind2
          let_name expression application_expression =
        let t = D.opened "t" ~open_ in
        (* TODO: Check arg1 <> arg2 && layout_arg1 <> layout_arg2 *)
        let to_body array1_layout array2_layout =
          let c1 = constrain_vec t kind1 array1_layout arg1 in
          let c2 = constrain_vec t kind2 array2_layout arg2 in
          Exp.fun_ Nolabel None c1
            (Exp.fun_ Nolabel None c2 expression)
        in
        let body =
          match layout with
          | None          -> Exp.newtype layout_arg1
                              (Exp.newtype layout_arg2
                                (to_body layout_arg1 layout_arg2))
          | Some (l1, l2) -> to_body l1 l2
        in
        Exp.let_ Nonrecursive [ Vb.mk (Pat.var (to_str let_name)) body]
          application_expression

      let layout_specific_without_app_map config name_prefix
        kind1 kind2 layout1 layout2 app =
        let name =
          name_prefix
          ^ L.to_name_suffix layout1
          ^ L.to_name_suffix layout2
        in
        make_let_single ~layout:(L.constraint_name layout1)
          ~open_:config.Cc.open_ kind1 name
          (Body.map config layout1 kind2 ~layout2)
          (app name)

      let layout_specific_without_app_single ~open_ name_prefix
          kind1 kind2 layout1 layout2
          to_body app =
        let index_offset = L.to_index_offsets layout1 layout2 in
        let name =
          name_prefix
          ^ L.to_name_suffix layout1
          ^ L.to_name_suffix layout2
        in
        let layout = L.constraint_name layout1, L.constraint_name layout2 in
        make_let_double ~layout ~open_ kind1 kind2 name
          (to_body ~index_offset)
          (app name)

      let layout_specific op kind1 kind2 layout1 layout2 =
        match op with
        | Operation.Map { config; arr } ->
            layout_specific_without_app_map config "map"
              kind1 kind2 layout1 layout2
              (fun name -> Exp.apply (e name) (unlabeled [arr]))
        | Operation.Iter { config; arr1; arr2 } ->
            layout_specific_without_app_single ~open_:config.open_ "iter"
              kind1 kind2 layout1 layout2
              (Body.iter config layout1)
              (fun name -> Exp.apply (e name) (unlabeled [arr1; arr2]))
        | Operation.Fold { config; left; init; arr1; arr2 } ->
            layout_specific_without_app_single ~open_:config.open_
              (Operation.fold_to_name config.with_index left)
              kind1 kind2 layout1 layout2
              (Body.fold config ~upto:left layout1 init)
              (fun name -> Exp.apply (e name) (unlabeled [arr1; arr2]))

      let layout_agnostic op kind1 kind2 =
        let name = Operation.to_name op in
        let open_ = Operation.open_ op in
        (* Layout agnostic has different meanings for Map vs Iter/Fold.*)
        match op with
        | Operation.Map { config ; arr} ->
          let lswm = layout_specific_without_app_map config "map" in
          (* We don't know the target arrays layout, so use the same as the
          * source array. *)
          let arg = "b" in
          let arg_ex = [Nolabel, e arg] in
          make_let_single ~arg ~open_ kind1 name ~constraint_kind:kind2
            (lswm kind1 kind2 (L.F) (L.F)
            (fun name_f_f ->
            (lswm kind1 kind2 (L.C) (L.C)
            (fun name_c_c ->
            Exp.match_ (Exp.apply (e (D.opened ~open_ "layout")) arg_ex)
                [ Exp.case (Pat.construct (lid "Fortran_layout") None)
                    (Exp.apply (e name_f_f) arg_ex)
                ; Exp.case (Pat.construct (lid "C_layout") None)
                    (Exp.apply (e name_c_c) arg_ex)
                ]))))
            (Exp.apply (e name) (unlabeled [arr]))

        | Operation.Iter { config; arr1; arr2 } ->
          let lswa k1 k2 l1 l2 =
            layout_specific_without_app_single ~open_:config.open_ "iter2"
              k1 k2 l1 l2
              (Body.iter config l1)
          in
          let arg1 = "c" in
          let arg2 = "d" in
          let arg1_ex = [Nolabel, e arg1] in
          let arg2_ex = [Nolabel, e arg2] in
          let args_ex = arg1_ex @ arg2_ex in
          make_let_double ~arg1 ~arg2 ~open_ kind1 kind2 name
            (lswa kind1 kind2 L.F L.F
            (fun name_f_f ->
            (lswa kind1 kind2 L.F L.C
            (fun name_f_c ->
            (lswa kind1 kind2 L.C L.F
            (fun name_c_f ->
            (lswa kind1 kind2 L.C L.C
            (fun name_c_c ->
              Exp.match_ (Exp.apply (e (D.opened ~open_ "layout")) arg1_ex)
                [ Exp.case (Pat.construct (lid "Fortran_layout") None)
                    (Exp.match_ (Exp.apply (e (D.opened ~open_ "layout")) arg2_ex)
                        [ Exp.case (Pat.construct (lid "Fortran_layout") None)
                            (Exp.apply (e name_f_f) args_ex)
                        ; Exp.case (Pat.construct (lid "C_layout") None)
                            (Exp.apply (e name_f_c) args_ex)])
                ; Exp.case (Pat.construct (lid "C_layout") None)
                    (Exp.match_ (Exp.apply (e (D.opened ~open_ "layout")) arg2_ex)
                        [ Exp.case (Pat.construct (lid "Fortran_layout") None)
                            (Exp.apply (e name_c_f) args_ex)
                        ; Exp.case (Pat.construct (lid "C_layout") None)
                            (Exp.apply (e name_c_c) args_ex)])
                ]))))))))
            (Exp.apply (e name) (unlabeled [arr1; arr2]))

        | Operation.Fold { config; left; init; arr1; arr2 } ->
          let lswa k1 k2 l1 l2 =
            layout_specific_without_app_single ~open_:config.open_
              (Operation.fold_to_name config.with_index left)
              k1 k2 l1 l2
              (Body.fold config ~upto:left l1 init)
          in
          let arg1 = "c" in
          let arg2 = "d" in
          let arg1_ex = [Nolabel, e arg1] in
          let arg2_ex = [Nolabel, e arg2] in
          let args_ex = arg1_ex @ arg2_ex in
          make_let_double ~arg1 ~arg2 ~open_ kind1 kind2 name
            (lswa kind1 kind2 L.F L.F
            (fun name_f_f ->
            (lswa kind1 kind2 L.F L.C
            (fun name_f_c ->
            (lswa kind1 kind2 L.C L.F
            (fun name_c_f ->
            (lswa kind1 kind2 L.C L.C
            (fun name_c_c ->
              Exp.match_ (Exp.apply (e (D.opened ~open_ "layout")) arg1_ex)
                [ Exp.case (Pat.construct (lid "Fortran_layout") None)
                    (Exp.match_ (Exp.apply (e (D.opened ~open_ "layout")) arg2_ex)
                        [ Exp.case (Pat.construct (lid "Fortran_layout") None)
                            (Exp.apply (e name_f_f) args_ex)
                        ; Exp.case (Pat.construct (lid "C_layout") None)
                            (Exp.apply (e name_f_c) args_ex)])
                ; Exp.case (Pat.construct (lid "C_layout") None)
                    (Exp.match_ (Exp.apply (e (D.opened ~open_ "layout")) arg2_ex)
                        [ Exp.case (Pat.construct (lid "Fortran_layout") None)
                            (Exp.apply (e name_c_f) args_ex)
                        ; Exp.case (Pat.construct (lid "C_layout") None)
                            (Exp.apply (e name_c_c) args_ex)])
                ]))))))))
            (Exp.apply (e name) (unlabeled [arr1; arr2]))

    end (* Create *)

    module Parse = struct

      let to_fs = function
        | true -> "fold_left2"
        | false -> "fold_right2"

      let fold_args_unlabled loc c left lst =
        let n = List.length lst in
        if n < 4 then
          location_error ~loc "Missing %s arguments." (to_fs left)
        else if n > 4 then
          location_error ~loc "Too many arguments to %s." (to_fs left)
        else
          match lst with
          | [ Nolabel, lambda; Nolabel, init; Nolabel, arr1; Nolabel, arr2 ] ->
              let config = Cc.overwrite_lambda c lambda in
              Operation.Fold { config; left; init; arr1; arr2}
          | _ ->
            location_error ~loc "Missing labeled f argument to %s." (to_fs left)

      let fold loc c left lst =
        match remove_and_assoc (Labelled "f") lst with
        | lambda, lst ->
            begin match remove_and_assoc (Labelled "init") lst with
            | init, lst ->
                begin match remove_and_assoc Nolabel lst with
                | arr1, lst ->
                    begin match remove_and_assoc Nolabel lst with
                    | arr2, [] ->
                        let config = Cc.overwrite_lambda c lambda in
                        Operation.Fold { config; left; init; arr1; arr2}
                    | _, ls ->
                        location_error ~loc "Extra arguments to %s." (to_fs left)
                    | exception Not_found ->
                        location_error ~loc "Missing unlabeled array1 argument to %s."
                          (to_fs left)
                    end
                | exception Not_found ->
                      location_error ~loc "Missing unlabeled array1 argument to %s."
                        (to_fs left)
                end
            | exception Not_found ->
                location_error ~loc "Missing labeled init argument to %s." (to_fs left)
            end
        | exception Not_found ->
            fold_args_unlabled loc c left lst

      let iter loc c lst =
        match remove_and_assoc (Labelled "f") lst with
        | lambda, lst ->
            begin match lst with
            | [ Nolabel, arr1; Nolabel, arr2 ] ->
                let config = Cc.overwrite_lambda c lambda in
                Operation.Iter { config; arr1; arr2}
            | _ -> location_error ~loc "Missing unlabeled arguments to iter2."
            end
        | exception Not_found  ->
            let n = List.length lst in
            if n < 3 then
              location_error ~loc "Missing iter2 arguments"
            else if n > 3 then
              location_error ~loc "Too many argument to iter2"
            else
              begin match lst with
              | [ Nolabel, lambda; Nolabel, arr1; Nolabel, arr2 ] ->
                let config = Cc.overwrite_lambda c lambda in
                Operation.Iter { config; arr1; arr2}
              | _ ->
                location_error ~loc "Missing unlabeled \"f\" argument to iter2."
              end

      let map loc c lst =
        match remove_and_assoc (Labelled "f") lst with
        | lambda, lst ->
            begin match lst with
            | [ Nolabel, arr ] ->
                let config = Cc.overwrite_lambda c lambda in
                Operation.Map { config; arr}
            | _ -> location_error ~loc "Missing unlabeled arguments to map."
            end
        | exception Not_found  ->
            let n = List.length lst in
            if n < 2 then
              location_error ~loc "Missing map arguments"
            else if n > 2 then
              location_error ~loc "Too many argument to map" iter
            else
              begin match lst with
              | [ Nolabel, lambda; Nolabel, arr ] ->
                let config = Cc.overwrite_lambda c lambda in
                Operation.Map { config; arr}
              | _ ->
                location_error ~loc "Missing unlabeled \"f\" argument to map."
              end

      let op_and_payload ~loc ~open_ = function
        | [ { pstr_desc =
              Pstr_eval
                ( { pexp_desc =
                    Pexp_apply ({pexp_desc =
                      Pexp_ident {txt = Longident.Lident f}}, args)}, _)}] ->
            begin match f with
            | "fold_left2"    ->
                Ok (fold loc (Cc.init ~open_ ~with_index:false) true args)
            | "fold_right2"   ->
                Ok (fold loc (Cc.init ~open_ ~with_index:false) false args)
            | "foldi_left2"   ->
                Ok (fold loc (Cc.init ~open_ ~with_index:true) true args)
            | "foldi_right2"  ->
                Ok (fold loc (Cc.init ~open_ ~with_index:true) false args)
            | "iter2"         ->
                Ok (iter loc (Cc.init ~open_ ~with_index:false) args)
            | "iteri2"        ->
                Ok (iter loc (Cc.init ~open_ ~with_index:true) args)
            | "map"           ->
                Ok (map loc (Cc.init ~open_ ~with_index:false) args)
            | "mapi"          ->
                Ok (map loc (Cc.init ~open_ ~with_index:true) args)
            | s               ->
                Error s
            end
        | []         -> location_error ~loc "Missing operation."
        |  _         -> location_error ~loc "Incorrect invocation."

    end (* Parse *)

    let maybe ~open_ ~loc r p =
      match Parse.op_and_payload ~open_ ~loc p with
      | Error s -> Error s
      | Ok op   ->
          let rec has_kind = function
            | []        -> location_error ~loc "Missing kind string."
            | kstr :: t -> let kind = Common_parse.kind ~loc kstr in
                          is_layout_or_kind ~kind t
          and is_layout_or_kind ?kind2 ~kind = function
            | []         -> l_agnostic ~kind ?kind2 ()
            | lkstr :: t ->
                begin match Common_parse.kind_or_layout ~loc lkstr with
                | `L layout -> another_layout ?kind2 ~kind ~layout t
                | `K kind2  -> is_layout_or_kind ~kind ~kind2 t
                end
          and another_layout ?kind2 ~kind ~layout = function
            | []         -> l_specific ?kind2 ~kind ~layout ()
            | lstr :: [] -> let layout2 = Common_parse.layout ~loc lstr in
                            l_specific ?kind2 ~kind ~layout ~layout2 ()
            | _ :: s :: _ ->
              location_error ~loc "Extra argument past last layout and kind: %s" s
          and l_agnostic ~kind ?kind2 () =
            begin match kind2 with
            | None  ->                               (* No layout, no 2nd kind. *)
                Create.layout_agnostic op kind kind     (* same kind. *)
            | Some kind2 ->
                Create.layout_agnostic op kind kind2    (* diff kind. *)
            end
          and l_specific ~kind ?kind2 ~layout ?layout2 () =
            begin match kind2 with
            | None  ->                                          (* No 2nd kind. *)
                begin match layout2 with
                | None ->
                    Create.layout_specific op
                          kind kind                               (* same kind. *)
                          layout layout                         (* same layout. *)
                | Some layout2 ->
                    Create.layout_specific op
                          kind kind                               (* same kind. *)
                          layout layout2                  (* maybe diff layout. *)
                end
            | Some kind2 ->
                begin match layout2 with
                | None ->
                    Create.layout_specific op
                      kind kind2                            (* maybe diff kind. *)
                      layout layout                             (* same layout. *)
                | Some layout2 ->
                    Create.layout_specific op
                      kind kind2                            (* maybe diff kind. *)
                      layout layout2                      (* maybe diff layout. *)
                end
            end
          in
          Ok (has_kind r)                               (* Fail via exceptions. *)

  end (* Double *)

  let operation ~open_ ~loc t payload =
    match Single.maybe ~open_ ~loc t payload with
    | Ok expression -> expression
    | Error _fn ->
        begin match Double.maybe ~open_ ~loc t payload with
        | Ok expression -> expression
        | Error fn ->
            location_error ~loc "Unsupported function: %s" fn
        end

end (* Make *)

module A1 = Make(A1d)
module A2 = Make(A2d)
module A3 = Make(A3d)

let transform loc txt payload def =
  try
    match String.split_on_char '.' txt with
    | "array1" :: t -> A1.operation ~open_:false ~loc t payload
    | "open1" :: t  -> A1.operation ~open_:true ~loc t payload
    | "array2" :: t -> A2.operation ~open_:false ~loc t payload
    | "open2" :: t  -> A2.operation ~open_:true ~loc t payload
    | "array3" :: t -> A3.operation ~open_:false ~loc t payload
    | "open3" :: t  -> A3.operation ~open_:true ~loc t payload
    | _             -> def ()
  with Location.Error e ->
    Exp.extension ~loc (extension_of_error e)

let bigarray_fold_mapper =
  { default_mapper with
    expr = fun mapper expr ->
      match expr with
      | { pexp_desc = Pexp_extension ({ txt }, PStr payload)} ->
          transform expr.pexp_loc txt payload
            (fun () -> default_mapper.expr mapper expr)
      | other -> default_mapper.expr mapper other; }

let rewriter _config _cookies =
  bigarray_fold_mapper

(* Registration *)

let () =
  let open Migrate_parsetree in
  Driver.register ~name:"bigarray_fold_ppx" Versions.ocaml_404 rewriter
