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

type index_offsets =
  | Aligned
  | AddOne
  | SubOne

module L = struct

  type t = L : 'a layout -> t

  (* layout name for constraint,
  * starting index,
  * minus one for ending point
  * suffix *)

  type layout_specific_for_options =
    { constraint_name : string
    ; start_index     : int
    ; minus_one       : bool                           (* When calculating end. *)
    }

  let to_fold_params = function
    | L Fortran_layout ->
        { constraint_name = "fortran_layout"
        ; start_index     = 1
        ; minus_one       = false
        }
    | L C_layout       ->
        { constraint_name = "c_layout"
        ; start_index     = 0
        ; minus_one       = true
        }

  let to_pattern_case = function
    | L Fortran_layout -> "Fortran_layout"
    | L C_layout       -> "C_layout"

  let to_name_suffix = function
    | L Fortran_layout -> "_fortran"
    | L C_layout       -> "_c"

  let to_index_offsets layout1 layout2 =
    match layout1, layout2 with
    | L C_layout,       L C_layout       -> Aligned
    | L Fortran_layout, L Fortran_layout -> Aligned
    | L Fortran_layout, L C_layout       -> SubOne
    | L C_layout,       L Fortran_layout -> AddOne

end (* L *)

(* AST construction helpers *)
let to_str s = Location.mkloc s Location.none

let lid s = Location.mkloc (Longident.parse s) Location.none

let ex_id s = Exp.ident (lid s)

let opened ~open_ s =
  if open_ then s else "Array1." ^ s

let constrain_vec ~open_ kind layout_s vec_var =
  let t1, t2 = K.to_constraint_types kind in
  let econstr s = Typ.constr (lid s) [] in
  Pat.constraint_ (Pat.var (to_str vec_var))
    (Typ.constr (lid (opened ~open_ "t"))
       [ econstr t1; econstr t2; econstr layout_s])

let unlabeled lst =
  List.map (fun ex -> Nolabel, ex) lst

let make_ref var init exp =
  Exp.let_ Nonrecursive
    [ Vb.mk (Pat.var (to_str var))
        (Exp.apply (ex_id "ref") (unlabeled [init]))]
    exp

let create_array1 ~open_ var kind layout size exp =
  Exp.let_ Nonrecursive
    [ Vb.mk (Pat.var (to_str var))
        (Exp.apply (ex_id (opened ~open_ "create"))
           (unlabeled [kind; layout; size]))]
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

let apply f args =
  Exp.apply f (unlabeled args)

let make_for_loop index ~start_exp ~end_exp upto body_exp =
  if upto
  then Exp.for_ (Pat.var (to_str index)) start_exp end_exp Upto body_exp
  else Exp.for_ (Pat.var (to_str index)) end_exp start_exp Downto body_exp

let const_int n = Pconst_integer (string_of_int n, None)

let plus_one exp =
  Exp.apply (ex_id "+")
    (unlabeled [ exp ; Exp.constant (const_int 1) ])

let minus_one exp =
  Exp.apply (ex_id "-")
    (unlabeled [ exp ; Exp.constant (const_int 1) ])

let index_offset_to_offset_index index = function
  | Aligned -> index
  | SubOne  -> minus_one index
  | AddOne  -> plus_one index

let mo_expr ~mo exp = if mo then minus_one exp else exp

let dim_expr ~open_ arr =
  let edim = ex_id (opened ~open_ "dim") in
  Exp.apply edim (unlabeled [ex_id arr])

let length_expr ~open_ ~mo arr =
  mo_expr ~mo (dim_expr ~open_ arr)

let let_unit exp =
  let unit_l = lid "()" in
  Exp.let_ Nonrecursive [ Vb.mk (Pat.construct unit_l None) exp]
    (Exp.construct unit_l None)

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
    | "fortran"  -> L.(L Fortran_layout)
    | "c"        -> L.(L C_layout)
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

module Single = struct

  module Body = struct                             (* Ie. Function body terms *)

    open Common_config

    let fold_apply_f { open_; with_index; lambda } ~upto ~ref_ ~index arr =
      let index_ex = ex_id index in
      let arg_list =
        if with_index then
          if upto then
            [ lookup_ref ref_; index_ex; get ~open_ arr index_ex]
          else
            [ index_ex; get ~open_ arr index_ex; lookup_ref ref_]
        else
          if upto then
            [ lookup_ref ref_; get ~open_ arr index_ex]
          else
            [ get ~open_ arr index_ex; lookup_ref ref_]
      in
      apply lambda arg_list

    (* TODO:
    * Generalize the variable naming mechanism, such that if a user passes an
    * initialial value as 'r' or an function as 'i' (for example), this will
    * still compile.
    * *)
    let fold_body ?(arr_arg="a") ?(ref_="r") ?(index="i") c
        ~upto ~start ~mo init =
      let start_exp = Exp.constant (const_int start) in
      let end_exp = length_expr ~open_:c.open_ ~mo arr_arg in
      make_ref ref_ init
        (Exp.sequence
          (make_for_loop index ~start_exp ~end_exp upto
            (assign_ref ref_
              (fold_apply_f c ~upto ~ref_ ~index arr_arg)))
          (lookup_ref ref_))

    let reduce_body ?(arr_arg="a") ?(ref_="r") ?(index="i") c
        ~upto ~start ~mo =
      let first_index, start_exp, end_exp, dir =
        let li = length_expr ~open_:c.open_ ~mo arr_arg in
        let fi = Exp.constant (const_int start) in
        if upto then
          fi
          , Exp.constant (const_int (start + 1))
          , li
          , Upto
        else
          li
          , (mo_expr ~mo:true li)
          , fi
          , Downto
      in
      make_ref ref_ (get ~open_:c.open_ arr_arg first_index)
        (Exp.sequence
          (Exp.for_ (Pat.var (to_str index)) start_exp end_exp dir
            (assign_ref ref_
              (fold_apply_f c ~upto ~ref_ ~index arr_arg)))
          (lookup_ref ref_))

    let iter ?(arr_arg="a") ?(index="i")
      { open_; with_index; lambda } ~upto ~modify ~start ~mo =
      let index_ex = ex_id index in
      let inside_ex =
        if modify then
          let new_value_exp =
            if with_index then
              apply lambda [index_ex; get ~open_ arr_arg index_ex]
            else
              apply lambda [get ~open_ arr_arg index_ex]
          in
          set ~open_ arr_arg index_ex new_value_exp
        else
          let_unit
            (if with_index then
              apply lambda [index_ex; get ~open_ arr_arg index_ex]
            else
              apply lambda [get ~open_ arr_arg index_ex])
      in
      make_for_loop index
        ~start_exp:(Exp.constant (const_int start))
        ~end_exp:(length_expr ~open_ ~mo arr_arg)
        upto
        inside_ex

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

    let to_body = function
      | Iter { config; modify }    -> Body.iter config ~upto:true ~modify
      | Fold { config; left; init} -> Body.fold_body config ~upto:left init
      | Reduce { config; left }    -> Body.reduce_body config ~upto:left

    let open_ = function
      | Iter { config } | Fold { config } | Reduce { config }-> config.open_

  end (* Operation *)

  (* Create a fast iter/fold using a reference and for-loop. *)
  module Create = struct

    let make_let ?layout ?(arg="a") ?(layout_arg="l") ~open_ kind let_name
        expression application_expression =
      let to_body array_layout =
        Exp.fun_ Nolabel None (constrain_vec ~open_ kind array_layout arg)
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
      let lsfo = L.to_fold_params layout in
      let name = Operation.to_name op ^ L.to_name_suffix layout in
      let open_ = Operation.open_ op in
      let body = Operation.to_body op in
      make_let ~layout:lsfo.constraint_name ~open_ kind name
        (body ~start:lsfo.start_index ~mo:lsfo.minus_one)
        (app name)

    let layout_specific kind op arr layout =
      layout_specific_without_app kind op layout
        (fun name -> Exp.apply (ex_id name) (unlabeled [arr]))

    let layout_agnostic kind op arr =
      let name = Operation.to_name op in
      let open_ = Operation.open_ op in
      (* This variable renaming isn't necessary, it just makes the code, as output
      * -dsource, eaiser to read. *)
      let arg = "b" in
      let arg_ex = [Nolabel, ex_id arg] in
      make_let ~arg ~open_ kind name
        (layout_specific_without_app kind op (L Fortran_layout)
          (fun name_f ->
            layout_specific_without_app kind op (L C_layout)
              (fun name_c ->
                 Exp.match_ (Exp.apply (ex_id (opened ~open_ "layout")) arg_ex)
                  [ Exp.case (Pat.construct (lid "Fortran_layout") None)
                      (Exp.apply (ex_id name_f) arg_ex)
                  ; Exp.case (Pat.construct (lid "C_layout") None)
                      (Exp.apply (ex_id name_c) arg_ex)])))
        (Exp.apply (ex_id name) [ Nolabel, arr])

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
          | lstr :: l :: _ -> location_error ~loc "Errant string %s after layout." l
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
        arr1 arr2 ~index_offset =
      let index1_ex = ex_id index in
      let offset2_ex = index_offset_to_offset_index index1_ex index_offset in
      let arg_list =
        if with_index then
          if upto then
              [ lookup_ref ref_
              ; index1_ex
              ; get ~open_ arr1 index1_ex
              ; get ~open_ arr2 offset2_ex
              ]
          else
              [ index1_ex
              ; get ~open_ arr1 index1_ex
              ; get ~open_ arr2 offset2_ex
              ; lookup_ref ref_
              ]
        else
          if upto then
            [ lookup_ref ref_
            ; get ~open_ arr1 index1_ex
            ; get ~open_ arr2 offset2_ex
            ]
          else
            [ get ~open_ arr1 index1_ex
            ; get ~open_ arr2 offset2_ex
            ; lookup_ref ref_
            ]
      in
      apply lambda arg_list

    let fold ?(arr_arg1="a") ?(arr_arg2="b") ?(ref_="r") ?(index="i")
      c ~upto init ~start ~mo ~index_offset =
      let start_exp = Exp.constant (const_int start) in
      let end_exp = length_expr ~open_:c.open_ ~mo arr_arg1 in
      let inside_ex = assign_ref ref_
        (fold_apply_f c ~upto ~ref_ ~index ~index_offset arr_arg1 arr_arg2)
      in
      make_ref ref_ init
        (Exp.sequence
           (make_for_loop index ~start_exp ~end_exp upto inside_ex)
           (lookup_ref ref_))

    let iter ?(arr_arg1="a") ?(arr_arg2="b") ?(index="i")
      { open_; with_index; lambda } ~upto ~start ~mo ~index_offset =
      let start_exp = Exp.constant (const_int start) in
      let end_exp = length_expr ~open_ ~mo arr_arg1 in
      let index1_ex = ex_id index in
      let offset2_ex = index_offset_to_offset_index index1_ex index_offset in
      let inside_ex =
        let gets =
          [get ~open_ arr_arg1 index1_ex ; get ~open_ arr_arg2 offset2_ex ]
        in
        let arg_list =
          if with_index then
            index1_ex :: gets
          else
            gets
        in
        let_unit (apply lambda arg_list)
      in
      make_for_loop index ~start_exp ~end_exp upto inside_ex

    let map ?(arr_arg1="a") ?(arr_arg2="b") ?(index="i")
      { open_; with_index; lambda } ~upto
      ~start ~mo
      ?layout2 target_kind =
      let size_ex = dim_expr ~open_ arr_arg1 in
      let start_exp = Exp.constant (const_int start) in
      let end_exp = length_expr ~open_ ~mo arr_arg1 in
      let index1_ex = ex_id index in
      let offset2_ex, tlayout_ex =
        match layout2 with
        | None               ->
            index1_ex
            , Exp.apply (ex_id (opened ~open_ "layout")) (unlabeled [ex_id arr_arg1])
        | Some (target_layout, index_offset) ->
            let offset2_ex = index_offset_to_offset_index index1_ex index_offset in
            let lsfo = L.to_fold_params target_layout in
            offset2_ex, ex_id lsfo.constraint_name
      in
      let inside_ex =
        let arg_list =
          if with_index then
            [ index1_ex ; get ~open_ arr_arg1 index1_ex ]
          else
            [ get ~open_ arr_arg1 index1_ex ]
        in
        set ~open_ arr_arg2 offset2_ex (apply lambda arg_list)
      in
      let tkind_ex = ex_id (K.to_string target_kind) in
      create_array1 ~open_ arr_arg2 tkind_ex tlayout_ex size_ex
        (Exp.sequence
           (make_for_loop index ~start_exp ~end_exp upto inside_ex)
           (ex_id arr_arg2))

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
      let to_args array_layout =
        match constraint_kind with
        | None ->
            Exp.fun_ Nolabel None (constrain_vec ~open_ kind array_layout arg)
              expression
        | Some k ->
            let t1, t2 = K.to_constraint_types k in
            let econstr s = Typ.constr (lid s) [] in
            let ct = Typ.constr (lid (opened ~open_ "t"))
                [ econstr t1; econstr t2; econstr array_layout]
            in
            Exp.fun_ Nolabel None (constrain_vec ~open_ kind array_layout arg)
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
      (* TODO: Check arg1 <> arg2 && layout_arg1 <> layout_arg2 *)
      let to_body array1_layout array2_layout =
        let c1 = constrain_vec ~open_ kind1 array1_layout arg1 in
        let c2 = constrain_vec ~open_ kind2 array2_layout arg2 in
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
      let lsfo1 = L.to_fold_params layout1 in
      let name =
        name_prefix
        ^ L.to_name_suffix layout1
        ^ L.to_name_suffix layout2
      in
      let layout2 = layout2, L.to_index_offsets layout1 layout2 in
      make_let_single ~layout:lsfo1.constraint_name
        ~open_:config.Cc.open_ kind1 name
        (Body.map config ~upto:true kind2 ~layout2
          ~start:lsfo1.start_index ~mo:lsfo1.minus_one)
        (app name)

    let layout_specific_without_app_single ~open_ name_prefix
        kind1 kind2 layout1 layout2
        to_body app =
      let lsfo1 = L.to_fold_params layout1 in
      let lsfo2 = L.to_fold_params layout2 in
      let index_offset = L.to_index_offsets layout1 layout2 in
      let name =
        name_prefix
        ^ L.to_name_suffix layout1
        ^ L.to_name_suffix layout2
      in
      let layout = lsfo1.constraint_name, lsfo2.constraint_name in
      make_let_double ~layout ~open_ kind1 kind2 name
        (to_body ~start:lsfo1.start_index ~mo:lsfo1.minus_one ~index_offset)
        (app name)

    let layout_specific op kind1 kind2 layout1 layout2 =
      match op with
      | Operation.Map { config; arr } ->
          layout_specific_without_app_map config "map"
            kind1 kind2 layout1 layout2
            (fun name -> Exp.apply (ex_id name) (unlabeled [arr]))
      | Operation.Iter { config; arr1; arr2 } ->
          layout_specific_without_app_single ~open_:config.open_ "iter"
            kind1 kind2 layout1 layout2
            (Body.iter config ~upto:true)
            (fun name -> Exp.apply (ex_id name) (unlabeled [arr1; arr2]))
      | Operation.Fold { config; left; init; arr1; arr2 } ->
          layout_specific_without_app_single ~open_:config.open_
            (Operation.fold_to_name config.with_index left)
            kind1 kind2 layout1 layout2
            (Body.fold config ~upto:left init)
            (fun name -> Exp.apply (ex_id name) (unlabeled [arr1; arr2]))

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
        let arg_ex = [Nolabel, ex_id arg] in
        make_let_single ~arg ~open_ kind1 name ~constraint_kind:kind2
          (lswm kind1 kind2 (L Fortran_layout) (L Fortran_layout)
          (fun name_f_f ->
          (lswm kind1 kind2 (L C_layout)       (L C_layout)
          (fun name_c_c ->
          Exp.match_ (Exp.apply (ex_id (opened ~open_ "layout")) arg_ex)
              [ Exp.case (Pat.construct (lid "Fortran_layout") None)
                  (Exp.apply (ex_id name_f_f) arg_ex)
              ; Exp.case (Pat.construct (lid "C_layout") None)
                  (Exp.apply (ex_id name_c_c) arg_ex)
              ]))))
          (Exp.apply (ex_id name) (unlabeled [arr]))

      | Operation.Iter { config; arr1; arr2 } ->
        let lswa k1 k2 l1 l2 =
          layout_specific_without_app_single ~open_:config.open_ "iter2"
            k1 k2 l1 l2
            (Body.iter config ~upto:true)
        in
        let arg1 = "c" in
        let arg2 = "d" in
        let arg1_ex = [Nolabel, ex_id arg1] in
        let arg2_ex = [Nolabel, ex_id arg2] in
        let args_ex = arg1_ex @ arg2_ex in
        make_let_double ~arg1 ~arg2 ~open_ kind1 kind2 name
          (lswa kind1 kind2 (L Fortran_layout) (L Fortran_layout)
          (fun name_f_f ->
          (lswa kind1 kind2 (L Fortran_layout) (L C_layout)
          (fun name_f_c ->
          (lswa kind1 kind2 (L C_layout)       (L Fortran_layout)
          (fun name_c_f ->
          (lswa kind1 kind2 (L C_layout)       (L C_layout)
          (fun name_c_c ->
            Exp.match_ (Exp.apply (ex_id (opened ~open_ "layout")) arg1_ex)
              [ Exp.case (Pat.construct (lid "Fortran_layout") None)
                  (Exp.match_ (Exp.apply (ex_id (opened ~open_ "layout")) arg2_ex)
                      [ Exp.case (Pat.construct (lid "Fortran_layout") None)
                          (Exp.apply (ex_id name_f_f) args_ex)
                      ; Exp.case (Pat.construct (lid "C_layout") None)
                          (Exp.apply (ex_id name_f_c) args_ex)])
              ; Exp.case (Pat.construct (lid "C_layout") None)
                  (Exp.match_ (Exp.apply (ex_id (opened ~open_ "layout")) arg2_ex)
                      [ Exp.case (Pat.construct (lid "Fortran_layout") None)
                          (Exp.apply (ex_id name_c_f) args_ex)
                      ; Exp.case (Pat.construct (lid "C_layout") None)
                          (Exp.apply (ex_id name_c_c) args_ex)])
              ]))))))))
          (Exp.apply (ex_id name) (unlabeled [arr1; arr2]))

      | Operation.Fold { config; left; init; arr1; arr2 } ->
        let lswa k1 k2 l1 l2 =
          layout_specific_without_app_single ~open_:config.open_
            (Operation.fold_to_name config.with_index left)
            k1 k2 l1 l2
            (Body.fold config ~upto:left init)
        in
        let arg1 = "c" in
        let arg2 = "d" in
        let arg1_ex = [Nolabel, ex_id arg1] in
        let arg2_ex = [Nolabel, ex_id arg2] in
        let args_ex = arg1_ex @ arg2_ex in
        make_let_double ~arg1 ~arg2 ~open_ kind1 kind2 name
          (lswa kind1 kind2 (L Fortran_layout) (L Fortran_layout)
          (fun name_f_f ->
          (lswa kind1 kind2 (L Fortran_layout) (L C_layout)
          (fun name_f_c ->
          (lswa kind1 kind2 (L C_layout)       (L Fortran_layout)
          (fun name_c_f ->
          (lswa kind1 kind2 (L C_layout)       (L C_layout)
          (fun name_c_c ->
            Exp.match_ (Exp.apply (ex_id (opened ~open_ "layout")) arg1_ex)
              [ Exp.case (Pat.construct (lid "Fortran_layout") None)
                  (Exp.match_ (Exp.apply (ex_id (opened ~open_ "layout")) arg2_ex)
                      [ Exp.case (Pat.construct (lid "Fortran_layout") None)
                          (Exp.apply (ex_id name_f_f) args_ex)
                      ; Exp.case (Pat.construct (lid "C_layout") None)
                          (Exp.apply (ex_id name_f_c) args_ex)])
              ; Exp.case (Pat.construct (lid "C_layout") None)
                  (Exp.match_ (Exp.apply (ex_id (opened ~open_ "layout")) arg2_ex)
                      [ Exp.case (Pat.construct (lid "Fortran_layout") None)
                          (Exp.apply (ex_id name_c_f) args_ex)
                      ; Exp.case (Pat.construct (lid "C_layout") None)
                          (Exp.apply (ex_id name_c_c) args_ex)])
              ]))))))))
          (Exp.apply (ex_id name) (unlabeled [arr1; arr2]))

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

let transform loc txt payload def =
  let split =  String.split_on_char '.' txt in
  try
    let rec is_open = function
      | "array1" :: t -> operation ~open_:false t
      | "open1" :: t  -> operation ~open_:true t
      | _             -> def ()
    and operation ~open_ t =
      match Single.maybe ~open_ ~loc t payload with
      | Ok expression -> expression
      | Error _fn ->
          begin match Double.maybe ~open_ ~loc t payload with
          | Ok expression -> expression
          | Error fn ->
              location_error ~loc "Unsupported function: %s" fn
          end
    in
    is_open split
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
