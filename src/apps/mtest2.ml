
open Printf
open Bau
open BigarrayExt
open Common


let generic_m f nk v =
  let l = Array1.dim v in
  let n = Array1.create nk (Array1.layout v) l in
  for i = 1 to l do
    Array1.unsafe_set n i (f (Array1.unsafe_get v i))
  done;
  n

let generic v = generic_m Complex.norm2 Float64 v

let regular_m v =
  let l = Array1.dim v in
  let n = Array1.create Float64 Fortran_layout l in
  for i = 1 to l do
    Array1.unsafe_set n i (Complex.norm2 (Array1.unsafe_get v i))
  done;
  n

let ppx_m_with_layout v = [%array1.complex64.float64.fortran map Complex.norm2 v]
let ppx_m_without_layout v = [%array1.complex64.float64 map Complex.norm2 v]

(* We don't test this function but it should be equivalent to previous . *)
let ppx_m_with_layout2 v =
  [%array1.complex64.float64.fortran.c map Complex.norm2 v]

(* Also don't use but to show labeled. *)
let ppx_m_labeled_with_layout v = [%array1.complex64.float64.fortran map ~f:Complex.norm2 v]

let ppx_m_via_mapi v = [%array1.complex64.float64.fortran mapi ~f:(fun _i c -> Complex.norm2 c) v]
let ppx_m_switch_layout v = [%array1.complex64.float64.fortran.c mapi ~f:(fun _i c -> Complex.norm2 c) v]

let layout_agnostic_comp u v =
  [%array1.float64 fold_left2 ~f:(fun acc (f1:float) f2 -> acc && f1 = f2)
      ~init:true u v]

let for_both_arr f r1 r2 =
  let acc = ref true in
  let n = Array.length r1 in
  for i = 0 to n - 1 do
    acc := !acc && f r1.(i) r2.(i)
  done;
  !acc

let () =
  let samples, n =
    if Array.length Sys.argv < 3 then
      1000, 50
    else
      int_of_string Sys.argv.(1)
      , int_of_string Sys.argv.(2)
  in
  print_endline "Test mapping";
  let data = Array.init samples (fun _ ->
      let _, f, _ = generate Complex64 n in
      f)
  in
  Gc.(set { (get ()) with max_overhead      = 1000000
                        ; allocation_policy = 1
                        ; minor_heap_size   = 4096000
          });
  let test name op = time name (fun () -> Array.map op data) in
  let generic, regular, without, with_l, v_mapi, wswitch =
    gc_between stdout "" (fun () ->
      let without = test "Using ppx without layout" ppx_m_without_layout in
      let generic = test "Using a generic map" generic in
      let with_l  = test "Using ppx with layout" ppx_m_with_layout in
      let regular = test "Using regular for loop" regular_m in
      let v_mapi  = test "Using ppx via mapi" ppx_m_via_mapi in
      let wswitch = test "Using ppx and switching layout!" ppx_m_switch_layout in
      generic, regular, without, with_l, v_mapi, wswitch)
  in
  Printf.printf "equal %b\n"
    (generic = regular
     && regular = without
     && without = with_l
     && with_l = v_mapi
     && for_both_arr layout_agnostic_comp v_mapi wswitch
    )
