open Bau
open BigarrayExt
open Common

let add3f a b c =
  a +. b +. c

let sum_r u v =
  let r = ref 0. in
  for i = 1 to Array1.dim v do
    r := add3f !r (Array1.unsafe_get u i) (Array1.unsafe_get v i)
  done;
  !r

let sum_f u v = [%array1.float64.float64.fortran fold_left2 add3f 0. u v]
let sum_fl u v = [%array1.float64.float64.fortran fold_left2 ~init:0. ~f:add3f u v]
let sum_l u v = [%array1.float64.float64 fold_left2 add3f 0. u v]
let sum_ll u v = [%array1.float64.float64 fold_left2 ~init:0. ~f:add3f u v]

let sum_fr u v = [%array1.float64.float64 fold_right2 add3f 0. u v]
let sum_frll u v = [%array1.float64.float64.fortran.fortran fold_right2 add3f 0. u v]

let () =
  let samples, n =
    if Array.length Sys.argv < 3 then
      10000, 40
    else
      int_of_string Sys.argv.(1)
      , int_of_string Sys.argv.(2)
  in
  print_endline "Test of folds 2 by summing 2 float arrays.";
  Printf.printf "%d samples of arrays of length %d \n" samples n;
  let data =
    Array.init samples (fun _ -> generate Float64 n, generate Float64 n)
  in
  Gc.(set { (get ()) with max_overhead      = 1000000
                        ; allocation_policy = 1
                        ; minor_heap_size   = 4096000
          });
  let test name op = time name (fun () -> Array.map op data) in
  let regular, typed, wlayout, right, rightwl = gc_between stdout ""
    (fun () ->
      let regular = test "regular fold as for loop"
                      (fun ((_,f1,_), (_,f2,_)) -> sum_r f1 f2) in
      let typed   = test "created fold_ppx"
                      (fun ((_,f1,_), (_,f2,_)) -> sum_f f1 f2) in
      let _       = test "created fold_ppx labeled"
                      (fun ((_,f1,_), (_,f2,_)) -> sum_fl f1 f2) in
      let wlayout = test "no layout"
                      (fun ((_,f1,_), (_,f2,_)) -> sum_l f1 f2) in
      let _       = test "no layout labeled"
                      (fun ((_,f1,_), (_,f2,_)) -> sum_ll f1 f2) in
      let right   = test "with a fold right"
                      (fun ((_,f1,_), (_,f2,_)) -> sum_fr f1 f2) in
      let rightwl = test "with a layout specified fold right"
                      (fun ((_,f1,_), (_,f2,_)) -> sum_frll f1 f2) in
      regular, typed, wlayout, right, rightwl)
  in
  Printf.printf "equal %b\n"
    (regular = typed
      && typed = wlayout
      && wlayout = right
      && right = rightwl)
