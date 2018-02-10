
open Printf
open Bau
open BigarrayExt
open Common

let iter2 f u v = [%array1.float64.float64 iter2 f u v]
let iter_f2 f u v = [%array1.float64.float64.fortran iter2 f u v]
let iter_c2 f u v = [%array1.float64.float64.c iter2 f u v]

let iteri2 f u v = [%array1.float64.float64 iteri2 f u v]
let iteri_f2 f u v = [%array1.float64.float64.fortran iteri2 f u v]
let iteri_c2 f u v = [%array1.float64.float64.c iteri2 f u v]

let foldi_left2 f u v = [%array1.float64.float64 foldi_left2 f () u v]
let foldi_right2 f v u = [%array1.float64.float64 foldi_right2 f () u v]

let p2i = printf "%d %f %f\n"
let print_all u v =
  iteri2 p2i u v

let print_fortran u v =
  iteri_f2 p2i u v

let print_c u v =
  iteri_c2 p2i u v

let print_as_left_fold u v =
  foldi_left2 (fun () i u v -> p2i i u v) u v

let print_as_right_fold u v =
  foldi_right2 (fun i u v () -> p2i i u v) u v

let () =
  let _, f1, c1 = generate Float64 10 in
  let _, f2, c2 = generate Float64 10 in
  print_endline "Test of iteration over 2 things";
  printf "Fortran with out layout:\n";
  print_all f1 f2;
  printf "Fortran with layout:\n";
  print_fortran f1 f2;
  printf "C with layout:\n";
  print_c c1 c2;

  printf "Mixed (fortran & c) layout:\n";
  print_all f1 c2;

  printf "Mixed (c & fortran) layout:\n";
  print_all c1 f2;

  printf "As left fold:\n";
  print_as_left_fold f1 f2;

  printf "As right fold:\n";
  print_as_right_fold f1 f2;
