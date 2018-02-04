
open Printf
open Bau
open BigarrayExt
open Common

let iteri f v = [%array1.float64 iteri f v]
let iteri_f f v = [%array1.float64.fortran iteri f v]
let iteri_c f v = [%array1.float64.c iteri f v]

let print_all v =
  iteri (printf "%d %f\n") v

let print_fortran v =
  iteri_f (printf "%d %f\n") v

let print_c v =
  iteri_c (printf "%d %f\n") v

let () =
  let _, f, c = generate Float64 10 in
  printf "Fortran with out layout:\n";
  print_all f;
  printf "Fortran with layout:\n";
  print_fortran f;
  printf "C with layout:\n";
  print_c c
