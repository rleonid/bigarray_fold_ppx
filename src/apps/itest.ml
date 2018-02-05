
open Printf
open Bau
open BigarrayExt
open Common

let iteri f v = [%array1.float64 iteri f v]
let iteri_f f v = [%array1.float64.fortran iteri f v]
let iteri_c f v = [%array1.float64.c iteri f v]

let foldi_left f v = [%array1.float64 foldi_left f () v]
let foldi_right f v = [%array1.float64 foldi_right f () v]

let print_all v =
  iteri (printf "%d %f\n") v

let print_fortran v =
  iteri_f (printf "%d %f\n") v

let print_c v =
  iteri_c (printf "%d %f\n") v

let print_as_left_fold v =
  foldi_left (fun () i f -> printf "%d %f\n" i f) v

let print_as_right_fold v =
  foldi_right (fun i f () -> printf "%d %f\n" i f) v

let () =
  let _, f, c = generate Float64 10 in
  printf "Fortran with out layout:\n";
  print_all f;
  printf "Fortran with layout:\n";
  print_fortran f;
  printf "C with layout:\n";
  print_c c;

  printf "As left fold:\n";
  print_as_left_fold f;

  printf "As right fold:\n";
  print_as_right_fold f;
