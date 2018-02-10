
open Printf
open Bau
open BigarrayExt
open Common


let iteri f v = [%array1.float64 iteri f v]

let modify f v = [%array1.float64 modify f v]
let modifyi f v = [%array1.float64 modifyi f v]

let print_array1 v =
  iteri (printf "%d %f\n") v

let () =
  let _, f, _ = generate Float64 10 in
  print_endline "Test of modification";
  printf "Before:\n";
  print_array1 f;
  modify (fun x -> x /. 2.0) f;
  printf "Divided in half:\n";
  print_array1 f;
  modifyi (fun i _ -> (float i)) f;
  printf "Replaced with index:\n";
  print_array1 f
