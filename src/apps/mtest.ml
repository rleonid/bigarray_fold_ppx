
open Printf
open Bau
open BigarrayExt
open Common


let iteri f v = [%array1.float64 iteri f v]

let mutate f v = [%array1.float64 mutate f v]
let mutatei f v = [%array1.float64 mutatei f v]

let print_array1 v =
  iteri (printf "%d %f\n") v

let () =
  let _, f, _ = generate Float64 10 in
  printf "Before:\n";
  print_array1 f;
  mutate (fun x -> x /. 2.0) f;
  printf "Divided in half:\n";
  print_array1 f;
  mutatei (fun i _ -> (float i)) f;
  printf "Replaced with index:\n";
  print_array1 f
