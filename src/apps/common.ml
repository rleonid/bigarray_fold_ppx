
open Bau
open BigarrayExt

let time s f =
  let n = Sys.time () in
  let r = f () in
  Printf.printf "%-30s: %f sec\n" s (Sys.time () -. n);
  r

let generate kind n =
  let gen  = Generators.random kind in
  let native = Array.init n (fun _ -> gen ()) in
  let f = Array1.of_array kind Fortran_layout native in
  let c = Array1.of_array kind C_layout native in
  native, f, c


