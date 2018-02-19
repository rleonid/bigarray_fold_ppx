
open Bau
open BigarrayExt

let time s f =
  let n = Sys.time () in
  let r = f () in
  Printf.printf "%-30s: %f sec\n" s (Sys.time () -. n);
  r

let d = 1e-6
let significantly_different_from x y = y < (x -. d) || y > (x +. d )
let equal_floats x y = not (significantly_different_from x y)

let eq_array arr1 arr2 =
  Array.fold_left (fun (b, i) v ->
    b && equal_floats v arr2.(i), i + 1) (true, 0) arr1
  |> fst

let eq_array_c arr1 arr2 =
  Array.fold_left (fun (b, i) v ->
    b && equal_floats v.Complex.re arr2.(i).Complex.re
      && equal_floats v.Complex.im arr2.(i).Complex.im, i + 1) (true, 0) arr1
  |> fst


let generate kind n =
  let gen  = Generators.random kind in
  let native = Array.init n (fun _ -> gen ()) in
  let f = Array1.of_array kind Fortran_layout native in
  let c = Array1.of_array kind C_layout native in
  native, f, c

let generate2 kind n =
  let gen  = Generators.random kind in
  let native = Array.init n (fun _ -> Array.init n (fun _ -> gen ())) in
  let f = Array2.of_array kind Fortran_layout native in
  let c = Array2.of_array kind C_layout native in
  native, f, c

let generate3 kind n =
  let gen  = Generators.random kind in
  let ai f = Array.init n f in
  let native = ai (fun _ -> ai (fun _ -> ai (fun _ -> gen ()))) in
  let f = Array3.of_array kind Fortran_layout native in
  let c = Array3.of_array kind C_layout native in
  native, f, c

let gc_between oc s f =
  let open Gc in
  let before = stat () in
  let r = f () in
  let after = stat () in
  Printf.fprintf oc "%s Gc change: \n\
    \t { minor_words : %f;\n\
    \t   promoted_words : %f;\n\
    \t   major_words : %f;\n\
    \t   minor_collections : %d;\n\
    \t   major_collections : %d;\n\
    \t   heap_words : %d;\n\
    \t   heap_chunks : %d;\n\
    \t   live_words : %d;\n\
    \t   live_blocks : %d;\n\
    \t   free_words : %d;\n\
    \t   free_blocks : %d;\n\
    \t   largest_free : %d;\n\
    \t   fragments : %d;\n\
    \t   compactions : %d;\n\
    \t   top_heap_words : %d;\n\
    \t   stack_size : %d;\n\
    \t }\n"
      s
      (after.minor_words -. before.minor_words)
      (after.promoted_words -. before.promoted_words)
      (after.major_words -. before.major_words)
      (after.minor_collections - before.minor_collections)
      (after.major_collections - before.major_collections)
      (after.heap_words - before.heap_words)
      (after.heap_chunks - before.heap_chunks)
      (after.live_words - before.live_words)
      (after.live_blocks - before.live_blocks)
      (after.free_words - before.free_words)
      (after.free_blocks - before.free_blocks)
      (after.largest_free - before.largest_free)
      (after.fragments - before.fragments)
      (after.compactions - before.compactions)
      (after.top_heap_words - before.top_heap_words)
      (after.stack_size - before.stack_size);
  r
