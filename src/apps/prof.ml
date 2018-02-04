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

let sum_n (v : float array) = Array.fold_left (+.) 0. v
let sum_r v =
  let r = ref 0. in
  for i = 1 to Array1.dim v do
    r := !r +. Array1.unsafe_get v i
  done;
  !r
let sum_f v = [%array1.float64.fortran fold_left (+.) 0. v]
let sum_fl v = [%array1.float64.fortran fold_left ~init:0. ~f:(+.) v]
let sum_l v = [%array1.float64 fold_left (+.) 0. v]
let sum_ll v = [%array1.float64 fold_left ~init:0. ~f:(+.) v]

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

let () =
  let samples, n =
    if Array.length Sys.argv < 3 then
      10000, 40
    else
      int_of_string Sys.argv.(1)
      , int_of_string Sys.argv.(2)
  in
  Printf.printf "%d samples of arrays of length %d \n" samples n;
  let data = Array.init samples (fun _ -> generate Float64 n) in
  Gc.(set { (get ()) with max_overhead      = 1000000
                        ; allocation_policy = 1
                        ; minor_heap_size   = 4096000
          });
  let test name op = time name (fun () -> Array.map op data) in
  let native, regular, typed, wlayout = gc_between stdout ""
    (fun () ->
      let native  = test "native" (fun (n,_,_) -> sum_n n) in
      let regular = test "regular fold as for loop" (fun (_,f,_) -> sum_r f) in
      let typed   = test "created fold_ppx" (fun (_,f,_) -> sum_f f) in
      let _       = test "created fold_ppx labeled" (fun (_,f,_) -> sum_fl f) in
      let wlayout = test "no layout" (fun (_,f,_) -> sum_l f) in
      let _       = test "no layout labeled" (fun (_,f,_) -> sum_l f) in
      native, regular, typed, wlayout)
  in
  Printf.printf "equal %b\n"
    (native = regular && regular = typed && typed = wlayout)
