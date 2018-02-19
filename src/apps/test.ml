open Bau
open BigarrayExt
open Common

(* TODO: Get to the bottom of if the differences are
   just due to comparing left vs right and different roundings.*)
type ('a, 'b) pt =
  { kind  : ('a, 'b) kind
  ; sum_n : 'a array -> 'a
  ; sum_fl : ('a, 'b, fortran_layout) Array1.t -> 'a
  ; sum_fr : ('a, 'b, fortran_layout) Array1.t -> 'a
  ; sum_cl : ('a, 'b, c_layout) Array1.t -> 'a
  ; sum_cr : ('a, 'b, c_layout) Array1.t -> 'a
  (* Using reduce *)
  ; red_fl : ('a, 'b, fortran_layout) Array1.t -> 'a
  ; red_fr : ('a, 'b, fortran_layout) Array1.t -> 'a
  ; red_cl : ('a, 'b, c_layout) Array1.t -> 'a
  ; red_cr : ('a, 'b, c_layout) Array1.t -> 'a
  }

let () =
  let open Core_bench.Std in
  let samples, n = 10000, 40 in
    (*if Array.length Sys.argv < 3 then
      10000, 40
    else
      int_of_string Sys.argv.(1)
      , int_of_string Sys.argv.(2)
  in*)
  Printf.printf "%d samples of %d \n" samples n;
  let fold = false in
  let per : type a b. string -> (a, b) pt -> Bench.Test.t =
    fun ks pt ->
      let data = Array.init samples (fun _ -> generate pt.kind n) in
      let test name op =
        Bench.Test.create ~name (fun () -> Array.map op data)
      in
      if fold then
        [ test "native"               (fun (n,_,_) -> pt.sum_n n)
        ; test "array1 left fortran"  (fun (_,f,_) -> pt.sum_fl f)
        ; test "array1 right fortran" (fun (_,f,_) -> pt.sum_fr f)
        ; test "array1 left c"        (fun (_,_,c) -> pt.sum_cl c)
        ; test "array1 right c"       (fun (_,_,c) -> pt.sum_cr c)
        ] |> Bench.Test.create_group ~name:ks
      else
        [ test "native"               (fun (n,_,_) -> pt.sum_n n)
        ; test "array1 left fortran"  (fun (_,f,_) -> pt.red_fl f)
        ; test "array1 right fortran" (fun (_,f,_) -> pt.red_fr f)
        ; test "array1 left c"        (fun (_,_,c) -> pt.red_cl c)
        ; test "array1 right c"       (fun (_,_,c) -> pt.red_cr c)
        ] |> Bench.Test.create_group ~name:ks
  in
  let clor a b = (int_of_char a) lor (int_of_char b) |> Char.chr in
  [ per "float32"
      { kind  = Float32
      ; sum_n = (fun (v : float array) -> Array.fold_left (+.) 0. v)
      ; sum_fl = (fun v -> [%array1.float32.fortran fold_left (+.) 0. v])
      ; sum_fr = (fun v -> [%array1.float32.fortran fold_right (+.) 0. v])
      ; sum_cl = (fun v -> [%array1.float32.c fold_left (+.) 0. v])
      ; sum_cr = (fun v -> [%array1.float32.c fold_right (+.) 0. v])
      ; red_fl = (fun v -> [%array1.float32.fortran reduce_left (+.) v])
      ; red_fr = (fun v -> [%array1.float32.fortran reduce_right (+.) v])
      ; red_cl = (fun v -> [%array1.float32.c reduce_left (+.) v])
      ; red_cr = (fun v -> [%array1.float32.c reduce_right (+.) v])
      }
  ; per "float64"
      { kind  = Float64
      ; sum_n = (fun (v : float array) -> Array.fold_left (+.) 0. v)
      ; sum_fl = (fun v -> [%array1.float64.fortran fold_left (+.) 0. v])
      ; sum_fr = (fun v -> [%array1.float64.fortran fold_right (+.) 0. v])
      ; sum_cl = (fun v -> [%array1.float64.c fold_left (+.) 0. v])
      ; sum_cr = (fun v -> [%array1.float64.c fold_right (+.) 0. v])
      ; red_fl = (fun v -> [%array1.float64.fortran reduce_left (+.) v])
      ; red_fr = (fun v -> [%array1.float64.fortran reduce_right (+.) v])
      ; red_cl = (fun v -> [%array1.float64.c reduce_left (+.) v])
      ; red_cr = (fun v -> [%array1.float64.c reduce_right (+.)  v])
      }
  ; per "complex32"
      { kind  = Complex32
      ; sum_n = (fun (v : Complex.t array)  -> Array.fold_left Complex.add Complex.zero v)
      ; sum_fl = (fun v -> [%array1.complex32.fortran fold_left Complex.add Complex.zero v])
      ; sum_fr = (fun v -> [%array1.complex32.fortran fold_right Complex.add Complex.zero v])
      ; sum_cl = (fun v -> [%array1.complex32.c fold_left Complex.add Complex.zero v])
      ; sum_cr = (fun v -> [%array1.complex32.c fold_right Complex.add Complex.zero v])
      ; red_fl = (fun v -> [%array1.complex32.fortran reduce_left Complex.add v])
      ; red_fr = (fun v -> [%array1.complex32.fortran reduce_right Complex.add v])
      ; red_cl = (fun v -> [%array1.complex32.c reduce_left Complex.add v])
      ; red_cr = (fun v -> [%array1.complex32.c reduce_right Complex.add v])
      }
  ; per "complex64"
      { kind  = Complex64
      ; sum_n = (fun (v : Complex.t array) -> Array.fold_left Complex.add Complex.zero v)
      ; sum_fl = (fun v -> [%array1.complex64.fortran fold_left Complex.add Complex.zero v])
      ; sum_fr = (fun v -> [%array1.complex64.fortran fold_right Complex.add Complex.zero v])
      ; sum_cl = (fun v -> [%array1.complex64.c fold_left Complex.add Complex.zero v])
      ; sum_cr = (fun v -> [%array1.complex64.c fold_right Complex.add Complex.zero v])
      ; red_fl = (fun v -> [%array1.complex64.fortran reduce_left Complex.add v])
      ; red_fr = (fun v -> [%array1.complex64.fortran reduce_right Complex.add v])
      ; red_cl = (fun v -> [%array1.complex64.c reduce_left Complex.add v])
      ; red_cr = (fun v -> [%array1.complex64.c reduce_right Complex.add v])
      }
  ; per "int8_signed"
      { kind  = Int8_signed
      ; sum_n = (fun (v : int array) -> Array.fold_left (+) 0 v)
      ; sum_fl = (fun v -> [%array1.int8_signed.fortran fold_left (+) 0 v])
      ; sum_fr = (fun v -> [%array1.int8_signed.fortran fold_right (+) 0 v])
      ; sum_cl = (fun v -> [%array1.int8_signed.c fold_left (+) 0 v])
      ; sum_cr = (fun v -> [%array1.int8_signed.c fold_right (+) 0 v])
      ; red_fl = (fun v -> [%array1.int8_signed.fortran reduce_left (+) v])
      ; red_fr = (fun v -> [%array1.int8_signed.fortran reduce_right (+) v])
      ; red_cl = (fun v -> [%array1.int8_signed.c reduce_left (+) v])
      ; red_cr = (fun v -> [%array1.int8_signed.c reduce_right (+) v])
      }
  ; per "int8_unsigned"
      { kind  = Int8_unsigned
      ; sum_n = (fun (v : int array) -> Array.fold_left (+) 0 v)
      ; sum_fl = (fun v -> [%array1.int8_unsigned.fortran fold_left (+) 0 v])
      ; sum_fr = (fun v -> [%array1.int8_unsigned.fortran fold_right (+) 0 v])
      ; sum_cl = (fun v -> [%array1.int8_unsigned.c fold_left (+) 0 v])
      ; sum_cr = (fun v -> [%array1.int8_unsigned.c fold_right (+) 0 v])
      ; red_fl = (fun v -> [%array1.int8_unsigned.fortran reduce_left (+) v])
      ; red_fr = (fun v -> [%array1.int8_unsigned.fortran reduce_right (+) v])
      ; red_cl = (fun v -> [%array1.int8_unsigned.c reduce_left (+) v])
      ; red_cr = (fun v -> [%array1.int8_unsigned.c reduce_right (+) v])
      }
  ; per "int16_signed"
      { kind  = Int16_signed
      ; sum_n = (fun (v : int array) -> Array.fold_left (+) 0 v)
      ; sum_fl = (fun v -> [%array1.int16_signed.fortran fold_left (+) 0 v])
      ; sum_fr = (fun v -> [%array1.int16_signed.fortran fold_right (+) 0 v])
      ; sum_cl = (fun v -> [%array1.int16_signed.c fold_left (+) 0 v])
      ; sum_cr = (fun v -> [%array1.int16_signed.c fold_right (+) 0 v])
      ; red_fl = (fun v -> [%array1.int16_signed.fortran reduce_left (+) v])
      ; red_fr = (fun v -> [%array1.int16_signed.fortran reduce_right (+) v])
      ; red_cl = (fun v -> [%array1.int16_signed.c reduce_left (+) v])
      ; red_cr = (fun v -> [%array1.int16_signed.c reduce_right (+) v])
      }
  ; per "int16_unsigned"
      { kind  = Int16_unsigned
      ; sum_n = (fun (v : int array) -> Array.fold_left (+) 0 v)
      ; sum_fl = (fun v -> [%array1.int16_unsigned.fortran fold_left (+) 0 v])
      ; sum_fr = (fun v -> [%array1.int16_unsigned.fortran fold_right (+) 0 v])
      ; sum_cl = (fun v -> [%array1.int16_unsigned.c fold_left (+) 0 v])
      ; sum_cr = (fun v -> [%array1.int16_unsigned.c fold_right (+) 0 v])
      ; red_fl = (fun v -> [%array1.int16_unsigned.fortran reduce_left (+) v])
      ; red_fr = (fun v -> [%array1.int16_unsigned.fortran reduce_right (+) v])
      ; red_cl = (fun v -> [%array1.int16_unsigned.c reduce_left (+) v])
      ; red_cr = (fun v -> [%array1.int16_unsigned.c reduce_right (+) v])
      }
  ; per "int"
      { kind  = Int
      ; sum_n = (fun (v : int array) -> Array.fold_left (+) 0 v)
      ; sum_fl = (fun v -> [%array1.int.fortran fold_left (+) 0 v])
      ; sum_fr = (fun v -> [%array1.int.fortran fold_right (+) 0 v])
      ; sum_cl = (fun v -> [%array1.int.c fold_left (+) 0 v])
      ; sum_cr = (fun v -> [%array1.int.c fold_right (+) 0 v])
      ; red_fl = (fun v -> [%array1.int.fortran reduce_left (+) v])
      ; red_fr = (fun v -> [%array1.int.fortran reduce_right (+) v])
      ; red_cl = (fun v -> [%array1.int.c reduce_left (+) v])
      ; red_cr = (fun v -> [%array1.int.c reduce_right (+) v])
      }
  ; per "int32"
      { kind  = Int32
      ; sum_n = (fun (v : int32 array) -> Array.fold_left Int32.add 0l v)
      ; sum_fl = (fun v -> [%array1.int32.fortran fold_left Int32.add 0l v])
      ; sum_fr = (fun v -> [%array1.int32.fortran fold_right Int32.add 0l v])
      ; sum_cl = (fun v -> [%array1.int32.c fold_left Int32.add 0l v])
      ; sum_cr = (fun v -> [%array1.int32.c fold_right Int32.add 0l v])
      ; red_fl = (fun v -> [%array1.int32.fortran reduce_left Int32.add v])
      ; red_fr = (fun v -> [%array1.int32.fortran reduce_right Int32.add v])
      ; red_cl = (fun v -> [%array1.int32.c reduce_left Int32.add v])
      ; red_cr = (fun v -> [%array1.int32.c reduce_right Int32.add v])
      }
  ; per "int64"
      { kind  = Int64
      ; sum_n = (fun (v : int64 array) -> Array.fold_left Int64.add 0L v)
      ; sum_fl = (fun v -> [%array1.int64.fortran fold_left Int64.add 0L v])
      ; sum_fr = (fun v -> [%array1.int64.fortran fold_right Int64.add 0L v])
      ; sum_cl = (fun v -> [%array1.int64.c fold_left Int64.add 0L v])
      ; sum_cr = (fun v -> [%array1.int64.c fold_right Int64.add 0L v])
      ; red_fl = (fun v -> [%array1.int64.fortran reduce_left Int64.add v])
      ; red_fr = (fun v -> [%array1.int64.fortran reduce_right Int64.add v])
      ; red_cl = (fun v -> [%array1.int64.c reduce_left Int64.add v])
      ; red_cr = (fun v -> [%array1.int64.c reduce_right Int64.add v])
      }
  ; per "nativeint"
      { kind  = Nativeint
      ; sum_n = (fun (v : Nativeint.t array) -> Array.fold_left Nativeint.add 0n v)
      ; sum_fl = (fun v -> [%array1.nativeint.fortran fold_left Nativeint.add 0n v])
      ; sum_fr = (fun v -> [%array1.nativeint.fortran fold_right Nativeint.add 0n v])
      ; sum_cl = (fun v -> [%array1.nativeint.c fold_left Nativeint.add 0n v])
      ; sum_cr = (fun v -> [%array1.nativeint.c fold_right Nativeint.add 0n v])
      ; red_fl = (fun v -> [%array1.nativeint.fortran reduce_left Nativeint.add v])
      ; red_fr = (fun v -> [%array1.nativeint.fortran reduce_right Nativeint.add v])
      ; red_cl = (fun v -> [%array1.nativeint.c reduce_left Nativeint.add v])
      ; red_cr = (fun v -> [%array1.nativeint.c reduce_right Nativeint.add v])
      }
  ; per "char"
      { kind  = Char
      ; sum_n = (fun (v : char array) -> Array.fold_left clor '\000' v)
      ; sum_fl = (fun v -> [%array1.char.fortran fold_left clor '\000' v])
      ; sum_fr = (fun v -> [%array1.char.fortran fold_right clor '\000' v])
      ; sum_cl = (fun v -> [%array1.char.c fold_left clor '\000' v])
      ; sum_cr = (fun v -> [%array1.char.c fold_right clor '\000' v])
      ; red_fl = (fun v -> [%array1.char.fortran reduce_left clor v])
      ; red_fr = (fun v -> [%array1.char.fortran reduce_right clor v])
      ; red_cl = (fun v -> [%array1.char.c reduce_left clor v])
      ; red_cr = (fun v -> [%array1.char.c reduce_right clor v])
      }]
  |> Bench.make_command
  |> Core.Command.run
