[![Build Status](https://travis-ci.org/rleonid/bigarray_fold_ppx.svg?branch=master)](https://travis-ci.org/rleonid/bigarray_fold_ppx)

BigArray Fold PPX
=================

## Motivation

The `OCaml` compiler has built in primitives (see `caml_ba_ref_` in
`bigarray.mli`) that can be used to index into a Bigarray faster if the full
[kind](http://caml.inria.fr/pub/docs/manual-ocaml/libref/Bigarray.html#TYPEkind)
of the bigarray is known. To avoid repeated writing of the type signatures we use
`ppx` to write an efficient `fold_left`, `fold_right` or `iter`:

```OCaml
let sum_b v = [%array1.float64.fortran fold_left.float64 (+.) 0. v]
```

A simple profiling program: [`prof.ml`](src/apps/prof.ml)
compares three implementations of summing either a native array of floats or
an `(float, float64, fortran_layout) Array1.t` :

1. Using native arrays.

  ```OCaml
  let sum_n (v : float array) = Array.fold_left (+.) 0. v
  ```

2. Without specifying the type of the `Array1.t`

  ```OCaml
  let sum_r v =
    let r = ref 0. in
    for i = 1 to Array1.dim v do
      r := !r +. Array1.unsafe_get v i
    done;
    !r
  ```

3. Using the typed code generated via `fold_ppx`:

  ```OCaml
  let sum_f v = [%array1.float64.fortran fold_left (+.) 0. v]
  ```

Typical performance results look like:

  ```bash
  $ prof.exe
  10000 samples of arrays of length 40
  native                        : 0.018666 sec
  regular fold as for loop      : 0.009421 sec
  created fold_ppx              : 0.001143 sec
  ```

## Usage

The general syntax is

```OCaml
[%bigarraytype.kind(.layout) operation f (init) v]
```

  - `bigarraytype` - Currently only supports `"array1"`
  - `kind` - One of:
          `float32`,
          `float64`,
          `complex32`,
          `complex64`,
          `int8_signed`,
          `int8_unsigned`,
          `int16_signed`,
          `int16_unsigned`,
          `int32`,
          `int64`,
          `int`,
          `nativeint`,
          or `char`.
  - `layout` Optional but can be `fortran` or `c`. If left off `fold_ppx`
    will generate code that detects the layout and acts accordingly.
  - `operation` - `fold_left`, `fold_right`, `foldi_left`, `foldi_right`,
     `iter`,`iteri`, `modify` or `modifyi`.
  - `f` the `fold` or `iter` function to apply. If `v` has type
    `(k, 'b, 'c) Array1.t` then `f` should have types:
      - `fold_left`     : `('a -> k -> 'a)`
      - `fold_right`    : `(k -> 'a -> 'a)`
      - `foldi_left`    : `('a -> int -> k -> 'a)`
      - `foldi_right`   : `(int -> k -> 'a -> 'a)`
      - `iter`          : `(k -> unit)`
      - `iteri`         : `(int -> k -> unit)`
      - `modify`        : `(k -> k)`
      - `modifyi`       : `(int -> k -> k)`

    Just like regular `Array` values. These can be applied with a label: `~f`
    but then `~init` must be labeled as well.

  - `init` the initial value, only for folds
  - `v` the `Array1`
