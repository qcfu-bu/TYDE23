# TLL Compiler

## OCaml Dependencies
- `dune`
- `ppxlib`
- `ppx_deriving`
- `fmt`
- `mparser`
- `zarith`

## C Dependencies
- `clang`
- `pthreads`
- `bohem gc`

## Usage
Example source files of varying complexity are given in the `tests` directory. 

To compile a TLL program such as `test1.clc`, execute the command `dune exec --profile release bin/main.exe tests/test1.clc` from the project root.

A `log.clc` file will be generated at the project root logging the intermediate representation at each phase of compilation. Another `main.c` file will be generated in the `c` directory containing the emitted C code. 

The emitted C code can be further compiled to a `main.out` executable by running `make -C ./c` from the project root.
