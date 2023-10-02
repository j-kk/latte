# Latte compiler

Latte compiler written in Haskell.

## Compilation

To compile, call the `make` command in the root directory.
The compiler required is `ghc`.
`make` also calls the `liblatte.c` library compilation containing basic functions (printInt, etc.).

## Extensions
- arrays
- structures
- objects (attributes, methods, inheritance without method substitution)
- virtual methods