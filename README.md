# Clocked Functional Reactive Programming

An implementation of the Simply-typed version of Clocked Type Theory (CloTT) [clocks] for my master's thesis at ITU (pdf is in the repo).
CloFRP (also known as CloPL) is a language that enables safe co-inductive programming.
Specifically, it uses guarded recursion to ensure that co-recursive definitions are productive and causal. The novel idea
compared to ordinary nakano-style guarded recursion is that it introduces the notion of clocks and ticks
on these clocks, which are used to unfold guarded-recursive definitions. One can quantify over clocks to
express truly coinductive definitions (as opposed to guarded-recursive) that maintain the productivity
guarantees, but relax the causality constraint. As such, we can bridge the gap between co-recursive
and guarded-recursive definitions. On top of that, the "guardedness" of a recursive function is explicit
in its type signature.

Aside from these ideas, CloFRP resembles an ordinary Haskell-inspired language. As such it features:
- Datatype declarations syntax ála vanilla Haskell
- Type synonyms 
- Automatic derivation of fmap (functor map) for strictly-positive types
- Bi-directional higher-rank type inference - polymorphic functions must be annotated, but everything else should
  be inferrable.
- Higher-kinded types
- Guarded recursion
- Well-founded primitive recursion
- A limited form of impredicativity via explicit type applications

Notable differences between Haskell:
- No type-classes (functors are special-case built-in pseudo-typeclass that can only be derived)
- Basically no language extensions (except for `TypeApplications` and `ScopedTypeVariables` which are built-in)
- Strict evaluation
- Clocks, ticks on clocks and clock-abstraction
- Not white-space aware syntax.
- `(:)` for type-annotations
- No kind-inference of type-variables -- they must be annotated if they're not of kind `*`
- No general recursion

Note that this is very much research-grade software!

## Project Structure
The `library` directory contains all the interesting code. `test-suite` contains the test suite (unsurprisingly) -- the test suite
consists of just over 300 hand-written scenario tests.
The code is split into several folders and modules:
- `AST` contains the abstract syntax tree of programs written in CloFRP - expressions, types, patterns, names, primitives, declarations and programs
- `Check` contains code to type-check (and elaborate, which should be refactored out) programs written in CloFRP. The meat of the implementation
  lies within this namespace.
- `Evals` contains code that evaluates CloFRP programs
- `Parser` contains parsers for various CloFRP terms
- `Derive` contains code to derive functors from data-type declarations
- `Interop` defines how to combine CloFRP programs with Haskell programs in a somewhat typesafe manner
- `QuasiQuoter` defines quasi-quoters that allow Haskell programmers to write programs in CloFRP easily
- `Annotated, Context, Pretty` and `Utils` contain mostly un-interesting helper functions to work with annotated AST's, different contexts,
  pretty-printing ASTs and assorted utility functions.

## Usage
You can clone this repository and build to try out the examples. You can also use
`stack` or `cabal` to install it as a dependencyl

The primary way to use `CloFRP` is through the `QuasiQuoter`s it exposes in 
`CloFRP.QuasiQuoter`. There are two main ways:

- The `hsclofrp` QuasiQuoter takes a textual `CloFRP` program and compiles it to 
  a semantically equivalent Haskell program which can be used from the rest of your
  Haskell application without any problems.
- The `clofrp` QuasiQuoter takes a textual `CloFRP` program and compiles it to an
  abstract syntax tree of `CloFRP` (the `AST.Expr` type). You can then evaluate this
  AST with `Eval.evalProg`. This approach is however a lot slower, and interoperation
  with Haskell is a lot more involved (see the paper for details).

## Examples
Examples are scattered around the code-base a bit. There are some in the
`Examples` module, but most are located in the `benchmark` and `test-suite`
directories, for example in the `Fixtures` module.