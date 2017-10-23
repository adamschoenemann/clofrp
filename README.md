# [Simply Typed Clocked Type Theory][clott]

For my master's thesis at ITU

## TODO
- Support higher-kinded types (should be not that hard)
  - Infer kind of tvar syntactically
  - Maintain the kind-info either in kind-ctx or annotate with kind in TyCtx
- Check/infer lambdas with annotated type-params
- Parse and desugar multi-param lambdas ✓
- Syntax sugar for tuples/units/lists?
- Optimize type-checking in general
- Make sure everything is sane by checking context-wellformedness more and checking that no impredicativeness takes place
  - Note: Assigning an existential to a partially-applied type-constructor is fine
- Add the actual CloTT primitives and rules
- Support (co)-inductive and guarded types
- Implement primitive recursion and guarded recursion 
- Think of a module strategy
- Integrate with Haskell
- Write a demo (Pong or Pacman if crazy)
- Expand type-aliases in type annotations
- Parse (:) syntax for type annotations instead of `the (A) e`
- application-synthesis leaves solved existentials in context (as it must to curried functions)
  but this pollutes the context after the application. We'd probably need to treat application as
  "spines" to fix this..
- Clean up error messages
  - Remove most uses of `Other` in favor of semantic variants
  - Add ability to decorate errors
  - Add source-location to errors
  - Parsing and checking is pretty laissez faire with propagating and maintaining annotations, leading
    to possibly incorrect source-locations in errors
- Check data decls and type aliases for well-formedness before elaboration
- Is OK to re-assign an existential iff it is the same type we're attempting to assign?

## Type Aliases
- Right now, type alias expansion is kind of a mess tbh. Here is a maybe better algorithm:
  - Go through each alias, and "fixpoint" expand them
    - If an alias encounters itself in its expansion, its recursive so we fail
    - If not, every alias is expanded into its "most-expanded" (normal) form
  - After each alias is in normal form, go through each type (signatures and annotations in expressions)
    - We know the arity n of each alias, so we should be able to simply search for its name applied to n
      arguments
    - We can then substitute the arguments (after they've been expanded as well)for the bound variables in
      the alias definition and replace it directly into the AST.

## Recursive Types
- Is it really a good idea to expose the recursive primitives to the user?
- Do we need the parameter at all? E.g. we have Fix x. NatF x, but we could
  just have Fix NatF and still treat Fix as a special construct, but substitutions
  would just be one extra type application to its functor.
  - This also means we can check that the kind of the argument to fix is (* -> *)

[clott]: https://github.com/adamschoenemann/clott
