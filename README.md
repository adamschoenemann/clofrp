# [clott][Simply Typed Clocked Type Theory]

For my master's thesis at ITU


[clott]: https://github.com/adamschoenemann/clott

## TODO
- Support higher-kinded types (should be not that hard)
- Check/infer lambdas with annotated type-params
- Parse and desugar multi-param lambdas
- Optimize type-checking in general
- Make sure everything is sane by checking context-wellformedness more and checking that no impredicativeness takes place
- Add the actual CloTT primitives and rules
- Support (co)-inductive and guarded types
- Implement primitive recursion and guarded recursion 
- Think of a module strategy
- Integrate with Haskell
- Write a demo (Pong or Pacman if crazy)

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
      