# [Simply Typed Clocked Type Theory][clott]

For my master's thesis at ITU

## TODO
- Support higher-kinded types (should be not that hard)
  - Infer kind of tvar syntactically
  - Maintain the kind-info either in kind-ctx or annotate with kind in TyCtx ✓
- Check/infer lambdas with annotated type-params ✓
- Parse and desugar multi-param lambdas ✓
- Syntax sugar for
  - tuples ✓
  - units?
  - lists?
- Optimize type-checking in general
- Make sure everything is sane by checking context-wellformedness more and checking that no impredicativeness takes place
  - Note: Assigning an existential to a partially-applied type-constructor is fine
- Add the actual CloTT primitives and rules ✓
- Support (co)-inductive and guarded types
  - no syntax sugar yet but otherwise
- Implement primitive recursion and guarded recursion
  - typechecking ✓
  - evaluation
- Think of a module strategy
- Integrate with Haskell
- Write a demo (Pong or Pacman if crazy)
- Expand type-aliases in type annotations ✓
- Parse (:) syntax for type annotations instead of `the (A) e` ✓
- application-synthesis leaves solved existentials in context (as it must to curried functions)
  but this pollutes the context after the application. We'd probably need to treat application as
  "spines" to fix this..
- Clean up error messages
  - Remove most uses of `Other` in favor of semantic variants
  - Add ability to decorate errors ✓
  - Add source-location to errors
  - Parsing and checking is pretty laissez faire with propagating and maintaining annotations, leading
    to possibly incorrect source-locations in errors
- Check data decls and type aliases for well-formedness before elaboration
- Is OK to re-assign an existential iff it is the same type we're attempting to assign?
  - should never happen now since we maintain optimally-solved contexts
- Improve inference for "unfold"

## Type Aliases
- Right now, type alias expansion is kind of a mess tbh. Here is a maybe better algorithm:
  - Go through each alias, and "fixpoint" expand them
    - If an alias encounters itself in its expansion, its recursive so we fail
    - If not, every alias is expanded into its "most-expanded" (normal) form
  - After each alias is in normal form, go through each type (signatures and annotations in expressions)
    - We know the arity n of each alias, so we should be able to simply search for its name applied to n
      arguments
    - We can then substitute the arguments (after they've been expanded as well) for the bound variables in
      the alias definition and replace it directly into the AST.

## Recursive Types
- Is it really a good idea to expose the recursive primitives to the user?

## Impredicativity and the eta-law
In general, the inference system should preserve eta-equivalence, such that if
(λx. f x) : A then f : A. However, this is complicated by predicativity.

Consider a polymorphic function such as `f : () -> ∀a. a`. If we have `⊥ : ∀a. a`
then we can implement `f` as `f = ⊥`. But this will not type check, as we would
have to set `a = () -> ∀a. a`, which is an impredicative instantiation.
(sidenote: Haskell will actually allow this, even though it doesn't support impredicativity?)
However, we can typecheck `f` as `f = λx -> ⊥ x`, since that will allow us to introduce the
type-variable into scope first (call it `a'`), and we'll simply set `a = a'`. 
So this is an example where predicativity breaks the eta-rule.

Another example of the above problem is changing the type of `f` to the equivalent
`f' : ∀a. () -> a` by floating the positive quantifier left.
Then we have eta-equivalence. But since the types are equivalent,
we should have eta-equivalence for `f` as well...

Is this a general problem that you cannot have "full" eta-equivalence with predicative types? I know that it seems undecidable to have both eta-equivalence and impredicative types in SystemF, but since this system is predicative, I feel like I should have "full" eta-equivalence

## Type-classes and stuff
I generally want to avoid type-classes, as it is complicated to implement. However, I have a problem with fmap and primRec since they're
effectively overloaded functions. Type-classes can help model this elegantly. However, such a solution would require that the checking
procedure somehow annotated applications of polymorphic functions with their dictionaries/implementations. In any case, we need to look
up the type of a value at runtime to dispatch to fmap. We can hardcode this rule for fmap and map constructors to their types and
then to the fmap implementation, but it is a nasty hack for sure. Also, we cannot check at compile-time whether fmap/primRec is called
on a Fix type whose argument is in fact a functor or not...
I think we could generate constraints and keep them around. Then, when we substitute contexts we also substitute in constraints. The
question is when to solve these constraints? After checking, as a separate step? Local constraints will need to be discharged.
Or can we do it at other points safely? At subsumption?
Before checking? Should we solve a constraint everytime its argument is instantiated to a complete type (no existentials?)

Another solution is to mandate the user annotate uses of fmap/primRec with the type. This is probably the easy solution, but
it also makes me sad now that I've spent some time making these functions actually inferable.

```
fmap (+2) [1,2,3] <= [Int]
  [->E] (fmap (+2)) [1,2,3] <= [Int]
    [->E] fmap (+2) <= [Int] -> [Int]
      [Var] fmap => ∀f a b. Functor f => (a -> b) -> f a -> f b
      [AppI] (∀f a b. Functor f => (a -> b) -> f a -> f b) ̇∙ (+2) => ∃f Int -> ∃f Int, {Functor ∃f}
        [∀App]*3  
          [ConstraintApp] Functor f => (a -> b) -> f a -> f b) ̇∙ (+2) => ∃f Int -> ∃f Int, {Functor ∃f}
            [->App] (∃a -> ∃b) -> ∃f ∃a -> ∃f ∃b) ̇∙ (+2) => ∃f Int -> ∃f Int, {Functor ∃f}
              [→I] (λx -> x + 2) <= (∃a -> ∃b) -- solves a = Int, b = Int
    [->App] (∃f Int -> ∃f Int) ∙ [1,2,3]
      [->E] 1::2::3::[] <= ∃f Int
```

[clott]: https://github.com/adamschoenemann/clott
