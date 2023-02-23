- ap/⋯ may need to work for general m/M, because we ne need laws involving id for Typing.Kit cases for
  type-preservation of terms like "clauses" which have no var-mode.
  
  Or at least this would allow us to use all properties for ap/⋯ and transfer them to ap AND ⋯.

- We could make a single Sub/Rename type that includes composition as a constructor, i.e.

        _·_ : ∀ ⦃ 𝕂₁ 𝕂₂ ⦄ ⦃ C : ComposeKit 𝕂₁ 𝕂₂ 𝕂 ⦄
              → µ₁ –[ 𝕂₁ ]→ µ₂
              → µ₂ –[ 𝕂₂ ]→ µ₃
              → µ₁ –[ 𝕂  ]→ µ₃

  Note that we could also do that generic over any kind of lattice instead of kits in particular for decoupling.
  Caveat: Would be Lattice + X, since x/t depends on Kit

- Alternatively maybe it would be good to define substitutions as `Star InnerSub` like to KitAltSimple.

- Should we make Context part of Term? `Ctx µ = µ ⊢ ℂ`
  Pro: can be easily traversed.
  Con: Ops and Laws need to be somehow derived + boilerplate.
  Alternative: Make Traversal somehow aware of external context.
  
- Make Context structure independent like Sub.
  This might also fix the previous point, as a Term-Context can be declared
  an instance afterwards. This instance could also be derived via reflection.

- Can we unify `_⋯_` and `_∘_` via yoneda lemma, i.e. by representing Terms as
  substitutions from a singleton context?
  - the `assoc` lemma will become real associativity - simply from the category
    instance.
  - `Term µ (m→M m)` would become `m ∷ [] –→ₛ µ`
  - `Term µ M` doesn't have a representation in general :(
    but we might be able to artificially add `VarMode`s for those terms, even though
    those variables cannot occur in `Terms`.
  - Maybe rethink the idea of `VarMode`s?
    - What problems do we avoid by having `Terms` without a corresponding `VarMode`?
      - `Term`s that only indirectly carry variables currently don't have a `VarMode`.
        If we give them a `VarMode`, then we also need to give them a `var`-constructor.
        Is there a way around this?
    - What useful scenarios can we model by having multiple `VarMode`s for the same term mode?
      - This allows to limit variable usage depending on the binding site. Is there a use case?

- Dependent Types
  - Types in Ctx are Values, which need to be weakened, either on insertion or
    on extraction (`wk-drop`).
  - Values don't support regular substitution. If we plug a `Value` into a
    `Neutral` we get a term, which only after evaluation becomes a `Value`
    again.
  - If we make one big syntactic category with modes for `Term`, `Value`, and
    `Neutral` stuff get's messy because a `Ctx` talks about `Term` variables not
    `Value` variables, and there's no suitable variable type in `Neutral` such
    that substitution works.
  - Either we need
    - some kind of heterogeneous substitution between `Term`, `Neutral` and
      `Value`; or
    - somehow integrate evaluation in substitution (allthough then substitution
      would still need to convert `Neutral` to `Value`); or
    - only use weakening on `Value`s
      - this should work since we can inject `Value`s into `Term`s, then
        substitute, and afterwards evaluate, which seems the only/most common
        scenario.
      - what does this imply for the theorems we need?
        will injection appear in equations?
        do we need lemmas between `Value`-weakening and `Term`-substitution?
      - can we split out renaming to work in a case where a `Neutral` term has a `Term` variable?
        or even provide a generalized substitution which works here, too?

- Generics

- Derive simple type preservation

- Alternative client-lemmas from agda-stdlib (`⋯-↑`)
  - We can derive our lemmas from `⋯-↑` - is the opposite also possible?

- Flesh out the substitution theory we want to derive (what are all the theorems of interest?)

- Investigate connection to semantics. In *syntax of universe and bindings* they have
  the `Semantics` type - what's that about precisely?

- Possible thesis structure:
  - Chapter 1 Motivate and specify the problem we want to solve, state
    contributions and show example usage of contributions
    - all the lemmas one wants to have, the use cases which motivate why we want to have them
  - Chapter 2 Introduce related work we build on
    - DeBruijn Indices
    - Kits
  - Chapter 3 Introduce our solution
  - Chapter 4 General related work
  - Chapter 5 Conclusion

  - unclear if general related work should be moved forward for further motivation.
    we could also structure by functionality and for each concept do:
    motivation, related work, our approach, conclusion
