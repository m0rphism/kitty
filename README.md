# Kit Theory

The best way to traverse a kitty cat.

## Project Structure

- `KitTheory.Prelude` contains small helper like `_∋_` and `_,_`.
- `KitTheory.Modes` contains the records `Modes` and `Terms` over which all other modules are parameterized.
- `KitTheory.Kit` contains the records `Kit` and `KitTraversal` for renaming and substiution.
- `KitTheory.Compose` contains the records `ComposeKit`, `KitAssoc`, and `KitAssocLemmas` for composing renaming and substitution and dealing with identity.
- `KitTheory.Types` contains the record `KitType`, which given a lifting of term- to type-modes defines contexts, and `KitTypeSubst`, which given a `KitTraversal` provides substitution on contexts.
- `KitTheory.OPE` defines Order Preserving Embeddings (OPEs) and the `ope-preserves-telescope`-lemma.
- `KitTheory.Kit2` and `KitTheory.Compose2` use a single stronger lemma to derive everything (traversal are defined by how they behave on variables)
- `KitTheory.ITerms` and `KitTheory.IKit` are a WIP attempt to derive substitution lemmas for typing relations with regular structure (Γ ⊢ e ∶ t).
- `KitTheory.Generics` are a WIP attempt to implement substitution for a generic syntax datatype based on the paper "A Type and Scope Safe Universe of Syntaxes with Binding".




