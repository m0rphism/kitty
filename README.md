# Kit Theory

The best way to traverse a kitty cat.

## Project Structure

- `Kitty.Prelude` contains small helper like `_∋_` and `_,_`.
- `Kitty.Modes` contains the records `Modes` and `Terms` over which all other modules are parameterized.
- `Kitty.Kit` contains the records `Kit` and `KitTraversal` for renaming and substiution.
- `Kitty.Compose` contains the records `ComposeKit`, `KitAssoc`, and `KitAssocLemmas` for composing renaming and substitution and dealing with identity.
- `Kitty.Types` contains the record `KitType`, which given a lifting of term- to type-modes defines contexts, and `KitTypeSubst`, which given a `KitTraversal` provides substitution on contexts.
- `Kitty.OPE` defines Order Preserving Embeddings (OPEs) and the `ope-preserves-telescope`-lemma.
- `Kitty.Kit2` and `Kitty.Compose2` use a single stronger lemma to derive everything (traversal are defined by how they behave on variables)
- `Kitty.ITerms` and `Kitty.IKit` are a WIP attempt to derive substitution lemmas for typing relations with regular structure (Γ ⊢ e ∶ t).
- `Kitty.Generics` are a WIP attempt to implement substitution for a generic syntax datatype based on the paper "A Type and Scope Safe Universe of Syntaxes with Binding".




