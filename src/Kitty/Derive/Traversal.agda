{-# OPTIONS -vreflection-debug:10 #-}

module Kitty.Derive.Traversal where

module Deriving where
  open import Agda.Primitive using (Level; _⊔_) renaming (lzero to 0ℓ)
  open import Data.Bool using (Bool; true; false; if_then_else_)
  open import Data.Fin as Fin using (Fin; zero; suc)
  open import Data.List as List using (List; []; _∷_; _++_; length; drop; zip; reverse)
  open import Data.List.Membership.Propositional using (_∈_)
  open import Data.List.Properties using (++-assoc)
  open import Data.List.Relation.Unary.Any using (here; there)
  open import Data.Maybe using (Maybe; just; nothing)
  open import Data.Nat as Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
  open import Data.Product using (_×_; _,_; Σ; Σ-syntax; ∃-syntax; proj₁; proj₂)
  open import Data.String as String using (String)
  open import Data.Unit using (⊤; tt)
  open import Function using (_∘_; _$_; case_of_)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; trans; sym; subst₂; module ≡-Reasoning)
  open import Relation.Nullary using (Dec; yes; no)
  open ≡-Reasoning
  import Agda.Builtin.List

  open import ReflectionLib.Standard.Syntax
  open import ReflectionLib.Standard.VeryPretty
  open import ReflectionLib.Standard.ActionsClass hiding (term→name; ⟦_⟧)
  open import ReflectionLib.Classes.Pretty
  open import ReflectionLib.Named.Syntax
  open import ReflectionLib.Named.Actions
  open import ReflectionLib.Named.VeryPretty
  open import ReflectionLib.Named.FromStandard
  open import ReflectionLib.Named.ToStandard
  open import ReflectionLib.Named.Substitution
  open import ReflectionLib.Named.Rewrite
  open import ReflectionLib.Algorithms.Fin
  open import ReflectionLib.Algorithms.Nat
  open import ReflectionLib.Categorical

  open import Kitty.Term.Prelude using (_∋_)
  open import Kitty.Term.Modes
  import Kitty.Term.Kit
  import Kitty.Term.KitAltSimple
  open import Kitty.Util.Star using (Star; []; _∷_)
  open import Kitty.Derive.Common
  import Kitty.Term.Sub
  import Kitty.Term.MultiSub

  private variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ℓ' : Level
    A B C : Set ℓ

  open Modes using (Scoped)

  record VarCon (𝕄 : Modes) (_⊢_ : Scoped 𝕄) : Set where
    open Modes 𝕄
    field
      nm    : Name
      ctor` : Term' → Term'
      pat`  : Pattern' → Pattern'
      ctor  : ∀ {µ m} → µ ∋ m → µ ⊢ m→M m

    ctor-lam` : Term'
    ctor-lam` = lam visible (abs "x" (ctor` (var "x" [])))

  open VarCon

  get-var-con : (𝕄 : Modes) (_⊢_ : Scoped 𝕄) → Name → TC (VarCon 𝕄 _⊢_)
  get-var-con 𝕄 _⊢_ `-nm = do
    let open Modes 𝕄
    catchTC
      (do
        `_ ← unquoteTC' {A = ∀ {µ m} → µ ∋ m → µ ⊢ m→M m} (con `-nm [])
        pure record
          { nm = `-nm
          ; ctor` = λ x → con `-nm [ argᵥ x ]
          ; pat` = λ x → con `-nm [ argᵥ x ]
          ; ctor = λ {µ} → `_ {µ}
          }
      )
      (do
        `_ ← (unquoteTC' {A = ∀ {µ m} → µ ∋ m → µ ⊢ m→M m}
                         (lam hidden (abs "µ"
                         (lam hidden (abs "m"
                         (con `-nm [ argₕ (var "µ" [])
                                   ; argₕ (var "m" [])
                                   ; argᵥ (con (quote refl) [])
                                   ]))))))
        pure record
          { nm = `-nm
          ; ctor` = λ x → con `-nm [ argᵥ (con (quote refl) []) ; argᵥ x ]
          ; pat` = λ x → con `-nm [ argᵥ (con (quote refl) []) ; argᵥ x ]
          ; ctor = λ {µ} → `_ {µ}
          }
      )

  derive-Terms : (𝕄 : Modes) → (_⊢_ : Scoped 𝕄) → Name → TC ⊤
  derive-Terms 𝕄 _⊢_ terms-nm = runFreshT do
    let open Modes 𝕄
    𝕄-nm ← quoteNameTC 𝕄
    ⊢-nm ← quoteNameTC _⊢_
    ⊢-def ← getDefinition ⊢-nm
    `-nm , _ ← split-term-ctors (ctors ⊢-def)
    var-con ← liftTC $ get-var-con 𝕄 _⊢_ `-nm
    terms-ty ← quoteTC' (Terms 𝕄)
    -- terms-body ← quoteTC' (mkTerms _⊢_ (ctor var-con) `-injective)
    let `-injective = pat-lam [ clause [] [ argᵥ (con (quote refl) []) ] (con (quote refl) []) ] []
    let terms-body = def (quote mkTerms) [ argᵥ (def ⊢-nm []) ; argᵥ (ctor-lam` var-con) ; argᵥ `-injective ]
    -- let terms-ty = def (quote Terms) [ argᵥ (def 𝕄-nm []) ]
    -- let terms-body = def (quote mkTerms) [ argᵥ (def ⊢-nm []) ; argᵥ (con `-nm []) ] 
    defdecFun'
      (argᵥ terms-nm)
      terms-ty
      [ clause [] [] terms-body ]

  -- record DeriveContext : Set₁ where
  --   field
  --     𝕄 : Modes
  --     𝕋 : Terms 𝕄

  --     `𝕄 : Name
  --     `𝕋 : Name
  --     `⊢ : Name
  --     `VarMode : Name
  --     `TermMode : Name
  --     `Kit : Name
  --     `⋯ : Name

  --     `var : Name
  --     `cons : List Name
  --     con-tys : List Type'
  --     con-tels : List Telescope'

  --   open Modes 𝕄 public
  --   open Terms 𝕋 public
  --   open Kitty.Kit 𝕋 public

  derive-⋯ : {𝕄 : Modes} → Terms 𝕄 → Name → TC ⊤
  derive-⋯ {𝕄} 𝕋 ⋯-nm = runFreshT do
    let open Modes 𝕄
    let open Terms 𝕋
    let open Kitty.Term.Kit 𝕋
    let open Kitty.Term.Sub 𝕋
    let open Sub ⦃ … ⦄
    𝕄-nm ← quoteNameTC 𝕄
    ⊢-nm ← quoteNameTC _⊢_
    ⊢-def ← getDefinition ⊢-nm
    `-nm , con-nms ← split-term-ctors (ctors ⊢-def)
    var-con ← liftTC $ get-var-con 𝕄 _⊢_ `-nm
    𝕋-nm ← term→name =<< quoteTC' 𝕋
    VarMode` ← quoteNormTC' VarMode
    VarModes` ← quoteNormTC' (List VarMode)
    Kit` ← quoteTC' Kit
    Sub` ← quoteTC' Sub

    let mk-tel c-tel =
          [ "𝕊" , argᵢ Sub`
          ; "𝕂" , argᵢ Kit`
          ; "µ₁" , argₕ VarModes`
          ; "µ₂" , argₕ VarModes`
          ] ++ c-tel ++
          [ "f" , argᵥ (def (quote Kitty.Term.Sub.Sub._–[_]→_)
              [ argᵥ (var "𝕊" [])
              ; argᵥ (var "µ₁" [])
              ; argᵥ (var "𝕂" [])
              ; argᵥ (var "µ₂" [])
              ])
          ]
    let mk-pats c-pat = 
          [ argᵢ (var "𝕊")
          ; argᵢ (var "𝕂")
          ; argₕ (var "µ₁")
          ; argₕ (var "µ₂")
          ] ++ c-pat ∷
          [ argᵥ (var "f" ) ]

    clauses ← forM (enumerate con-nms) λ (i , c) → do
      -- Get constructor telescope
      c-ty ← getType' c
      let (c-tel , c-ret) = pi→tel c-ty

      -- Retrieve variable name used for `µ`
      c-µ ← case unterm ⊢-nm c-ret of λ where
        (just (var µ [] , M)) → pure µ
        (just (µ , M)) → liftTC $ failStr "constructed type has to return variable as µ."
        nothing → liftTC $ failStr "impossible"

      -- Rename `µ` binding and occurences to `µ₁`
      let c-tel' = List.map (λ { (x , b) → case x String.≟ c-µ of λ where
                                             (no _)  → (x , b [ c-µ ↦ var "µ₁" [] ])
                                             (yes _) → ("µ₁" , b)
                               }) c-tel

      -- Remove `µ₁` binding, since it's already bound on the outside
      let c-tel'x = List.boolFilter
            (λ { (x , _) → case x String.≟ "µ₁" of λ { (yes _) → false; (no _) → true } })
            c-tel'

      let c-tel'' = List.map (λ { (x , b) → case x String.≟ c-µ of λ where
                                              (no _)  → (x , b [ c-µ ↦ var "µ₂" [] ])
                                              (yes _) → ("µ₂" , b)
                                }) c-tel
      let c-pats = List.map (λ { (x , arg i _) → case x String.≟ c-µ of λ where
                                                   (no _)  → arg i (var x)
                                                   (yes _) → arg i (dot (var "µ₁" []))
                               }) c-tel'
      let c-pat = argᵥ (con c c-pats)
      let body = con c $ foldr' c-tel'' [] λ where
            (s , arg i t) c-args → _∷ c-args $ case unterm ⊢-nm t of λ where
              (just _) → arg i (def ⋯-nm [ argᵥ (var s [])
                                         ; argᵥ (def (quote Kitty.Term.MultiSub._↑*'_)
                                             [ argᵥ (def 𝕋-nm [])
                                             ; argᵥ (var "f" [])
                                             ; argᵥ unknown
                                             ])
                                         ]) 
              nothing  → case s String.≟ c-µ of λ where
                            (no _)  → arg i (var s [])
                            (yes _) → arg i (var "µ₂" [])
      pure $ clause (mk-tel c-tel'x) (mk-pats c-pat) body

    let var-tel = [ "x" , argᵥ (def (quote _∋_) [ argᵥ (var "µ₁" [])
                                                ; argᵥ unknown
                                                ])
                  ]
    let var-pat = argᵥ (pat` var-con (var "x"))
    let var-clause = clause (mk-tel var-tel)
                            (mk-pats var-pat)
                            (def (quote Kitty.Term.Kit.Kit.`/id)
                              [ argᵥ (var "𝕂" [])
                              ; argᵥ (def (quote Kitty.Term.Sub.Sub._&_) [ argᵥ (var "𝕊" [])
                                                                         ; argᵥ (var "x" [])
                                                                         ; argᵥ (var "f" [])
                                                                         ])
                              ])

    ⋯-ty ← quoteTC' (∀ ⦃ 𝕊 : Kitty.Term.Sub.Sub 𝕋 ⦄ ⦃ 𝕂 : Kitty.Term.Kit.Kit 𝕋 ⦄ {µ₁ µ₂} {M} → µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M)

    defdecFun'
      (argᵥ ⋯-nm)
      ⋯-ty
      (var-clause ∷ clauses)

  -- _⋯_ : ∀ {µ₁} {µ₂} {M} {{𝕂 : Kit}} → µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M
  -- (` x)     ⋯ f = `/id _ (f _ x)
  -- (λx t)    ⋯ f = λx (t ⋯ (f ↑* _))
  -- (t₁ · t₂) ⋯ f = _·_ (t₁ ⋯ f) (t₂ ⋯ f)
  -- (foo t)   ⋯ f = foo (t ⋯ (f ↑* _))

  derive-⋯-var : {𝕄 : Modes} → Terms 𝕄 → Name → Name → TC ⊤
  derive-⋯-var {𝕄} 𝕋 ⋯-nm ⋯-var-nm = runFreshT do
    let open Modes 𝕄
    let open Terms 𝕋
    let open Kitty.Term.Kit 𝕋
    let open Kitty.Term.Sub 𝕋
    let open Sub ⦃ … ⦄
    let open SubWithLaws ⦃ … ⦄

    𝕄-nm ← quoteNameTC 𝕄
    ⊢-nm ← quoteNameTC _⊢_
    ⊢-def ← getDefinition ⊢-nm
    `-nm , con-nms ← split-term-ctors (ctors ⊢-def)
    var-con ← liftTC $ get-var-con 𝕄 _⊢_ `-nm
    𝕋-nm ← term→name =<< quoteTC' 𝕋

    _⋯_ ← unquoteTC' {A = ∀ ⦃ 𝕊 : SubWithLaws ⦄ ⦃ 𝕂 : Kitty.Term.Kit.Kit 𝕋 ⦄ {µ₁ µ₂} {M} → µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M} (def ⋯-nm [])

    let body = lam visible (abs "x" (
               lam visible (abs "f" (
               con (quote refl) []))))
    ⋯-var-ty ← quoteTC' (∀ ⦃ 𝕊 : SubWithLaws ⦄ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {m} (x : µ₁ ∋ m) (f : µ₁ –[ 𝕂 ]→ µ₂)
                         → (ctor var-con x) ⋯ f ≡ Kit.`/id 𝕂 (x & f))
    defdecFun'
      (argᵥ ⋯-var-nm)
      ⋯-var-ty
      [ clause [] [] body ]

  -- ⋯-var : ∀ {{𝕂 : Kit}} {µ₁} {µ₂} {m} (x : µ₁ ∋ m) (f : µ₁ –→ µ₂) →
  --         (` x) ⋯ f ≡ `/id _ (f _ x)
  -- ⋯-var x f = refl

  -- Deriving n-ary cong ---------------------------------------------------------

  -- cong₂ : ∀ {a : Level} {A : Set a}
  --           {b : Level} {B : Set b}
  --           {c : Level} {C : Set c}
  --           (f : A → B → C)
  --           {x y : A}
  --           {u v : B}
  --         → x ≡ y
  --         → u ≡ v
  --         → f x u ≡ f y v
  -- cong₂ f refl refl = refl

  cong-n : ℕ → Name → FreshT TC ⊤
  cong-n n nm = do
    levels    ← fresh-ids n "ℓ"
    sets      ← fresh-ids n "A"
    out-level ← fresh-id "ℓ"
    out-set   ← fresh-id "A"
    let all-levels = levels ++ [ out-level ]
    let all-sets   = sets ++ [ out-set ]
    let level-tel  = map (λ ℓ → (ℓ , argₕ (def (quote Level) []))) all-levels
    let set-tel    = map (λ (ℓ , A) → (A , argₕ (agda-sort (set (var ℓ []))))) (zip all-levels all-sets)
    f ← fresh-id "f"
    let f-ty  = tel→pi (map (λ A → ("_" , argᵥ (var A []))) sets) (var out-set [])
    let f-tel = [ f , argᵥ f-ty ]
    args-x ← fresh-ids (length sets) "x"
    args-y ← fresh-ids (length sets) "y"
    let args-x-tel = map (λ (x , A) → (x , argₕ (var A []))) (zip args-x sets)
    let args-y-tel = map (λ (x , A) → (x , argₕ (var A []))) (zip args-y sets)
    let eq-tel = map
          (λ (x , y) → ("_", argᵥ (def (quote _≡_) [ argᵥ (var x []) ; argᵥ (var y []) ])))
          (zip args-x args-y)
    let eq-res = def (quote _≡_) [ argᵥ (var f (map (λ x → argᵥ (var x [])) args-x))
                                 ; argᵥ (var f (map (λ y → argᵥ (var y [])) args-y)) ]
    let tel = level-tel ++ set-tel ++ f-tel ++ args-x-tel ++ args-y-tel ++ eq-tel
    let cong-ty = tel→pi tel eq-res
    let cong-clause = clause
          (level-tel ++ set-tel ++ f-tel)
          (List.map (λ x → argₕ (var x)) all-levels ++
          List.map (λ x → argₕ (var x)) all-sets ++
          argᵥ (var f) ∷ List.map (λ _ → argᵥ (con (quote refl) [])) eq-tel)
          (con (quote refl) [])
    defdecFun' (argᵥ nm) cong-ty [ cong-clause ]

  tel→args : Telescope' → List (Arg Term')
  tel→args [] = []
  tel→args ((x , arg i t) ∷ tel) = arg i (var x []) ∷ tel→args tel

  µ→[]' : String → Term' → Term'
  µ→[]' `µ t₂ =
    let t₂ = rw (λ { ⦃ `Term ⦄ t → case un-++ t of λ where
                       (just (xs , var ys [])) → case `µ String.≟ ys of λ where
                                                   (yes _) → just xs
                                                   (no  _) → nothing
                       _                        → nothing
                   ; ⦃ T     ⦄ t → nothing
                   }) t₂
    in t₂ [ `µ ↦ con (quote List.List.[]) [] ]

  derive-⋯-↑-con : {𝕄 : Modes} → Terms 𝕄 → Name → Name → Name → TC ⊤
  derive-⋯-↑-con {𝕄} 𝕋 ⋯-nm con-nm ⋯-↑-con-nm = runFreshT do
    let open Modes 𝕄
    let open Terms 𝕋
    let open Kitty.Term.Kit 𝕋
    let open Kitty.Term.Prelude using (_▷▷_)
    let open Kitty.Term.KitAltSimple 𝕋
    let open Kitty.Term.Sub 𝕋
    let open Sub ⦃ … ⦄
    let open SubWithLaws ⦃ … ⦄

    𝕄-nm ← quoteNameTC 𝕄
    ⊢-nm ← quoteNameTC _⊢_
    ⊢-def ← getDefinition ⊢-nm
    `-nm , con-nms ← split-term-ctors (ctors ⊢-def)
    𝕋-nm ← term→name =<< quoteTC' 𝕋

    _⋯⊤_ ← unquoteTC' {A = ∀ (_ : ⊤) ⦃ 𝕊 : Sub ⦄ ⦃ 𝕂 : Kitty.Term.Kit.Kit 𝕋 ⦄ {µ₁ µ₂} {M} → µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M}
                      (lam visible (abs "_" (def ⋯-nm [])))
    let open Kitty.Term.MultiSub.TraversalOps' 𝕋 _⋯⊤_

    -- Get constructor telescope
    c-ty ← getType' con-nm
    let (c-tel , c-ret) = pi→tel c-ty

    -- Retrieve variable name used for `µ`
    c-µ ← case unterm ⊢-nm c-ret of λ where
      (just (var µ [] , M)) → pure µ
      (just (µ , M)) → liftTC $ failStr "constructed type has to return variable as µ."
      nothing → liftTC $ failStr "impossible"

    -- Rename `µ` to `µ₁` and replace `µ` occurences with `µ₁ ▷▷ µ₁'`
    let c-tel' = List.map (λ { (x , b) → case x String.≟ c-µ of λ where
                                            (no _)  → (x , b [ c-µ ↦ def (quote _▷▷_) [ argᵥ (var "µ₁" []) ; argᵥ (var "µ₁'" []) ] ])
                                            (yes _) → ("µ₁" , b)
                              }) c-tel

    -- Remove `µ₁` binding, since it's already bound on the outside
    let c-tel'x = List.boolFilter
          (λ { (x , _) → case x String.≟ "µ₁" of λ { (yes _) → false; (no _) → true } })
          c-tel'

    Kit` ← quoteTC' (Kitty.Term.Kit.Kit 𝕋)
    Kits` ← quoteTC' (List (Kitty.Term.Kit.Kit 𝕋))
    VarModes` ← quoteTC' (List VarMode)
    SubWithLaws` ← quoteTC' (Kitty.Term.Sub.SubWithLaws 𝕋)

    -- Convert tel bindings (x , t) to var arguments, but replace `µ₁` with `µ₁ ▷▷ µ₁'`
    let con-term = con con-nm $ List.map
                     (λ where (x , arg i _) → case x String.≟ "µ₁" of λ where
                                (yes _) → arg i (def (quote _▷▷_)
                                                     [ argᵥ (var "µ₁" [])
                                                     ; argᵥ (var "µ₁'" []) ])
                                (no _) → arg i (var x [])
                     )
                     c-tel'
    -- ((λx t) ⋯* (f ↑** µ₁')) ≡ λx (t ⋯* (f ↑** µ₁' ↑** [ 𝕖 ]))
    let _⋯*`_ = (Term' → Term' → Term') by
                  λ t fs → def (quote Kitty.Term.MultiSub.TraversalOps'._⋯*_)
                          [ argᵥ (def 𝕋-nm [])
                          ; argᵥ (lam visible (abs "_" (def ⋯-nm [])))
                          ; argᵥ t
                          ; argᵥ fs
                          ]
    let _↑**`_ = (Term' → Term' → Term') by
                  λ fs µ → def (quote Kitty.Term.MultiSub._↑**_)
                               [ argᵥ (def 𝕋-nm []) ; argᵥ fs ; argᵥ µ ]
    let lhs = con-term ⋯*` (var "fs" [] ↑**` var "µ₁'" [])
    let rhs = con con-nm $ List.map
                     (λ where (x , arg i t) → case x String.≟ c-µ of λ where
                                (yes _) → arg i (def (quote _▷▷_)
                                                     [ argᵥ (var "µ₂" [])
                                                     ; argᵥ (var "µ₁'" []) ])
                                (no _) → case unterm ⊢-nm t of λ where
                                           (just (µ , _)) → let µ' = µ→[]' c-µ µ in
                                                            arg i (var x [] ⋯*` ((var "fs" [] ↑**` var "µ₁'" []) ↑**` µ'))
                                           nothing        → arg i (var x [])
                     )
                     c-tel
    let ⋯-↑-con-ty = tel→pi
          ( [ ("𝕊"  , argᵢ SubWithLaws`)
            ; ("𝕂s"  , argₕ Kits`)
            ; ("µ₁"  , argₕ VarModes`) 
            ; ("µ₂"  , argₕ VarModes`) 
            ; ("µ₁'" , argₕ VarModes`)
            ; ("fs"  , argᵥ (def (quote Kitty.Term.MultiSub._–[_]→*_)
                            [ argᵥ (def 𝕋-nm []) ; argᵥ (var "µ₁" []) ; argᵥ (var "𝕂s" []) ; argᵥ (var "µ₂" []) ]))
            ] ++ c-tel'x)
          (def (quote _≡_) [ argᵥ lhs ; argᵥ rhs ])

    let mk-tel 𝕂s-binds fs-binds = Telescope' by
          ([ ("𝕊" , argᵢ SubWithLaws`) ] ++
           𝕂s-binds ++
           [ ("µ₁" , argₕ VarModes`)
           ; ("µ₂" , argₕ VarModes`)
           ; ("µ₁'" , argₕ VarModes`)
           ] ++
           fs-binds ++
           c-tel'x)
    let c-pats = List (Arg Pattern') by
                 List.map (λ { (x , arg i _) → arg i (var x) }) c-tel'x
    let mk-pats 𝕂s-pats fs-pats = List (Arg Pattern') by
          [ argᵢ (var "𝕊") ] ++
          𝕂s-pats ++
          [ argₕ (var "µ₁")
          ; argₕ (var "µ₂")
          ; argₕ (var "µ₁'")
          ] ++ fs-pats ++ c-pats

    -- ⋯-↑-λ : ∀ {𝕂s : List Kit} {µ₁ µ₂ µ₁'} (f : µ₁ –[ 𝕂s ]→* µ₂)
    --         → (t : (µ₁ ▷▷ µ₁' ▷ 𝕖) ⊢ 𝕖)
    --         → ((λx t) ⋯* (f ↑** µ₁')) ≡ λx (t ⋯* (f ↑** µ₁' ↑** [ 𝕖 ]))

    -- ⋯-↑-λ           []       t = refl
    let clause₁ = clause
          (mk-tel [] [])
          (mk-pats [ argₕ (con (quote Agda.Builtin.List.List.[]) []) ]
                   [ argᵥ (con (quote Kitty.Util.Star.Star.[]) []) ])
          (con (quote refl) [])

    let 𝕤 = def (quote Kitty.Term.Sub.SubWithLaws.SubWithLaws-Sub)
              [ argᵥ (var "𝕊" [])
              ]

    -- ⋯-↑-λ {𝕂s ▷ 𝕂} (f ∷ fs) t = cong₂ (_⋯_ ⦃ 𝕂 ⦄) (⋯-↑-λ fs t) refl
    let con-args = List.map
                     (λ where (x , arg i _) → arg i (var x []))
                     c-tel'x
    let rec = def ⋯-↑-con-nm ([ argᵥ (var "fs" []) ] ++ con-args)
    let clause₂ = clause
          (mk-tel [ ("𝕂" , argₕ Kit`) ; ("𝕂s" , argₕ Kits`) ]
                  [ ("µₓ" , argₕ VarModes`)
                  ; ("f" , argᵥ (def (quote Kitty.Term.Sub.Sub._–[_]→_)
                        [ argᵥ 𝕤
                        ; argᵥ (var "µₓ" []) ; argᵥ (var "𝕂" []) ; argᵥ (var "µ₂" []) ]))
                  ; ("fs" , argᵥ (def (quote Kitty.Term.MultiSub._–[_]→*_)
                        [ argᵥ (def 𝕋-nm [])
                        ; argᵥ (var "µ₁" []) ; argᵥ (var "𝕂s" []) ; argᵥ (var "µₓ" []) ]))
                  ])
          (mk-pats [ argₕ (con (quote Agda.Builtin.List.List._∷_) [ argᵥ (var "𝕂") ; argᵥ (var "𝕂s") ]) ]
                   [ argᵥ (con (quote Kitty.Util.Star._∷_) [ argₕ (dot (var "µ₂" []))
                                                           ; argₕ (var "µₓ")
                                                           ; argₕ (dot (var "µ₁" []))
                                                           ; argᵥ (var "f") ; argᵥ (var "fs") ])
                   ])
          (def (quote cong₂)
            [ argᵥ (def ⋯-nm [ argᵢ 𝕤 ; argᵢ (var "𝕂" []) ])
            ; argᵥ rec
            ; argᵥ (con (quote refl) [])
            ])

    defdecFun'
      (argᵥ ⋯-↑-con-nm)
      ⋯-↑-con-ty
      [ clause₁ ; clause₂ ]

  derive-⋯-↑ : {𝕄 : Modes} → Terms 𝕄 → Name → Name → TC ⊤
  derive-⋯-↑ {𝕄} 𝕋 ⋯-nm ⋯-↑-nm = runFreshT do
    let open Modes 𝕄
    let open Terms 𝕋
    let open Kitty.Term.Kit 𝕋
    let open Kitty.Term.Prelude using (_▷▷_)
    let open Kitty.Term.KitAltSimple 𝕋
    let open Kitty.Term.Sub 𝕋
    let open Kitty.Term.MultiSub 𝕋
    let open Sub ⦃ … ⦄
    let open SubWithLaws ⦃ … ⦄

    𝕄-nm ← quoteNameTC 𝕄
    ⊢-nm ← quoteNameTC _⊢_
    ⊢-def ← getDefinition ⊢-nm
    `-nm , con-nms ← split-term-ctors (ctors ⊢-def)
    var-con ← liftTC $ get-var-con 𝕄 _⊢_ `-nm
    𝕋-nm ← term→name =<< quoteTC' 𝕋

    Kit` ← quoteTC' (Kitty.Term.Kit.Kit 𝕋)
    Kits` ← quoteTC' (List (Kitty.Term.Kit.Kit 𝕋))
    VarModes` ← quoteTC' (List VarMode)
    SubWithLaws` ← quoteTC' (Kitty.Term.Sub.SubWithLaws 𝕋)

    _⋯_ ← unquoteTC' {A = ∀ ⦃ 𝕊 : Kitty.Term.Sub.Sub 𝕋 ⦄ ⦃ 𝕂 : Kitty.Term.Kit.Kit 𝕋 ⦄ {µ₁ µ₂} {M} → µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M} (def ⋯-nm [])
    _⋯⊤_ ← unquoteTC' {A = ∀ (_ : ⊤) ⦃ 𝕊 : Kitty.Term.Sub.Sub 𝕋 ⦄ ⦃ 𝕂 : Kitty.Term.Kit.Kit 𝕋 ⦄ {µ₁ µ₂} {M} → µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M} (lam visible (abs "_" (def ⋯-nm [])))

    let open Kitty.Term.MultiSub.TraversalOps' 𝕋 _⋯⊤_

    let mk-tel c-tel =
          [ "𝕊" , argᵢ SubWithLaws`
          ; "𝕂s₁" , argₕ Kits`
          ; "𝕂s₂" , argₕ Kits`
          ; "µ₁" , argₕ VarModes`
          ; "µ₂" , argₕ VarModes`
          ; "fs" , argᵥ (def (quote Kitty.Term.MultiSub._–[_]→*_)
              [ argᵥ (def 𝕋-nm [])
              ; argᵥ (var "µ₁" [])
              ; argᵥ (var "𝕂s₁" [])
              ; argᵥ (var "µ₂" [])
              ])
          ; "gs" , argᵥ (def (quote Kitty.Term.MultiSub._–[_]→*_)
              [ argᵥ (def 𝕋-nm [])
              ; argᵥ (var "µ₁" [])
              ; argᵥ (var "𝕂s₂" [])
              ; argᵥ (var "µ₂" [])
              ])
          ; "fs≈gs" , argᵥ (def (quote Kitty.Term.MultiSub.TraversalOps'._≈ₓ_)
              [ argᵥ (def 𝕋-nm [])
              ; argᵥ (lam visible (abs "_" (def ⋯-nm [])))
              ; argᵥ (var "fs" [])
              ; argᵥ (var "gs" [])
              ])
          ; "µ₁'" , argₕ VarModes`
          ] ++ c-tel
    let mk-pats c-pat = 
          [ argᵢ (var "𝕊")
          ; argₕ (var "𝕂s₁")
          ; argₕ (var "𝕂s₂")
          ; argₕ (var "µ₁")
          ; argₕ (var "µ₂")
          ; argᵥ (var "fs" )
          ; argᵥ (var "gs" )
          ; argᵥ (var "fs≈gs" )
          ; argₕ (var "µ₁'")
          ] ++ c-pat ∷ []

    non-var-clauses ← forM (enumerate con-nms) λ (i , c) → do
      ⋯-↑-con-nm ← freshName "⋯-↑-con"
      liftTC (derive-⋯-↑-con 𝕋 ⋯-nm c ⋯-↑-con-nm)

      -- Get constructor telescope
      c-ty ← getType' c
      let (c-tel , c-ret) = pi→tel c-ty

      -- Retrieve variable name used for `µ`
      c-µ ← case unterm ⊢-nm c-ret of λ where
        (just (var µ [] , M)) → pure µ
        (just (µ , M)) → liftTC $ failStr "constructed type has to return variable as µ."
        nothing → liftTC $ failStr "impossible"

      -- Rename `µ` to `µ₁` and replace `µ` occurences with `µ₁ ▷▷ µ₁'`
      let c-tel' = List.map (λ { (x , b) → case x String.≟ c-µ of λ where
                                              (no _)  → (x , b [ c-µ ↦ def (quote _▷▷_) [ argᵥ (var "µ₁" []) ; argᵥ (var "µ₁'" []) ] ])
                                              (yes _) → ("µ₁" , b)
                                }) c-tel

      -- Remove `µ₁` binding, since it's already bound on the outside
      let c-tel'x = List.boolFilter
            (λ { (x , _) → case x String.≟ "µ₁" of λ { (yes _) → false; (no _) → true } })
            c-tel'

      -- Convert tel bindings (x , t) to var patterns, but replace `µ₁` with `µ₁ ▷▷ µ₁'`
      let c-pats = List.map (λ { (x , arg i _) → case x String.≟ c-µ of λ where
                                                   (no _)  → arg i (var x)
                                                   (yes _) → arg i (dot (def (quote _▷▷_)
                                                      [ argᵥ (var "µ₁" [])
                                                      ; argᵥ (var "µ₁'" []) ]))
                               }) c-tel
      let c-pat = argᵥ (con c c-pats)


      let ⋯-↑-con` = (Term' → Term' → Term') by λ 𝕂s fs →
            def ⋯-↑-con-nm
              ([ argₕ 𝕂s
               ; argₕ (var "µ₁" [])
               ; argₕ (var "µ₂" [])
               ; argₕ (var "µ₁'" [])
               ; argᵥ fs
               ] ++ List.map (λ { (x , arg i t) → arg i (var x []) }) c-tel'x)
      let sym` = (Term' → Term') by λ eq → def (quote sym) [ argᵥ eq ]
      let trans` = (Term' → Term' → Term') by λ eq₁ eq₂ → def (quote trans) [ argᵥ eq₁ ; argᵥ eq₂ ]
      let 𝕂s₁` = Term' by (var "𝕂s₁" [])
      let 𝕂s₂` = Term' by (var "𝕂s₂" [])
      let fs` = Term' by (var "fs" [])
      let gs` = Term' by (var "gs" [])
      let µ₁'` = Term' by (var "µ₁'" [])
      let fs≈gs` = Term' by (var "fs≈gs" [])
      let cong` = (Term' → Term' → Term') by λ f eq → def (quote cong) [ argᵥ f ; argᵥ eq ]
      let _⋯*`_ = (Term' → Term' → Term') by
                    λ t fs → def (quote Kitty.Term.MultiSub.TraversalOps'._⋯*_)
                            [ argᵥ (def 𝕋-nm [])
                            ; argᵥ (lam visible (abs "_" (def ⋯-nm [])))
                            ; argᵥ t
                            ; argᵥ fs
                            ]
      let _↑**`_ = (Term' → Term' → Term') by
                    λ fs µ → def (quote Kitty.Term.MultiSub._↑**_)
                                [ argᵥ (def 𝕋-nm []) ; argᵥ fs ; argᵥ µ ]
      let ⋯-↑` = (Term' → Term' → Term' → Term' → Term') by λ fs gs fs≈gs t →
                 def ⋯-↑-nm [ argᵥ fs ; argᵥ gs ; argᵥ fs≈gs ; argᵥ t ]
      let ≈↑**` = (Term' → Term' → Term' → Term') by λ fs gs fs≈gs →
                 def (quote Kitty.Term.MultiSub.TraversalOps'.≈↑**)
                     [ argᵥ (def 𝕋-nm [])
                     ; argᵥ (lam visible (abs "_" (def ⋯-nm [])))
                     ; argᵥ fs ; argᵥ gs ; argᵥ fs≈gs
                     ]

      let rec = (Term' → Term') by λ t →
            ⋯-↑` (fs` ↑**` µ₁'`) (gs` ↑**` µ₁'`) (≈↑**` fs` gs` fs≈gs`) t

      let tel-rec , tel-non-rec = splitRec c-tel ⊢-nm
      let rec-ids = map proj₁ tel-rec
      let non-rec-ids = map proj₁ tel-non-rec
      cong-name ← freshName "cong-n"
      cong-n (length rec-ids) cong-name
      let cong-fun = tel→lam tel-rec $ con c $
                      List.map (λ{ (x , arg i t) → case x String.≟ c-µ of λ where
                                      (no _)  → arg i (var x [])
                                      (yes _) → arg i (def (quote _▷▷_)
                                                        [ argᵥ (var "µ₂" [])
                                                        ; argᵥ (var "µ₁'" []) ])
                                 }) c-tel

      let eqq = def cong-name (argᵥ cong-fun ∷ List.map (λ x → argᵥ (rec (var x []))) rec-ids)

      let body = trans` (⋯-↑-con` 𝕂s₁` fs`) (
                 trans` eqq
                        (sym` (⋯-↑-con` 𝕂s₂` gs`)))

      pure $ clause
        (mk-tel c-tel'x)
        (mk-pats c-pat)
        body

    ⋯-↑-ty ← quoteTC' (
        ∀ ⦃ 𝕊 : SubWithLaws ⦄ {𝕂s₁ 𝕂s₂ : List Kit} {µ₁} {µ₂} (f : µ₁ –[ 𝕂s₁ ]→* µ₂) (g : µ₁ –[ 𝕂s₂ ]→* µ₂) →
          f ≈ₓ g → f ≈ₜ g
      )

    let var-clause = clause
          (mk-tel [ "x" , argᵥ (def (quote _∋_) [ argᵥ (def (quote List._++_)
                                                         [ argᵥ (var "µ₁'" [])
                                                         ; argᵥ (var "µ₁" [])
                                                         ])
                                                ; argᵥ unknown
                                                ])
                  ])
          (mk-pats (argᵥ (pat` var-con (var "x"))))
          (var "fs≈gs" [ argᵥ (var "x" []) ])

    defdecFun'
      (argᵥ ⋯-↑-nm)
      ⋯-↑-ty
      (var-clause ∷ non-var-clauses)

  derive-KitTraversalAlt : {𝕄 : Modes} → Terms 𝕄 → Name → Name → Name → Name → TC ⊤
  derive-KitTraversalAlt {𝕄} 𝕋 ⋯-nm ⋯-var-nm ⋯-↑-nm kit-traversal-nm = runFreshT do
    𝕋-nm ← term→name =<< quoteTC' 𝕋
    let body =
          con (quote Kitty.Term.KitAltSimple.mkKitTraversalAlt)
            [ argᵥ (def ⋯-nm [])
            ; argᵥ (def ⋯-var-nm [])
            ; argᵥ (def ⋯-↑-nm [])
            ]
    defdecFun'
      (argᵥ kit-traversal-nm)
      (def (quote Kitty.Term.KitAltSimple.KitTraversalAlt) [ argᵥ (def 𝕋-nm []) ])
      [ clause [] [] body ]

  derive-traversal : (𝕄 : Modes) → (_⊢_ : Scoped 𝕄) → Name → TC ⊤
  derive-traversal 𝕄 _⊢_ traversal-nm = do
    liftTC $ printStr "Deriving Terms"
    terms-nm ← freshName "terms"
    derive-Terms 𝕄 _⊢_ terms-nm
    terms ← unquoteTC {A = Terms 𝕄} (def terms-nm [])

    liftTC $ printStr "Deriving ⋯"
    ⋯-nm ← freshName "⋯"
    derive-⋯ terms ⋯-nm

    liftTC $ printStr "Deriving ⋯-var"
    ⋯-var-nm ← freshName "⋯-var"
    derive-⋯-var terms ⋯-nm ⋯-var-nm

    liftTC $ printStr "Deriving ⋯-↑"
    ⋯-↑-nm ← freshName "⋯-↑"
    derive-⋯-↑ terms ⋯-nm ⋯-↑-nm

    derive-KitTraversalAlt terms ⋯-nm ⋯-var-nm ⋯-↑-nm traversal-nm


  module Derived {𝕄 : Modes} {𝕋 : Terms 𝕄} (T : Kitty.Term.KitAltSimple.KitTraversalAlt 𝕋) where
    import Kitty.Term.KitAltSimple
    open Kitty.Term.KitAltSimple.Derive _ T public

open Deriving using  (module Derived; derive-traversal) public 
open Deriving hiding (module Derived; derive-traversal) 

module Example where
  open import Kitty.Term.Prelude
  open import Kitty.Term.Modes
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; trans; sym; subst₂; module ≡-Reasoning)
  open ≡-Reasoning
  open import ReflectionLib.Categorical

  data Modeᵥ : Set where 𝕖 : Modeᵥ
  data Modeₜ : Set where 𝕖 : Modeₜ

  m→M : Modeᵥ → Modeₜ
  m→M 𝕖 = 𝕖

  𝕄 : Modes
  𝕄 = record { VarMode = Modeᵥ ; TermMode = Modeₜ ; m→M = m→M }

  infix  30 `_
  infixl 20 _·_
  infixr 10 λx_

  data _⊢_ : List Modeᵥ → Modeₜ → Set where
    `_    : ∀ {µ m}  →  µ ∋ m  →  µ ⊢ m→M m
    λx_   : ∀ {µ}  →  (µ ▷ 𝕖) ⊢ 𝕖  →  µ ⊢ 𝕖
    _·_   : ∀ {µ}  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖
    foo   : ∀ {µ µ'}  →  (µ ▷▷ µ') ⊢ 𝕖  →  µ ⊢ 𝕖

  module Manual where
    terms : Terms 𝕄
    terms = record { _⊢_ = _⊢_ ; `_ = `_ ; `-injective = λ { refl → refl } }

    open import Kitty.Term.Sub terms
    open import Kitty.Term.MultiSub terms
    open import Kitty.Term.KitAltSimple terms
    open import Kitty.Term.Kit terms
    open import Kitty.Util.Star
    open Kit ⦃ ... ⦄
    open Sub ⦃ ... ⦄
    open SubWithLaws ⦃ ... ⦄

    _⋯_ : ∀ ⦃ 𝕂 : Kit ⦄ ⦃ 𝕊 : Sub ⦄ {µ₁} {µ₂} {M} → µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M
    (` x)     ⋯ f = `/id (x & f)
    (λx t)    ⋯ f = λx (t ⋯ (f ↑*' _))
    (t₁ · t₂) ⋯ f = _·_ (t₁ ⋯ f) (t₂ ⋯ f)
    (foo t)   ⋯ f = foo (t ⋯ (f ↑*' _))

    ⋯-var : ∀ ⦃ 𝕊 : SubWithLaws ⦄ {{𝕂 : Kit}} {µ₁} {µ₂} {m} (x : µ₁ ∋ m) (f : µ₁ –→ µ₂) →
            (` x) ⋯ f ≡ `/id (x & f)
    ⋯-var x f = refl

    open TraversalOps _⋯_

    ⋯-↑-· : ∀ ⦃ 𝕊 : SubWithLaws ⦄ {𝕂s : List Kit} {µ₁ µ₂ µ₁'} (f : µ₁ –[ 𝕂s ]→* µ₂)
            → (t₁ t₂ : (µ₁ ▷▷ µ₁') ⊢ 𝕖)
            → ((t₁ · t₂) ⋯* (f ↑** µ₁')) ≡ (t₁ ⋯* (f ↑** µ₁' ↑** [])) · (t₂ ⋯* (f ↑** µ₁' ↑** []))
    ⋯-↑-· {.[]}     []       t₁ t₂ = refl
    ⋯-↑-· {𝕂 ∷ 𝕂s} (f ∷ fs) t₁ t₂ = cong₂ (_⋯_ ⦃ 𝕂 ⦄) (⋯-↑-· fs t₁ t₂) refl

    ⋯-↑-λ : ∀ ⦃ 𝕊 : SubWithLaws ⦄ {𝕂s : List Kit} {µ₁ µ₂ µ₁'} (f : µ₁ –[ 𝕂s ]→* µ₂)
            → (t : (µ₁ ▷▷ µ₁' ▷ 𝕖) ⊢ 𝕖)
            → ((λx t) ⋯* (f ↑** µ₁')) ≡ λx (t ⋯* (f ↑** µ₁' ↑** [ 𝕖 ]))
    ⋯-↑-λ           []       t = refl
    ⋯-↑-λ {𝕂s ▷ 𝕂} (f ∷ fs) t = cong₂ (_⋯_ ⦃ 𝕂 ⦄) (⋯-↑-λ fs t) refl

    ⋯-↑-foo : ∀ ⦃ 𝕊 : SubWithLaws ⦄ {𝕂s : List Kit} {µ₁ µ₂ µ₁' µ} (f : µ₁ –[ 𝕂s ]→* µ₂)
             → (t : (µ₁ ▷▷ µ₁' ▷▷ µ) ⊢ 𝕖)
             → (foo {µ' = µ} t) ⋯* (f ↑** µ₁')
             ≡ foo {µ' = µ} (t ⋯* ((f ↑** µ₁') ↑** µ))
    ⋯-↑-foo {.[]}     []       t = refl
    ⋯-↑-foo {𝕂s ▷ 𝕂} (f ∷ fs) t = cong₂ (_⋯_ ⦃ 𝕂 ⦄) (⋯-↑-foo fs t) refl

    -- TODO: does it still work if we pull out the µ₁'?
    ⋯-↑ : ∀ ⦃ 𝕊 : SubWithLaws ⦄ {𝕂s₁ 𝕂s₂ : List Kit} {µ₁ µ₂ } (f : µ₁ –[ 𝕂s₁ ]→* µ₂) (g : µ₁ –[ 𝕂s₂ ]→* µ₂)
          → f ≈ₓ g → f ≈ₜ g
    ⋯-↑ f g f≈g (` x) = f≈g x
    ⋯-↑ f g f≈g {µ₁' = µ₁'} (λx t) =
      (λx t) ⋯* (f ↑** µ₁')           ≡⟨ ⋯-↑-λ f t ⟩
      λx (t ⋯* (f ↑** µ₁' ↑** [ 𝕖 ])) ≡⟨ cong λx_ (⋯-↑ (f ↑** µ₁') (g ↑** µ₁') (≈↑** f g f≈g) t) ⟩
      λx (t ⋯* (g ↑** µ₁' ↑** [ 𝕖 ])) ≡⟨ sym (⋯-↑-λ g t) ⟩
      (λx t) ⋯* (g ↑** µ₁')           ∎
    ⋯-↑ f g f≈g {µ₁' = µ₁'} (t₁ · t₂) =
      (t₁ · t₂) ⋯* (f ↑** µ₁')                                ≡⟨ ⋯-↑-· f t₁ t₂ ⟩
      (t₁ ⋯* (f ↑** µ₁' ↑** [])) · (t₂ ⋯* (f ↑** µ₁' ↑** [])) ≡⟨ cong₂ _·_ (⋯-↑ (f ↑** µ₁') (g ↑** µ₁') (≈↑** f g f≈g) t₁)
                                                                           (⋯-↑ (f ↑** µ₁') (g ↑** µ₁') (≈↑** f g f≈g) t₂) ⟩
      (t₁ ⋯* (g ↑** µ₁' ↑** [])) · (t₂ ⋯* (g ↑** µ₁' ↑** [])) ≡⟨ sym (⋯-↑-· g t₁ t₂) ⟩
      (t₁ · t₂) ⋯* (g ↑** µ₁')                                ∎
    ⋯-↑ {𝕂s₁} {𝕂s₂} {µ₁ = µ₁} {µ₂ = µ₂} f g f≈g {µ₁' = µ₁'} (foo {µ' = µ} t) =
      foo t ⋯* (f ↑** µ₁')                  ≡⟨ ⋯-↑-foo f t ⟩
      foo {µ' = µ} (t ⋯* (f ↑** µ₁' ↑** µ)) ≡⟨ cong foo (⋯-↑ (f ↑** µ₁') (g ↑** µ₁') (≈↑** f g f≈g) t) ⟩
      foo {µ' = µ} (t ⋯* (g ↑** µ₁' ↑** µ)) ≡⟨ sym (⋯-↑-foo g t) ⟩
      foo t ⋯* (g ↑** µ₁')                  ∎

    kit-traversal-alt : KitTraversalAlt
    kit-traversal-alt = mkKitTraversalAlt _⋯_ ⋯-var ⋯-↑

    open Derived kit-traversal-alt

  module Half-Derived where
    unquoteDecl terms = derive-Terms 𝕄 _⊢_ terms
    unquoteDecl _⋯_   = derive-⋯ terms _⋯_
    unquoteDecl ⋯-var = derive-⋯-var terms (quote _⋯_) ⋯-var
    unquoteDecl ⋯-↑   = derive-⋯-↑ terms (quote _⋯_) ⋯-↑

    -- Tests
    open import Data.List.Relation.Unary.Any using (here; there)
    open import Kitty.Term.KitAltSimple terms
    open import Kitty.Term.Kit terms
    open import Kitty.Term.Sub terms
    open import Kitty.Term.MultiSub terms
    open Kit ⦃ … ⦄
    open Sub ⦃ … ⦄
    open SubWithLaws ⦃ … ⦄
    open TraversalOps _⋯_

    _⋯'_ : ∀ ⦃ 𝕊 : Sub ⦄ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {M} → µ₁ ⊢ M → µ₁ –[ 𝕂 ]→ µ₂ → µ₂ ⊢ M
    _⋯'_ = _⋯_

    ⋯-var' : ∀ ⦃ 𝕊 : SubWithLaws ⦄ ⦃ 𝕂 : Kit ⦄ {µ₁} {µ₂} {m} (x : µ₁ ∋ m) (f : µ₁ –→ µ₂) →
            (` x) ⋯ f ≡ `/id (x & f)
    ⋯-var' = ⋯-var

    ⋯-↑' : ∀ ⦃ 𝕊 : SubWithLaws ⦄ {𝕂s₁ 𝕂s₂ : List Kit} {µ₁ µ₂} (f : µ₁ –[ 𝕂s₁ ]→* µ₂) (g : µ₁ –[ 𝕂s₂ ]→* µ₂)
          → f ≈ₓ g → f ≈ₜ g
    ⋯-↑' = ⋯-↑

    kit-traversal-alt : KitTraversalAlt
    kit-traversal-alt = mkKitTraversalAlt _⋯_ ⋯-var ⋯-↑

    open Derived kit-traversal-alt hiding (_⋯_; ⋯-var; ⋯-↑)
    open Sub-Functional

    `id : [] ⊢ 𝕖
    `id = λx ` here refl

    `f : [ 𝕖 ] ⊢ 𝕖
    `f = λx (` here refl) · (` there (here refl))

    `f' : [] ⊢ 𝕖
    `f' = `f ⋯ ⦅ `id ⦆ₛ

    test-`f' : `f' ≡ λx (` here refl) · (λx ` here refl)
    test-`f' = refl

  module Derived' where
    unquoteDecl traversal = derive-traversal 𝕄 _⊢_ traversal
    open Derived traversal
    open Sub-Functional

    open import Data.List.Relation.Unary.Any using (here; there)

    `id : [] ⊢ 𝕖
    `id = λx ` here refl

    `f : [ 𝕖 ] ⊢ 𝕖
    `f = λx (` here refl) · (` there (here refl))

    `f' : [] ⊢ 𝕖
    `f' = `f ⋯ ⦅ `id ⦆ₛ

    test-`f' : `f' ≡ λx (` here refl) · (λx ` here refl)
    test-`f' = refl

module ExampleVarEq where
  open import Kitty.Term.Prelude
  open import Kitty.Term.Modes
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; trans; sym; subst₂; module ≡-Reasoning)
  open ≡-Reasoning
  open import ReflectionLib.Categorical

  data Modeᵥ : Set where 𝕖 : Modeᵥ
  data Modeₜ : Set where 𝕖 : Modeₜ

  m→M : Modeᵥ → Modeₜ
  m→M 𝕖 = 𝕖

  𝕄 : Modes
  𝕄 = record { VarMode = Modeᵥ ; TermMode = Modeₜ ; m→M = m→M }

  infix  30 `[_]_
  infixl 20 _·_
  infixr 10 λx_

  data _⊢_ : List Modeᵥ → Modeₜ → Set where
    `[_]_ : ∀ {µ m M}  →  m→M m ≡ M  →  µ ∋ m  →  µ ⊢ M
    λx_   : ∀ {µ}  →  (µ ▷ 𝕖) ⊢ 𝕖  →  µ ⊢ 𝕖
    _·_   : ∀ {µ}  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖  →  µ ⊢ 𝕖
    foo   : ∀ {µ µ'}  →  (µ ▷▷ µ') ⊢ 𝕖  →  µ ⊢ 𝕖

  module Derived' where
    unquoteDecl traversal = derive-traversal 𝕄 _⊢_ traversal
    open Derived traversal

