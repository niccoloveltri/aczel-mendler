{-# OPTIONS --cubical #-}

module Utilities where

open import Cubical.Foundations.Everything
open import Cubical.HITs.SetQuotients

-- ==============================================

{- PRELIMINARIES -}

-- Prop-valued relations 
isPropRel : ∀{ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} (R : A → B → Type ℓ'') → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
isPropRel R = ∀ a b → isProp (R a b)

-- Reflexive relations
isReflRel : ∀{ℓ ℓ'} {A : Type ℓ} (R : A → A → Type ℓ') → Type (ℓ-max ℓ ℓ')
isReflRel R = ∀ a → R a a

-- Equivalent relations give equivalent set quotients
module EquivQuot {ℓ ℓʳ ℓˢ : Level}
                (A : Type ℓ)
                (R : A → A → Type ℓʳ)
                (S : A → A → Type ℓˢ) 
                (R≃S : ∀ x y → R x y ≃ S x y) where

  changeQuot : A / R → A / S
  changeQuot =
    rec squash/
        [_]
        λ x y r → eq/ x y (equivFun (R≃S x y) r)

  changeQuotEq : Path (A → A / S) [_] (changeQuot ∘ [_])
  changeQuotEq = refl
  
-- Iterated set quotients
module IterQuot {ℓ ℓʳ ℓˢ : Level}
                (A : Type ℓ)
                (R : A → A → Type ℓʳ)
                (S : A / R → A / R → Type ℓˢ)
                (isReflS : ∀ x → S x x) where

  S∘R : A → A → Type ℓˢ
  S∘R x y = S [ x ] [ y ]

  collapse/ : (A / R) / S → A / S∘R
  collapse/ =
    rec squash/
        (rec squash/ [_] (λ x y r → eq/ x y (subst (S [ x ]) (eq/ x y r) (isReflS _))))
        (elimProp2 (λ _ _ → isPropΠ λ _ → squash/ _ _) eq/)

  expand/ : A / S∘R → (A / R) / S
  expand/ = rec squash/ ([_] ∘ [_]) (λ x y → eq/ [ x ] [ y ])

  collapse/-iso : Iso ((A / R) / S) (A / S∘R)
  Iso.fun collapse/-iso = collapse/
  Iso.inv collapse/-iso = expand/
  Iso.rightInv collapse/-iso = elimProp (λ _ → squash/ _ _) (λ _ → refl)
  Iso.leftInv collapse/-iso = elimProp (λ _ → squash/ _ _) (elimProp (λ _ → squash/ _ _) (λ _ → refl))


-- Propositional resizing (Def. 2.4 of de Jong & Escardó "On small types in univalent foundations")
PropRes : (ℓS ℓL : Level) → Type (ℓ-max (ℓ-suc ℓS) (ℓ-suc ℓL))
PropRes ℓS ℓL = (P : Type ℓL) → isProp P → Σ[ Q ∈ Type ℓS ] P ≃ Q

-- Functors

record SemiFunctor : Typeω where
  field
    F : ∀ {ℓ} → Type ℓ → Type ℓ
    map : ∀{ℓ ℓ'}{X : Type ℓ}{Y : Type ℓ'} (f : X → Y) → F X → F Y
    map∘ : ∀{ℓ ℓ' ℓ''}{X : Type ℓ}{Y : Type ℓ'}{Z : Type ℓ''}
      → {g : Y → Z} {f : X → Y} (x : F X)
      → map (g ∘ f) x ≡ map g (map f x)
    isSetF : ∀{ℓ} {X : Type ℓ} → isSet (F X)
