{-# OPTIONS --cubical #-}

module Utilities where

open import Cubical.Foundations.Everything public
open import Cubical.HITs.SetQuotients public
open import Cubical.Data.Nat hiding (elim) public
open import Cubical.Data.Sigma public
open import Cubical.Data.Sum renaming (rec to rec⊎) hiding (map; elim) public
open import Cubical.HITs.PropositionalTruncation renaming (rec to recP; elim to elimP) hiding (map; rec2) public
open import Cubical.Relation.Binary.Base public
open BinaryRelation public

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

-- Different notion of functor, which act only on functions with set-valued codomain.
-- (Preservation of identity is never used.)

record Functor ℓs : Typeω where
  field    
    F : ∀ {ℓ} → Type ℓ → Type (ℓ-max ℓs ℓ)
    map : ∀{ℓ ℓ'}{X : Type ℓ}{Y : Type ℓ'} → isSet Y → (f : X → Y) → F X → F Y
    map∘ : ∀{ℓ ℓ' ℓ''}{X : Type ℓ}{Y : Type ℓ'}{Z : Type ℓ''}
      → {setY : isSet Y} {setZ : isSet Z}
      → {g : Y → Z} {f : X → Y} (x : F X)
      → map setZ (g ∘ f) x ≡ map setZ g (map setY f x)
    isSetF : ∀{ℓ} {X : Type ℓ} → isSet (F X)

module _ {ℓs} (Fun : Functor ℓs) where

  open Functor Fun

  relLift : ∀{ℓ ℓʳ} {A : Type ℓ} (R : A → A → Type ℓʳ)
    → F A → F A → Type (ℓ-max (ℓ-max ℓs ℓ) ℓʳ)
  relLift R x y = map squash/ ([_] {R = R}) x ≡ map squash/ ([_] {R = R}) y

  map-lem : ∀ {ℓ ℓ' ℓ''} 
    → {A : Type ℓ} {X : A → Type ℓ'} {Y : Type ℓ''}
    → {setY : isSet Y}
    → {a : A} {f : X a → Y} {x : F (X a)} 
    → {a' : A} (eq : a ≡ a')
    → {f' : X a' → Y} (eqf : ∀ x → f x ≡ f' (transport (cong X eq) x)) 
    → {x' : F (X a')} (eqx : PathP (λ i → F (X (eq i))) x x') 
    → map setY f x ≡ map setY f' x'
  map-lem {X = X}{Y} {a = a}{f}{x} =
    J (λ a' eq → {f' : X a' → Y} (eqf : ∀ x → f x ≡ f' (transport (cong X eq) x)) 
               → {x' : F (X a')} (eqx : PathP (λ i → F (X (eq i))) x x') 
               → map _ f x ≡ map _ f' x')
      (λ {f'} eqf → cong₂ (map _) (funExt eqf ∙ funExt (λ z → cong f' (transportRefl z))))

-- Locally small types
isLocally[_]Small : ∀ {ℓL} (ℓS : Level) (X : Type ℓL) → Type (ℓ-max ℓL (ℓ-suc ℓS))
isLocally[ ℓS ]Small X = (x x' : X) → Σ[ Y ∈ Type ℓS ]  (x ≡ x') ≃ Y
