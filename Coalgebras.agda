{-# OPTIONS --cubical #-}

open import Utilities

-- Assume given a set-valued functor F
-- (preservation of identity is not needed though?)

module Coalgebras (SF : SemiFunctor) where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Sum renaming (rec to rec⊎) hiding (map)
open import Cubical.HITs.SetQuotients
open import Cubical.HITs.PropositionalTruncation renaming (rec to recP) hiding (map)
open import Cubical.Relation.Binary.Base
open BinaryRelation
open SemiFunctor SF

-- ==============================================

-- COALGEBRAS AND COALGEBRA MORPHISMS

Coalg : ∀ ℓ → Type (ℓ-suc ℓ)
Coalg ℓ = Σ[ A ∈ Type ℓ ] (A → F A)

coalg : ∀{ℓ} (C : Coalg ℓ) → ⟨ C ⟩ → F ⟨ C ⟩
coalg = snd

CoalgHom : ∀{ℓ ℓ'} (C : Coalg ℓ) (C' : Coalg ℓ') → Type (ℓ-max ℓ ℓ')
CoalgHom (A , a) (A' , a') = Σ[ f ∈ (A → A') ] map f ∘ a ≡ a' ∘ f

CoalgHom∘ : ∀{ℓ ℓ' ℓ''} {C : Coalg ℓ} {C' : Coalg ℓ'} {C'' : Coalg ℓ''}
  → CoalgHom C' C'' → CoalgHom C C' → CoalgHom C C''
CoalgHom∘ {C = A , a} {B , b} {C , c} (f , fhom) (g , ghom) = f ∘ g ,
  (map (f ∘ g) ∘ a
   ≡⟨ cong (_∘ a) (funExt map∘) ⟩
   map f ∘ map g ∘ a
   ≡⟨ cong (λ x → map f ∘ x) ghom ⟩
   map f ∘ b ∘ g
   ≡⟨ cong (_∘ g) fhom ⟩
   c ∘ f ∘ g
   ∎)

-- A coalgebra is strongly extensional if any other coalgebra has at
-- most one coalgebra morphism into it.
strExt : ∀ {ℓ} ℓ' → (C : Coalg ℓ) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
strExt ℓ' C = (C' : Coalg ℓ') → isProp (CoalgHom C' C)

-- A coalgebra is copmlete if any other coalgebra has exactly one
-- coalgebra morphism into it.
complete : ∀ {ℓ} ℓ' → (C : Coalg ℓ) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
complete ℓ' C = (C' : Coalg ℓ') → isContr (CoalgHom C' C)

