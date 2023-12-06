{-# OPTIONS --cubical #-}

open import Utilities

-- Assume given a set-valued functor F

module Coalgebras (Fun : Functor) where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Sum renaming (rec to rec⊎) hiding (map)
open import Cubical.HITs.SetQuotients
open import Cubical.HITs.PropositionalTruncation renaming (rec to recP) hiding (map)
open import Cubical.Relation.Binary.Base
open BinaryRelation
open Functor Fun

-- ==============================================

-- COALGEBRAS AND COALGEBRA MORPHISMS

Coalg : ∀ ℓ → Type (ℓ-suc ℓ)
Coalg ℓ = Σ[ A ∈ Type ℓ ] (A → F A)

coalg : ∀{ℓ} (C : Coalg ℓ) → ⟨ C ⟩ → F ⟨ C ⟩
coalg = snd

isCoalgHom : ∀{ℓ ℓ'} (C : Coalg ℓ) (C' : Coalg ℓ') (f : ⟨ C ⟩ → ⟨ C' ⟩) → Type (ℓ-max ℓ ℓ')
isCoalgHom C C' f = map f ∘ coalg C ≡ coalg C' ∘ f

CoalgHom : ∀{ℓ ℓ'} (C : Coalg ℓ) (C' : Coalg ℓ') → Type (ℓ-max ℓ ℓ')
CoalgHom C C' = Σ[ f ∈ (⟨ C ⟩ → ⟨ C' ⟩) ] isCoalgHom C C' f

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
isComplete : ∀ {ℓ} ℓ' → (C : Coalg ℓ) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
isComplete ℓ' C = (C' : Coalg ℓ') → isContr (CoalgHom C' C)

isFinal : ∀ {ℓ} → (C : Coalg ℓ) → Type (ℓ-suc ℓ)
isFinal {ℓ} C = (C' : Coalg ℓ) → isContr (CoalgHom C' C)

