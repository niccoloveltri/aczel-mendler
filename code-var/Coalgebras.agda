{-# OPTIONS --cubical #-}

open import Utilities

-- Assume given a set-valued functor F

module Coalgebras {ℓs} (Fun : Functor ℓs) where

open Functor Fun

-- ==============================================

-- COALGEBRAS AND COALGEBRA MORPHISMS

Coalg : ∀ ℓ → Type (ℓ-max ℓs (ℓ-suc ℓ))
Coalg ℓ = Σ[ A ∈ Type ℓ ] (A → F A)

coalg : ∀{ℓ} (C : Coalg ℓ) → ⟨ C ⟩ → F ⟨ C ⟩
coalg = snd

isCoalgHom : ∀{ℓ ℓ'} (C : Coalg ℓ) (C' : Coalg ℓ')
  → isSet ⟨ C' ⟩
  → (f : ⟨ C ⟩ → ⟨ C' ⟩) → Type (ℓ-max (ℓ-max ℓs ℓ) ℓ')
isCoalgHom C C' setC' f = map setC' f ∘ coalg C ≡ coalg C' ∘ f

CoalgHom : ∀{ℓ ℓ'} (C : Coalg ℓ) (C' : Coalg ℓ') → isSet ⟨ C' ⟩
  → Type (ℓ-max (ℓ-max ℓs ℓ) ℓ')
CoalgHom C C' setC' = Σ[ f ∈ (⟨ C ⟩ → ⟨ C' ⟩) ] isCoalgHom C C' setC' f

CoalgHom∘ : ∀{ℓ ℓ' ℓ''} {C : Coalg ℓ} {C' : Coalg ℓ'} {C'' : Coalg ℓ''}
  → {setC' : isSet ⟨ C' ⟩} {setC'' : isSet ⟨ C'' ⟩}
  → CoalgHom C' C'' setC'' → CoalgHom C C' setC' → CoalgHom C C'' setC''
CoalgHom∘ {C = A , a} {B , b} {C , c} {_}{setC} (f , fhom) (g , ghom) = f ∘ g ,
  (map _ (f ∘ g) ∘ a
   ≡⟨ cong (_∘ a) (funExt map∘) ⟩
   map _ f ∘ map _ g ∘ a
   ≡⟨ cong (λ x → map setC f ∘ x) ghom ⟩
   map _ f ∘ b ∘ g
   ≡⟨ cong (_∘ g) fhom ⟩
   c ∘ f ∘ g
   ∎)

-- A coalgebra is strongly extensional if any other coalgebra has at
-- most one coalgebra morphism into it.
strExt : ∀ {ℓ} ℓ' → (C : Coalg ℓ) → isSet ⟨ C ⟩ → Type (ℓ-max (ℓ-max ℓs ℓ) (ℓ-suc ℓ'))
strExt ℓ' C setC = (C' : Coalg ℓ') → isProp (CoalgHom C' C setC)

-- A ℓ-coalgebra is ℓ'-complete if any other ℓ'-coalgebra has exactly one
-- coalgebra morphism into it.
-- A ℓ-coalgebra is final if it is ℓ-complete.
isComplete : ∀ {ℓ} ℓ' → (C : Coalg ℓ) → isSet ⟨ C ⟩ → Type (ℓ-max (ℓ-max ℓs ℓ) (ℓ-suc ℓ'))
isComplete ℓ' C setC = (C' : Coalg ℓ') → isContr (CoalgHom C' C setC)

isFinal : ∀ {ℓ} → (C : Coalg ℓ) → isSet ⟨ C ⟩ → Type (ℓ-max ℓs (ℓ-suc ℓ))
isFinal {ℓ} = isComplete ℓ

isFinalSet : ∀ {ℓ} → (C : Coalg ℓ) → isSet ⟨ C ⟩ → Type (ℓ-max ℓs (ℓ-suc ℓ))
isFinalSet {ℓ} C setC = (C' : Coalg ℓ) → isSet ⟨ C' ⟩ → isContr (CoalgHom C' C setC)

