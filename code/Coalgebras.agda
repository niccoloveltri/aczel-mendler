{-# OPTIONS --cubical #-}

open import Utilities

-- Assume given a set-valued functor F

module Coalgebras {υ} (Fun : Functor υ) where

open Functor Fun

-- ==============================================

-- COALGEBRAS AND COALGEBRA MORPHISMS

Coalg : ∀ ℓ → Type (ℓ-max υ (ℓ-suc ℓ))
Coalg ℓ = Σ[ A ∈ Type ℓ ] (A → F A)

coalg : ∀{ℓ} (C : Coalg ℓ) → ⟨ C ⟩ → F ⟨ C ⟩
coalg = snd

isCoalgHom : ∀{ℓ ℓ'} (C : Coalg ℓ) (C' : Coalg ℓ') (f : ⟨ C ⟩ → ⟨ C' ⟩) → Type (ℓ-max (ℓ-max υ ℓ) ℓ')
isCoalgHom C C' f = map f ∘ coalg C ≡ coalg C' ∘ f

CoalgHom : ∀{ℓ ℓ'} (C : Coalg ℓ) (C' : Coalg ℓ') → Type (ℓ-max (ℓ-max υ ℓ) ℓ')
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

-- A coalgebra is ℓ'-simple if any other ℓ'-coalgebra has at
-- most one coalgebra morphism into it.
is[_]Simple : ∀ {ℓ} ℓ' → (C : Coalg ℓ) → Type (ℓ-max (ℓ-max υ ℓ) (ℓ-suc ℓ'))
is[ ℓ' ]Simple C = (C' : Coalg ℓ') → isProp (CoalgHom C' C)

-- A ℓ-coalgebra is ℓ'-terminal if any other ℓ'-coalgebra has exactly one
-- coalgebra morphism into it.
-- A ℓ-coalgebra is terminal if it is ℓ-complete.
is[_]Terminal : ∀ {ℓ} ℓ' → (C : Coalg ℓ) → Type (ℓ-max (ℓ-max υ ℓ) (ℓ-suc ℓ'))
is[ ℓ' ]Terminal C = (C' : Coalg ℓ') → isContr (CoalgHom C' C)

isTerminal : ∀ {ℓ} → (C : Coalg ℓ) → Type (ℓ-max υ (ℓ-suc ℓ))
isTerminal {ℓ} = is[ ℓ ]Terminal 

