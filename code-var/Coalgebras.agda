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

isCoalgHom : ∀{ℓ ℓ'} (C : Coalg ℓ) (C' : Coalg ℓ')
  → isSet ⟨ C' ⟩
  → (f : ⟨ C ⟩ → ⟨ C' ⟩) → Type (ℓ-max (ℓ-max υ ℓ) ℓ')
isCoalgHom C C' setC' f = map setC' f ∘ coalg C ≡ coalg C' ∘ f

CoalgHom : ∀{ℓ ℓ'} (C : Coalg ℓ) (C' : Coalg ℓ') → isSet ⟨ C' ⟩
  → Type (ℓ-max (ℓ-max υ ℓ) ℓ')
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

-- A coalgebra is ℓ'-simple if any other ℓ'-coalgebra has at
-- most one coalgebra morphism into it.
is[_]Simple : ∀ {ℓ} ℓ' → (C : Coalg ℓ) → isSet ⟨ C ⟩ → Type (ℓ-max (ℓ-max υ ℓ) (ℓ-suc ℓ'))
is[ ℓ' ]Simple C setC = (C' : Coalg ℓ') → isProp (CoalgHom C' C setC)

-- A ℓ-coalgebra is ℓ'-terminal if any other ℓ'-coalgebra has exactly one
-- coalgebra morphism into it.
-- A ℓ-coalgebra is terminal if it is ℓ-terminal.
is[_]Terminal : ∀ {ℓ} ℓ' → (C : Coalg ℓ) → isSet ⟨ C ⟩ → Type (ℓ-max (ℓ-max υ ℓ) (ℓ-suc ℓ'))
is[ ℓ' ]Terminal C setC = (C' : Coalg ℓ') → isContr (CoalgHom C' C setC)

isTerminal : ∀ {ℓ} → (C : Coalg ℓ) → isSet ⟨ C ⟩ → Type (ℓ-max υ (ℓ-suc ℓ))
isTerminal {ℓ} = is[ ℓ ]Terminal

isTerminalSet : ∀ {ℓ} → (C : Coalg ℓ) → isSet ⟨ C ⟩ → Type (ℓ-max υ (ℓ-suc ℓ))
isTerminalSet {ℓ} C setC = (C' : Coalg ℓ) → isSet ⟨ C' ⟩ → isContr (CoalgHom C' C setC)

