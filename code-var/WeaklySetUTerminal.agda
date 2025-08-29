{-# OPTIONS --cubical #-}

open import Utilities

-- Assume given a set-valued functor F

module WeaklySetUTerminal {υ} (Fun : Functor υ) (ℓ : Level) where

open import Cubical.HITs.SetTruncation hiding (map) renaming (rec to recST)
open Functor Fun
open import Coalgebras Fun

-- ==============================================

-- The *weakly* SetU-terminal coalgebra: the union of all coalgebras

wνF : Type (ℓ-max υ (ℓ-suc ℓ))
wνF = ∥ Σ[ C ∈ Coalg ℓ ] ⟨ C ⟩ ∥₂

-- Unfolding is just pairing
unfold : (C : Coalg ℓ) → ⟨ C ⟩ → wνF
unfold C x = ∣ C , x ∣₂

coalg-wνF : wνF → F wνF
coalg-wνF = recST (isSetF) λ (C , x) → map squash₂ (unfold C) (coalg C x)

unfold-eq : (C : Coalg ℓ) → map squash₂ (unfold C) ∘ coalg C ≡ coalg-wνF ∘ unfold C
unfold-eq C = refl

wνF-Coalg : Coalg (ℓ-max υ (ℓ-suc ℓ))
wνF-Coalg = wνF , coalg-wνF

unfold-CoalgHom : (C : Coalg ℓ) → CoalgHom C wνF-Coalg _
unfold-CoalgHom C = unfold C , unfold-eq C
