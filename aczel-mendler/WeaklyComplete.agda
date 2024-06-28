{-# OPTIONS --cubical #-}

open import Utilities

-- Assume given a set-valued functor F

module WeaklyComplete {ℓs} (Fun : Functor ℓs) (ℓ : Level) where

open Functor Fun
open import Coalgebras Fun

-- ==============================================

-- The *weakly* complete coalgebra: the union of all coalgebras

wνF : Type (ℓ-max ℓs (ℓ-suc ℓ))
wνF = Σ[ C ∈ Coalg ℓ ] ⟨ C ⟩ 

-- Unfolding is just pairing
unfold : (C : Coalg ℓ) → ⟨ C ⟩ → wνF
unfold C x = C , x

coalg-wνF : wνF → F wνF
coalg-wνF (C , x) = map (unfold C) (coalg C x)

unfold-eq : (C : Coalg ℓ) → map (unfold C) ∘ coalg C ≡ coalg-wνF ∘ unfold C
unfold-eq C = refl

wνF-Coalg : Coalg (ℓ-max ℓs (ℓ-suc ℓ))
wνF-Coalg = wνF , coalg-wνF

unfold-CoalgHom : (C : Coalg ℓ) → CoalgHom C wνF-Coalg
unfold-CoalgHom C = unfold C , unfold-eq C

