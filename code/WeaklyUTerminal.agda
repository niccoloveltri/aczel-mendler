{-# OPTIONS --cubical #-}

open import Utilities

-- Assume given a set-valued functor F

module WeaklyUTerminal {υ} (Fun : Functor υ) (ℓ : Level) where

open Functor Fun
open import Coalgebras Fun

-- ==============================================

-- The *weakly* U-terminal coalgebra: the union of all coalgebras

wνF : Type (ℓ-max υ (ℓ-suc ℓ))
wνF = Σ[ C ∈ Coalg ℓ ] ⟨ C ⟩ 

-- Unfolding is just pairing
unfold : (C : Coalg ℓ) → ⟨ C ⟩ → wνF
unfold C x = C , x

coalg-wνF : wνF → F wνF
coalg-wνF (C , x) = map (unfold C) (coalg C x)

unfold-eq : (C : Coalg ℓ) → map (unfold C) ∘ coalg C ≡ coalg-wνF ∘ unfold C
unfold-eq C = refl

wνF-Coalg : Coalg (ℓ-max υ (ℓ-suc ℓ))
wνF-Coalg = wνF , coalg-wνF

unfold-CoalgHom : (C : Coalg ℓ) → CoalgHom C wνF-Coalg
unfold-CoalgHom C = unfold C , unfold-eq C

isLocallySmall-wνF : isLocally[ (ℓ-max υ ℓ) ]Small wνF
isLocallySmall-wνF (C@(X , c) , x) (C'@(X' , c') , x') =
  _ ,
  (((X , c) , x) ≡ ((X' , c') , x')
   ≃⟨ invEquiv (isoToEquiv ΣPathIsoPathΣ) ⟩
   Σ[ eq ∈ ((X , c) ≡ (X' , c')) ] PathP (λ i → fst (eq i)) x x'
   ≃⟨ invEquiv (Σ-cong-equiv-fst (isoToEquiv ΣPathIsoPathΣ)) ⟩
   Σ (Σ[ eq ∈ (X ≡ X') ] PathP (λ i → eq i → F (eq i)) c c') (λ eqp → PathP (λ i → fst eqp i) x x')
   ≃⟨ isoToEquiv Σ-assoc-Iso ⟩
   Σ[ eq ∈ (X ≡ X') ] (PathP (λ i → eq i → F (eq i)) c c') × PathP (λ i → eq i) x x'
   ≃⟨ invEquiv (Σ-cong-equiv-fst (invEquiv univalence)) ⟩
   Σ[ e ∈ (X ≃ X') ] (PathP (λ i → ua e i → F (ua e i)) c c') × PathP (λ i → ua e i) x x'
   ■)

