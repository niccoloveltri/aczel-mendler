{-# OPTIONS --cubical #-}

open import Utilities
import Coalgebras 

module MaxQuotExt {ℓs} (Fun : Functor ℓs) (ℓ : Level) (C : Coalgebras.Coalg Fun ℓ) (setC : isSet ⟨ C ⟩) where

open Functor Fun
open Coalgebras Fun
open import Precongruences Fun 

-- The quotient by the largest precongruence is s-extensional

sExt-MaxQuot' : ∀ {ℓʳ} (x y : ⟨ C ⟩) (S : Precong _ (MaxQuot-Coalg _ C setC ℓʳ) squash/ ℓʳ)
  → isReflRel (S .fst)
  → S .fst [ x ] [ y ] → wνFRel _ C setC ℓʳ x y
sExt-MaxQuot' {ℓʳ} x y S@(R , q , p) r s = ∣ S' , s ∣₁
  where
    open IterQuot _ (wνFRel _ C setC ℓʳ) R r

    R' : ⟨ C ⟩ → ⟨ C ⟩ → Type ℓʳ
    R' x y = R [ x ] [ y ] 

    Rp' : isPrecong _ C setC R'
    Rp' x y r =
      map _ ([_] {R = R'}) (coalg C x)
      ≡⟨ refl ⟩
      map _ (collapse/ ∘ [_] {R = R} ∘ [_] {R = wνFRel _ C setC ℓʳ}) (coalg C x)
      ≡⟨ map∘ _ ⟩
      map _ collapse/ (map _ ([_] {R = R} ∘ [_] {R = wνFRel _ C setC ℓʳ}) (coalg C x))
      ≡⟨ cong (map _ collapse/) (map∘ _) ⟩
      map _ collapse/ (map _ ([_] {R = R}) (coalg-MaxQuot _ C setC [ x ]))
      ≡⟨ cong (map _ collapse/) (p _ _ r) ⟩
      map _ collapse/ (map _ ([_] {R = R}) (coalg-MaxQuot _ C setC [ y ]))
      ≡⟨ cong (map _ collapse/) (sym (map∘ _)) ⟩
      map _ collapse/ (map _ ([_] {R = R} ∘ [_] {R = wνFRel _ C setC ℓʳ}) (coalg C y))
      ≡⟨ sym (map∘ _) ⟩
      map _ (collapse/ ∘ [_] {R = R} ∘ [_] {R = wνFRel _ C setC ℓʳ}) (coalg C y)
      ≡⟨ refl ⟩
      map _ ([_] {R = R'}) (coalg C y)
      ∎

    S' : Precong _ C setC ℓʳ
    S' = R' , (λ _ _ → q _ _) , Rp'

sExt-MaxQuot : ∀ ℓʳ → sExt _ (MaxQuot-Coalg _ C setC ℓʳ) squash/ ℓʳ
sExt-MaxQuot ℓʳ =
  elimProp2
    (λ _ _ → isPropΠ3 (λ _ _ _ → squash/ _ _))
    (λ x y S r s → eq/ _ _ (sExt-MaxQuot' x y S r s))

