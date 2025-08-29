{-# OPTIONS --cubical #-}

open import Utilities
import Coalgebras 

module MaxQuotExt {υ} (Fun : Functor υ) (ℓ : Level) (C : Coalgebras.Coalg Fun ℓ) where

open Functor Fun
open Coalgebras Fun
open import Precongruences Fun 

-- The quotient by the largest precongruence is precongruence simple

isPrecongSimple-MaxQuot' : ∀ {ℓʳ} (x y : ⟨ C ⟩) (S : Precong _ (MaxQuot-Coalg _ C ℓʳ) ℓʳ)
  → isReflRel (S .fst)
  → S .fst [ x ] [ y ] → wνFRel _ C ℓʳ x y
isPrecongSimple-MaxQuot' {ℓʳ} x y S@(R , q , p) r s = ∣ S' , s ∣₁
  where
    open IterQuot _ (wνFRel _ C ℓʳ) R r

    R' : ⟨ C ⟩ → ⟨ C ⟩ → Type ℓʳ
    R' x y = R [ x ] [ y ] 

    Rp' : isPrecong _ C R'
    Rp' x y r =
      map ([_] {R = R'}) (coalg C x)
      ≡⟨ refl ⟩
      map (collapse/ ∘ [_] {R = R} ∘ [_] {R = wνFRel _ C ℓʳ}) (coalg C x)
      ≡⟨ map∘ _ ⟩
      map collapse/ (map ([_] {R = R} ∘ [_] {R = wνFRel _ C ℓʳ}) (coalg C x))
      ≡⟨ cong (map collapse/) (map∘ _) ⟩
      map collapse/ (map ([_] {R = R}) (coalg-MaxQuot _ C [ x ]))
      ≡⟨ cong (map collapse/) (p _ _ r) ⟩
      map collapse/ (map ([_] {R = R}) (coalg-MaxQuot _ C [ y ]))
      ≡⟨ cong (map collapse/) (sym (map∘ _)) ⟩
      map collapse/ (map ([_] {R = R} ∘ [_] {R = wνFRel _ C ℓʳ}) (coalg C y))
      ≡⟨ sym (map∘ _) ⟩
      map (collapse/ ∘ [_] {R = R} ∘ [_] {R = wνFRel _ C ℓʳ}) (coalg C y)
      ≡⟨ refl ⟩
      map ([_] {R = R'}) (coalg C y)
      ∎

    S' : Precong _ C ℓʳ
    S' = R' , (λ _ _ → q _ _) , Rp'

isPrecongSimple-MaxQuot : ∀ ℓʳ → is[ _ ]PrecongSimple (MaxQuot-Coalg _ C ℓʳ) ℓʳ
isPrecongSimple-MaxQuot ℓʳ =
  elimProp2
    (λ _ _ → isPropΠ3 (λ _ _ _ → squash/ _ _))
    (λ x y S r s → eq/ _ _ (isPrecongSimple-MaxQuot' x y S r s))

