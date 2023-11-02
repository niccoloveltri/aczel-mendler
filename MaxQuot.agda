{-# OPTIONS --cubical #-}

open import Utilities
open import Cubical.Foundations.Everything
import Coalgebras 

module MaxQuot (SF : SemiFunctor) (ℓ : Level) (C : Coalgebras.Coalg SF ℓ) where

open import Cubical.Data.Sigma
open import Cubical.Data.Sum renaming (rec to rec⊎) hiding (map)
open import Cubical.HITs.SetQuotients
open import Cubical.HITs.PropositionalTruncation renaming (rec to recP) hiding (map)
open import Cubical.Relation.Binary.Base
open BinaryRelation
open SemiFunctor SF
open Coalgebras SF
open import Precongruences SF 

sExt-MaxQuot' : ∀ {ℓʳ} (x y : ⟨ C ⟩) (S : Precong _ (MaxQuot-Coalg _ C ℓʳ) ℓʳ)
  → isReflRel (S .fst)
  → S .fst [ x ] [ y ] → wνFRel _ C ℓʳ x y
sExt-MaxQuot' {ℓʳ} x y S@(R , q , p) r s = ∣ S' , s ∣₁
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

sExt-MaxQuot : ∀ ℓʳ → sExt _ (MaxQuot-Coalg _ C ℓʳ) ℓʳ
sExt-MaxQuot ℓʳ =
  elimProp2
    (λ _ _ → isPropΠ3 (λ _ _ _ → squash/ _ _))
    (λ x y S r s → eq/ _ _ (sExt-MaxQuot' x y S r s))

