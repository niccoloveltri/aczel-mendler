{-# OPTIONS --cubical #-}

open import Utilities
open import Cubical.Foundations.Everything
import Coalgebras 

module Precongruences (SF : SemiFunctor) (ℓ : Level) (C : Coalgebras.Coalg SF ℓ) where

open import Cubical.Data.Sigma
open import Cubical.Data.Sum renaming (rec to rec⊎) hiding (map)
open import Cubical.HITs.SetQuotients
open import Cubical.HITs.PropositionalTruncation renaming (rec to recP) hiding (map)
open import Cubical.Relation.Binary.Base
open BinaryRelation
open SemiFunctor SF
open Coalgebras SF


A = ⟨ C ⟩
a = coalg C

-- Lifting a relation R on A to another relation FRel R on A
relLift : ∀{ℓʳ} (R : A → A → Type ℓʳ) → F A → F A → Type (ℓ-max ℓ ℓʳ)
relLift R x y = map ([_] {R = R}) x ≡ map ([_] {R = R}) y

FRel : ∀{ℓʳ} (R : A → A → Type ℓʳ) → A → A → Type (ℓ-max ℓ ℓʳ)
FRel R x y = relLift R (a x) (a y)

-- FRel is a monotone operator
monQuot : ∀{ℓʳ ℓˢ} {R : A → A → Type ℓʳ} {S : A → A → Type ℓˢ}
  → (∀ x y → R x y → S x y)
  → A / R → A / S
monQuot k = rec squash/ [_] (λ x y r → eq/ x y (k x y r))

monFRel : ∀{ℓʳ ℓˢ} {R : A → A → Type ℓʳ} {S : A → A → Type ℓˢ}
  → (∀ x y → R x y → S x y)
  → ∀ x y → FRel R x y → FRel S x y
monFRel {R = R} {S} k x y r =
  map ([_] {R = S}) (a x)
  ≡⟨ refl ⟩
  map (monQuot k ∘ [_] {R = R}) (a x)
  ≡⟨ map∘ _ ⟩
  map (monQuot k) (map ([_] {R = R}) (a x))
  ≡⟨ cong (map (monQuot k)) r ⟩
  map (monQuot k) (map ([_] {R = R}) (a y))
  ≡⟨ sym (map∘ _) ⟩
  map (monQuot k ∘ [_] {R = R}) (a y)
  ≡⟨ refl ⟩
  map ([_] {R = S}) (a y)
  ∎  

-- Definition of precongruence (FRel-coalgebra in relations)
isPrecong : ∀{ℓʳ} (R : A → A → Type ℓʳ) → Type (ℓ-max ℓ ℓʳ)
isPrecong R = ∀ x y → R x y → FRel R x y

Precong : ∀ ℓʳ → Type (ℓ-max ℓ (ℓ-suc ℓʳ))
Precong ℓʳ = Σ[ R ∈ (A → A → Type ℓʳ) ] isPropRel R × isPrecong R

RPrecong : ∀ ℓʳ → Type (ℓ-max ℓ (ℓ-suc ℓʳ))
RPrecong ℓʳ = Σ[ R ∈ (A → A → Type ℓʳ) ] isPropRel R × isReflRel R × isPrecong R

-- The maximal precongruence: the union of all precongruences
wνFRel' : ∀ ℓʳ → A → A → Type (ℓ-max ℓ (ℓ-suc ℓʳ))
wνFRel' ℓʳ x y = Σ[ S ∈ Precong ℓʳ ] S .fst x y

wνFRel : ∀ ℓʳ → A → A → Type (ℓ-max ℓ (ℓ-suc ℓʳ))
wνFRel ℓʳ x y = ∥ wνFRel' ℓʳ x y ∥₁

-- wνFRel is a precongurence
monwνFRel' : ∀ {ℓʳ} x y → wνFRel' ℓʳ x y → FRel (wνFRel ℓʳ) x y
monwνFRel' x y (S@(R , q , p) , s) = monFRel (λ _ _ r → ∣ S , r ∣₁) _ _ (p x y s)

monwνFRel : ∀ {ℓʳ} x y → wνFRel ℓʳ x y → FRel (wνFRel ℓʳ) x y
monwνFRel x y = recP (isSetF _ _) (monwνFRel' x y)

-- Quotienting a coalgebra by its largest precongruence
MaxQuot : ∀ ℓʳ → Type (ℓ-max ℓ (ℓ-suc ℓʳ))
MaxQuot ℓʳ = A / wνFRel ℓʳ

-- The quotient is a coalgebra, and the eq. class function [_] is a coalgebra morphism.
coalg-MaxQuot : ∀{ℓʳ} → MaxQuot ℓʳ → F (MaxQuot ℓʳ)
coalg-MaxQuot = rec isSetF (map [_] ∘ a) monwνFRel

MaxQuot-Coalg : ∀ ℓʳ → Coalg (ℓ-max ℓ (ℓ-suc ℓʳ))
MaxQuot-Coalg ℓʳ = MaxQuot ℓʳ , coalg-MaxQuot

coalg-MaxQuot-CoalgHom : ∀{ℓʳ} → CoalgHom C (MaxQuot-Coalg ℓʳ)
coalg-MaxQuot-CoalgHom = [_] , funExt (λ _ → refl)


-- =====================================================

{- S-EXTENSIONALITY -}

-- A coalgebra is *s-extensional* if,
-- whenever two states are related by a *reflexive* precongruence,
-- then they are equal.
sExt : ∀ ℓʳ → Type (ℓ-max ℓ (ℓ-suc ℓʳ))
sExt ℓʳ = (x y : A) (S : Precong ℓʳ) → isReflRel (S .fst) → S .fst x y → x ≡ y

-- This notion differs from Aczel and Mendler's one, since they
-- moreover ask the pregrongruence to be transitive and symmetric,
-- i.e. a congruence.
-- But reflexivity is sufficient.

sExt→strExt' : ∀{ℓ'} → sExt (ℓ-max ℓ ℓ')
  → (C' : Coalg ℓ') (h k : CoalgHom C' C)
  → ∀ z → fst h z ≡ fst k z
sExt→strExt' {ℓ'} sext C'@(A' , a') (f , fhom) (f' , fhom') z = sext _ _ S r s
  where
    R' : A → A → Type (ℓ-max ℓ ℓ')
    R' x x' = Σ[ y ∈ A' ] (x ≡ f y) × (x' ≡ f' y)

    R : A → A → Type (ℓ-max ℓ ℓ')
    R x x' = ∥ R' x x' ⊎ (x ≡ x') ∥₁

    Rp'' : ∀ x₁ x₂ → x₁ ≡ x₂ → FRel R x₁ x₂
    Rp'' x₁ x₂ eq i = map [_] (coalg C (eq i))

    Rp' : ∀ x₁ x₂ → R' x₁ x₂ → FRel R x₁ x₂
    Rp' x₁ x₂ (y , eq₁ , eq₂) = 
      map [_] (coalg C x₁)
      ≡⟨ cong (map [_] ∘ coalg C) eq₁ ⟩
      map [_] (coalg C (f y))
      ≡⟨ (λ i → map [_] (fhom (~ i) y)) ⟩
      map [_] (map f (a' y))
      ≡⟨ sym (map∘ _) ⟩
      map ([_] ∘ f) (a' y)
      ≡⟨ cong (λ h → map h (a' y)) (funExt (λ y → eq/ _ _ ∣ inl (_ , refl , refl) ∣₁)) ⟩
      map ([_] ∘ f') (a' y)
      ≡⟨ map∘ _ ⟩
      map [_] (map f' (a' y))
      ≡⟨ (λ i → map [_] (fhom' i y)) ⟩
      map [_] (coalg C (f' y))
      ≡⟨ (λ i → map [_] (coalg C (eq₂ (~ i)))) ⟩
      map [_] (coalg C x₂)
      ∎

    Rp : isPrecong R
    Rp x₁ x₂ = recP (isSetF _ _) (rec⊎ (Rp' x₁ x₂) (Rp'' x₁ x₂))

    S : Precong (ℓ-max ℓ ℓ')
    S = R , (λ _ _ → isPropPropTrunc) , Rp

    r : isReflRel R
    r x = ∣ inr refl ∣₁

    s : R (f z) (f' z)
    s = ∣ inl (z , refl , refl) ∣₁

sExt→strExt : ∀{ℓ'} → sExt (ℓ-max ℓ ℓ') → strExt ℓ' C
sExt→strExt sext C' h k =
  Σ≡Prop (λ _ → isSetΠ (λ _ → isSetF) _ _)
         (funExt (sExt→strExt' sext C' h k))
