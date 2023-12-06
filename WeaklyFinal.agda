{-# OPTIONS --cubical #-}

open import Utilities
open import Cubical.Foundations.Everything

-- Assume given a set-valued semifunctor F

module WeaklyFinal (Fun : Functor) (ℓ : Level) where

open import Cubical.Data.Sigma
open import Cubical.Data.Sum renaming (rec to rec⊎) hiding (map)
open import Cubical.HITs.SetQuotients
open import Cubical.HITs.PropositionalTruncation renaming (rec to recP) hiding (map)
open import Cubical.Relation.Binary.Base
open BinaryRelation
open Functor Fun
open import Coalgebras Fun

-- ==============================================

-- The *weakly* final coalgebra: the union of all coalgebras
--module WeaklyFinalCoalgebra (ℓ : Level) where

wνF : Type (ℓ-suc ℓ)
wνF = Σ[ C ∈ Coalg ℓ ] ⟨ C ⟩ 

-- Unfolding is just pairing
unfold : (C : Coalg ℓ) → ⟨ C ⟩ → wνF
unfold C x = C , x

coalg-wνF : wνF → F wνF
coalg-wνF (C , x) = map (unfold C) (coalg C x)

unfold-eq : (C : Coalg ℓ) → map (unfold C) ∘ coalg C ≡ coalg-wνF ∘ unfold C
unfold-eq C = refl

wνF-Coalg : Coalg (ℓ-suc ℓ)
wνF-Coalg = wνF , coalg-wνF

unfold-CoalgHom : (C : Coalg ℓ) → CoalgHom C wνF-Coalg
unfold-CoalgHom C = unfold C , unfold-eq C


-- -- Lifting a relation R on A to another relation FRel R on A
-- module Precongruence (ℓ : Level) (C : Coalg ℓ) where

--   A = ⟨ C ⟩
--   a = coalg C

--   relLift : ∀{ℓʳ} (R : A → A → Type ℓʳ) → F A → F A → Type (ℓ-max ℓ ℓʳ)
--   relLift R x y = map ([_] {R = R}) x ≡ map ([_] {R = R}) y

--   FRel : ∀{ℓʳ} (R : A → A → Type ℓʳ) → A → A → Type (ℓ-max ℓ ℓʳ)
--   FRel R x y = relLift R (a x) (a y)

-- -- FRel is a monotone operator
--   monQuot : ∀{ℓʳ ℓˢ} {R : A → A → Type ℓʳ} {S : A → A → Type ℓˢ}
--     → (∀ x y → R x y → S x y)
--     → A / R → A / S
--   monQuot k = rec squash/ [_] (λ x y r → eq/ x y (k x y r))

--   monFRel : ∀{ℓʳ ℓˢ} {R : A → A → Type ℓʳ} {S : A → A → Type ℓˢ}
--     → (∀ x y → R x y → S x y)
--     → ∀ x y → FRel R x y → FRel S x y
--   monFRel {R = R} {S} k x y r =
--     map ([_] {R = S}) (a x)
--     ≡⟨ refl ⟩
--     map (monQuot k ∘ [_] {R = R}) (a x)
--     ≡⟨ map∘ _ ⟩
--     map (monQuot k) (map ([_] {R = R}) (a x))
--     ≡⟨ cong (map (monQuot k)) r ⟩
--     map (monQuot k) (map ([_] {R = R}) (a y))
--     ≡⟨ sym (map∘ _) ⟩
--     map (monQuot k ∘ [_] {R = R}) (a y)
--     ≡⟨ refl ⟩
--     map ([_] {R = S}) (a y)
--     ∎  

-- -- Definition of precongruence (FRel-coalgebra in relations)
--   isPrecong : ∀{ℓʳ} (R : A → A → Type ℓʳ) → Type (ℓ-max ℓ ℓʳ)
--   isPrecong R = ∀ x y → R x y → FRel R x y

--   Precong : ∀ ℓʳ → Type (ℓ-max ℓ (ℓ-suc ℓʳ))
--   Precong ℓʳ = Σ[ R ∈ (A → A → Type ℓʳ) ] isPropRel R × isPrecong R

--   RPrecong : ∀ ℓʳ → Type (ℓ-max ℓ (ℓ-suc ℓʳ))
--   RPrecong ℓʳ = Σ[ R ∈ (A → A → Type ℓʳ) ] isPropRel R × isReflRel R × isPrecong R

-- -- The maximal precongruence: the union of all precongruences
--   wνFRel' : ∀ ℓʳ → A → A → Type (ℓ-max ℓ (ℓ-suc ℓʳ))
--   wνFRel' ℓʳ x y = Σ[ S ∈ Precong ℓʳ ] S .fst x y

--   wνFRel : ∀ ℓʳ → A → A → Type (ℓ-max ℓ (ℓ-suc ℓʳ))
--   wνFRel ℓʳ x y = ∥ wνFRel' ℓʳ x y ∥₁

--   monwνFRel' : ∀ {ℓʳ} x y → wνFRel' ℓʳ x y → FRel (wνFRel ℓʳ) x y
--   monwνFRel' x y (S@(R , q , p) , s) = monFRel (λ _ _ r → ∣ S , r ∣₁) _ _ (p x y s)

--   monwνFRel : ∀ {ℓʳ} x y → wνFRel ℓʳ x y → FRel (wνFRel ℓʳ) x y
--   monwνFRel x y = recP (isSetF _ _) (monwνFRel' x y)

--   MaxQuot : ∀ ℓʳ → Type (ℓ-max ℓ (ℓ-suc ℓʳ))
--   MaxQuot ℓʳ = A / wνFRel ℓʳ

--   coalg-MaxQuot : ∀{ℓʳ} → MaxQuot ℓʳ → F (MaxQuot ℓʳ)
--   coalg-MaxQuot = rec isSetF (map [_] ∘ a) monwνFRel

--   MaxQuot-Coalg : ∀ ℓʳ → Coalg (ℓ-max ℓ (ℓ-suc ℓʳ))
--   MaxQuot-Coalg ℓʳ = MaxQuot ℓʳ , coalg-MaxQuot

--   coalg-MaxQuot-CoalgHom : ∀{ℓʳ} → CoalgHom C (MaxQuot-Coalg ℓʳ)
--   coalg-MaxQuot-CoalgHom = [_] , funExt (λ _ → refl)

-- -- The candidate for final coalgebra:
-- -- The set-quotient of the weakly final coalgebra by the maximal precongruence.
-- module FinalCoalgebra (ℓ : Level) where

--   open WeaklyFinalCoalgebra ℓ
--   open Precongruence --(ℓ-suc ℓ) wνF-Coalg

--   νF : Type (ℓ-suc ℓ)
--   νF = MaxQuot _ wνF-Coalg ℓ
  
--   coalg-νF : νF → F νF
--   coalg-νF = coalg-MaxQuot _ wνF-Coalg

--   νF-Coalg : Coalg (ℓ-suc ℓ)
--   νF-Coalg = MaxQuot-Coalg _ wνF-Coalg ℓ

--   sExtL : Type (ℓ-suc (ℓ-suc ℓ))
--   sExtL = (x y : νF) (S : Precong _ νF-Coalg (ℓ-suc ℓ)) → isReflRel (S .fst) → S .fst x y → x ≡ y

--   sExtS : Type (ℓ-suc ℓ)
--   sExtS = (x y : νF) (S : Precong _ νF-Coalg ℓ) → isReflRel (S .fst) → S .fst x y → x ≡ y

--   strExt : Type (ℓ-suc ℓ)
--   strExt = (C : Coalg ℓ) → isProp (CoalgHom C νF-Coalg)

--   sExtL→strExt' : sExtL 
--     → (C : Coalg ℓ) (h k : CoalgHom C νF-Coalg)
--     → ∀ z → fst h z ≡ fst k z
--   sExtL→strExt' sext C'@(A' , a') (f , fhom) (f' , fhom') z = sext _ _ S r s
--     where
--       R' : νF → νF → Type (ℓ-suc ℓ)
--       R' x x' = Σ[ y ∈ A' ] (x ≡ f y) × (x' ≡ f' y)

--       R : νF → νF → Type (ℓ-suc ℓ)
--       R x x' = ∥ R' x x' ⊎ (x ≡ x') ∥₁

--       Rp'' : ∀ x₁ x₂ → x₁ ≡ x₂ → FRel (ℓ-suc ℓ) νF-Coalg R x₁ x₂
--       Rp'' x₁ x₂ eq i = map [_] (coalg-νF (eq i))

--       Rp' : ∀ x₁ x₂ → R' x₁ x₂ → FRel (ℓ-suc ℓ) νF-Coalg R x₁ x₂
--       Rp' x₁ x₂ (y , eq₁ , eq₂) = 
--         map [_] (coalg-νF x₁)
--         ≡⟨ cong (map [_] ∘ coalg-νF) eq₁ ⟩
--         map [_] (coalg-νF (f y))
--         ≡⟨ (λ i → map [_] (fhom (~ i) y)) ⟩
--         map [_] (map f (a' y))
--         ≡⟨ sym (map∘ _) ⟩
--         map ([_] ∘ f) (a' y)
--         ≡⟨ cong (λ h → map h (a' y)) (funExt (λ y → eq/ _ _ ∣ inl (_ , refl , refl) ∣₁)) ⟩
--         map ([_] ∘ f') (a' y)
--         ≡⟨ map∘ _ ⟩
--         map [_] (map f' (a' y))
--         ≡⟨ (λ i → map [_] (fhom' i y)) ⟩
--         map [_] (coalg-νF (f' y))
--         ≡⟨ (λ i → map [_] (coalg-νF (eq₂ (~ i)))) ⟩
--         map [_] (coalg-νF x₂)
--         ∎

--       Rp : isPrecong _ νF-Coalg R
--       Rp x₁ x₂ = recP (isSetF _ _) (rec⊎ (Rp' x₁ x₂) (Rp'' x₁ x₂))

--       S : Precong _ νF-Coalg _
--       S = R , (λ _ _ → isPropPropTrunc) , Rp

--       r : isReflRel R
--       r x = ∣ inr refl ∣₁

--       s : R (f z) (f' z)
--       s = ∣ inl (z , refl , refl) ∣₁

--   sExtL→strExt : sExtL → strExt
--   sExtL→strExt sext C' h k =
--     Σ≡Prop (λ _ → isSetΠ (λ _ → isSetF) _ _)
--            (funExt (sExtL→strExt' sext C' h k))

--   sExtS-MaxQuot' : (x y : wνF) (S : Precong _ νF-Coalg ℓ)
--     → isReflRel (S .fst)
--     → S .fst [ x ] [ y ] → wνFRel _ wνF-Coalg ℓ x y
--   sExtS-MaxQuot' x y S@(R , q , p) r s = ∣ S' , s ∣₁
--     where
--       open IterQuot _ (wνFRel _ wνF-Coalg ℓ) R r

--       R' : wνF → wνF → Type ℓ
--       R' x y = R [ x ] [ y ] 

--       Rp' : isPrecong _ wνF-Coalg R'
--       Rp' x y r =
--         map ([_] {R = R'}) (coalg-wνF x)
--         ≡⟨ refl ⟩
--         map (collapse/ ∘ [_] {R = R} ∘ [_] {R = wνFRel _ wνF-Coalg ℓ}) (coalg-wνF x)
--         ≡⟨ map∘ _ ⟩
--         map collapse/ (map ([_] {R = R} ∘ [_] {R = wνFRel _ wνF-Coalg ℓ}) (coalg-wνF x))
--         ≡⟨ cong (map collapse/) (map∘ _) ⟩
--         map collapse/ (map ([_] {R = R}) (coalg-MaxQuot _ wνF-Coalg [ x ]))
--         ≡⟨ cong (map collapse/) (p _ _ r) ⟩
--         map collapse/ (map ([_] {R = R}) (coalg-MaxQuot _ wνF-Coalg [ y ]))
--         ≡⟨ cong (map collapse/) (sym (map∘ _)) ⟩
--         map collapse/ (map ([_] {R = R} ∘ [_] {R = wνFRel _ wνF-Coalg ℓ}) (coalg-wνF y))
--         ≡⟨ sym (map∘ _) ⟩
--         map (collapse/ ∘ [_] {R = R} ∘ [_] {R = wνFRel _ wνF-Coalg ℓ}) (coalg-wνF y)
--         ≡⟨ refl ⟩
--         map ([_] {R = R'}) (coalg-wνF y)
--         ∎

--       S' : Precong _ wνF-Coalg ℓ
--       S' = R' , (λ _ _ → q _ _) , Rp'

--   sExtS-MaxQuot : sExtS 
--   sExtS-MaxQuot =
--     elimProp2
--       (λ _ _ → isPropΠ3 (λ _ _ _ → squash/ _ _))
--       (λ x y S r s → eq/ _ _ (sExtS-MaxQuot' x y S r s))


--   module FinalityWithPropResizing (PR : PropRes ℓ (ℓ-suc ℓ)) where

--     sExtL-MaxQuot : sExtL
--     sExtL-MaxQuot x y S@(R , p , q) r s = sExtS-MaxQuot x y S' r' s'
--       where          
--         R' : νF → νF → Type ℓ
--         R' x₁ x₂ = PR (R x₁ x₂) (p x₁ x₂) .fst

--         e : ∀ x₁ x₂ → R x₁ x₂ ≃ R' x₁ x₂
--         e x₁ x₂ = PR (R x₁ x₂) (p x₁ x₂) .snd

--         p' : isPropRel R'
--         p' x₁ x₂ = isOfHLevelRespectEquiv 1 (e x₁ x₂) (p x₁ x₂)
        
--         open EquivQuot _ R R' e

--         q' :  isPrecong (ℓ-suc ℓ) νF-Coalg R'
--         q' x₁ x₂ r' =
--           map [_] (coalg-νF x₁)
--           ≡⟨ refl ⟩
--           map (changeQuot ∘ [_]) (coalg-νF x₁)
--           ≡⟨ map∘ _ ⟩
--           map changeQuot (map [_] (coalg-νF x₁))
--           ≡⟨ cong (map changeQuot) (q x₁ x₂ (invEq (e x₁ x₂) r')) ⟩
--           map changeQuot (map [_] (coalg-νF x₂))
--           ≡⟨ sym (map∘ _) ⟩
--           map (changeQuot ∘ [_]) (coalg-νF x₂)
--           ≡⟨ refl ⟩
--           map [_] (coalg-νF x₂)
--           ∎

--         S' : Precong (ℓ-suc ℓ) νF-Coalg ℓ
--         S' = R' , p' , q'

--         r' : isReflRel R'
--         r' z = equivFun (e z z) (r z)

--         s' : R' x y
--         s' = equivFun (e x y) s

--     uniq-mor : (C : Coalg ℓ) → isProp (CoalgHom C νF-Coalg)
--     uniq-mor = sExtL→strExt sExtL-MaxQuot

--     final : (C : Coalg ℓ) → isContr (CoalgHom C νF-Coalg)
--     final C .fst = CoalgHom∘ {C = C}{wνF-Coalg}{νF-Coalg} (coalg-MaxQuot-CoalgHom _ _) (unfold-CoalgHom C)
--     final C .snd = uniq-mor _ _


