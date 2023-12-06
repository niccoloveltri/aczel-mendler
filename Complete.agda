{-# OPTIONS --cubical #-}

open import Utilities
open import Cubical.Foundations.Everything

module Complete (Fun : Functor) (ℓ : Level) where

open import Cubical.Data.Sigma
open import Cubical.Data.Sum renaming (rec to rec⊎) hiding (map)
open import Cubical.HITs.SetQuotients
open import Cubical.HITs.PropositionalTruncation renaming (rec to recP) hiding (map)
open import Cubical.Relation.Binary.Base
open BinaryRelation
open Functor Fun
open import Coalgebras Fun
open import WeaklyFinal Fun ℓ
open import Precongruences Fun

-- The final coalgebra is the set-quotient of the weakly final
-- coalgebra by the maximal precongruence.

νF : Type (ℓ-suc ℓ)
νF = MaxQuot _ wνF-Coalg ℓ

coalg-νF : νF → F νF
coalg-νF = coalg-MaxQuot _ wνF-Coalg

νF-Coalg : Coalg (ℓ-suc ℓ)
νF-Coalg = MaxQuot-Coalg _ wνF-Coalg ℓ

sExtL : Type (ℓ-suc (ℓ-suc ℓ))
sExtL = sExt _ νF-Coalg (ℓ-suc ℓ)

sExtS : Type (ℓ-suc ℓ)
sExtS = sExt _ νF-Coalg ℓ

-- Proof:

-- For each coalgebra C, there is a coalgebra morphism to νF which factors to wνF.
-- Therefore, to prove that νF is complete is enough to show that it is strongly extensional. 
-- We know that every s-extensional coalgebra is strongly extensional.

sExtL→strExt : sExtL → strExt ℓ νF-Coalg
sExtL→strExt = sExt→strExt (ℓ-suc ℓ) νF-Coalg

-- And νF, being the quotient of a coalgebra by the largest preconruence, is s-extensional.
open import MaxQuot Fun _ wνF-Coalg
sExtS-νF : sExtS
sExtS-νF = sExt-MaxQuot ℓ

-- To put everything together we need propositional resizing.

-- Since we know that νF is s-extensional wrt. ℓ-valued
-- precongruences, but theorem sExtL→strExt requires s-extensionality
-- wrt. (ℓ + 1)-valued precongruences.
module FinalityWithPropResizing (PR : PropRes ℓ (ℓ-suc ℓ)) where

  sExtL-νF : sExtL
  sExtL-νF x y S@(R , p , q) r s = sExtS-νF x y S' r' s'
    where          
      R' : νF → νF → Type ℓ
      R' x₁ x₂ = PR (R x₁ x₂) (p x₁ x₂) .fst

      e : ∀ x₁ x₂ → R x₁ x₂ ≃ R' x₁ x₂
      e x₁ x₂ = PR (R x₁ x₂) (p x₁ x₂) .snd

      p' : isPropRel R'
      p' x₁ x₂ = isOfHLevelRespectEquiv 1 (e x₁ x₂) (p x₁ x₂)
      
      open EquivQuot _ R R' e

      q' :  isPrecong (ℓ-suc ℓ) νF-Coalg R'
      q' x₁ x₂ r' =
        map [_] (coalg-νF x₁)
        ≡⟨ refl ⟩
        map (changeQuot ∘ [_]) (coalg-νF x₁)
        ≡⟨ map∘ _ ⟩
        map changeQuot (map [_] (coalg-νF x₁))
        ≡⟨ cong (map changeQuot) (q x₁ x₂ (invEq (e x₁ x₂) r')) ⟩
        map changeQuot (map [_] (coalg-νF x₂))
        ≡⟨ sym (map∘ _) ⟩
        map (changeQuot ∘ [_]) (coalg-νF x₂)
        ≡⟨ refl ⟩
        map [_] (coalg-νF x₂)
        ∎

      S' : Precong (ℓ-suc ℓ) νF-Coalg ℓ
      S' = R' , p' , q'

      r' : isReflRel R'
      r' z = equivFun (e z z) (r z)

      s' : R' x y
      s' = equivFun (e x y) s

  uniq-mor : strExt ℓ νF-Coalg
  uniq-mor = sExtL→strExt sExtL-νF

  complete : isComplete ℓ νF-Coalg
  complete C .fst =
    CoalgHom∘ {C = C}{wνF-Coalg}{νF-Coalg}
              (coalg-MaxQuot-CoalgHom _ _)
              (unfold-CoalgHom C)
  complete C .snd = uniq-mor _ _


