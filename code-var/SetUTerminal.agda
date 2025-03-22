{-# OPTIONS --cubical #-}

module SetUTerminal where

open import Utilities
open import Cubical.HITs.SetTruncation hiding (map) renaming (rec to recST)

-- ==============================================

-- Construction of the SetU-terminal coalgebra, assuming propositional
-- resizing.
-- There are two versions, depending of whether the functor F is
-- of the form
-- 1) F : ∀{ℓ} → Type ℓ → Type (ℓ-max υ ℓ)
--    in module SetUTerminalSmall      
-- 2) F : ∀{ℓ} → Type ℓ → Type (ℓ-max (ℓ-suc υ) ℓ)
--    in module SetUTerminalLarge

module SetUTerminalSmall (ℓ : Level) (Fun : Functor ℓ) where

  open Functor Fun
  open import Coalgebras Fun
  open import WeaklySetUTerminal Fun ℓ
  open import Precongruences Fun

-- The ℓ-complete coalgebra is the set-quotient of the weakly final
-- coalgebra by the maximal precongruence.

  νF : Type (ℓ-suc ℓ)
  νF = MaxQuot _ wνF-Coalg squash₂ ℓ

  coalg-νF : νF → F νF
  coalg-νF = coalg-MaxQuot _ wνF-Coalg squash₂

  νF-Coalg : Coalg (ℓ-suc ℓ)
  νF-Coalg = MaxQuot-Coalg _ wνF-Coalg squash₂ ℓ

  isPrecongSimpleL : Type (ℓ-suc (ℓ-suc ℓ))
  isPrecongSimpleL = is[_]PrecongSimple _ νF-Coalg squash/ (ℓ-suc ℓ)

  isPrecongSimpleS : Type (ℓ-suc ℓ)
  isPrecongSimpleS = is[_]PrecongSimple _ νF-Coalg squash/ ℓ

-- Proof:

-- For each coalgebra C, there is a coalgebra morphism to νF which factors to wνF.
-- Therefore, to prove that νF is complete is enough to show that it is strongly extensional. 
-- We know that every s-extensional coalgebra is strongly extensional.

  isPrecongSimpleL→isSimple : isPrecongSimpleL → is[ ℓ ]Simple νF-Coalg squash/
  isPrecongSimpleL→isSimple = isPrecongSimple→isSimple (ℓ-suc ℓ) νF-Coalg squash/ squash/

-- And νF, being the quotient of a coalgebra by the largest preconruence, is s-extensional.
  open import MaxQuotExt Fun _ wνF-Coalg
  isPrecongSimpleS-νF : isPrecongSimpleS
  isPrecongSimpleS-νF = isPrecongSimple-MaxQuot squash₂ ℓ

-- To put everything together we need propositional resizing.

-- Since we know that νF is s-extensional wrt. ℓ-valued
-- precongruences, but theorem isPrecongSimpleL→isSimple requires s-extensionality
-- wrt. (ℓ + 1)-valued precongruences.
  module SetUTerminalWithPropResizing (PR : PropRes ℓ (ℓ-suc ℓ)) where

    isPrecongSimpleL-νF : isPrecongSimpleL
    isPrecongSimpleL-νF x y S@(R , p , q) r s = isPrecongSimpleS-νF x y S' r' s'
      where          
        R' : νF → νF → Type ℓ
        R' x₁ x₂ = PR (R x₁ x₂) (p x₁ x₂) .fst

        e : ∀ x₁ x₂ → R x₁ x₂ ≃ R' x₁ x₂
        e x₁ x₂ = PR (R x₁ x₂) (p x₁ x₂) .snd

        p' : isPropRel R'
        p' x₁ x₂ = isOfHLevelRespectEquiv 1 (e x₁ x₂) (p x₁ x₂)
     
        open EquivQuot _ R R' e

        q' :  isPrecong (ℓ-suc ℓ) νF-Coalg squash/ R'
        q' x₁ x₂ r' =
          map _ [_] (coalg-νF x₁)
          ≡⟨ refl ⟩
          map _ (changeQuot ∘ [_]) (coalg-νF x₁)
          ≡⟨ map∘ _ ⟩
          map _ changeQuot (map _ [_] (coalg-νF x₁))
          ≡⟨ cong (map squash/ changeQuot) (q x₁ x₂ (invEq (e x₁ x₂) r')) ⟩
          map _ changeQuot (map _ [_] (coalg-νF x₂))
          ≡⟨ sym (map∘ _) ⟩
          map _ (changeQuot ∘ [_]) (coalg-νF x₂)
          ≡⟨ refl ⟩
          map _ [_] (coalg-νF x₂)
          ∎

        S' : Precong (ℓ-suc ℓ) νF-Coalg squash/ ℓ
        S' = R' , p' , q'

        r' : isReflRel R'
        r' z = equivFun (e z z) (r z)

        s' : R' x y
        s' = equivFun (e x y) s

    uniq-mor : is[ ℓ ]Simple νF-Coalg _
    uniq-mor = isPrecongSimpleL→isSimple isPrecongSimpleL-νF

    setuterminal : is[ ℓ ]Terminal νF-Coalg _
    setuterminal C .fst =
      CoalgHom∘ {C = C}{wνF-Coalg}{νF-Coalg}
                (coalg-MaxQuot-CoalgHom _ _ squash₂)
                (unfold-CoalgHom C)
    setuterminal C .snd = uniq-mor _ _

-- =====================================================

module SetUTerminalLarge (ℓ : Level) (Fun : Functor (ℓ-suc ℓ)) where

  open Functor Fun
  open import Coalgebras Fun
  open import WeaklySetUTerminal Fun ℓ
  open import Precongruences Fun

-- The ℓ-complete coalgebra is the set-quotient of the weakly final
-- coalgebra by the maximal precongruence.

  νF : Type (ℓ-suc ℓ)
  νF = MaxQuot _ wνF-Coalg squash₂ ℓ

  coalg-νF : νF → F νF
  coalg-νF = coalg-MaxQuot _ wνF-Coalg squash₂

  νF-Coalg : Coalg (ℓ-suc ℓ)
  νF-Coalg = MaxQuot-Coalg _ wνF-Coalg squash₂ ℓ

  isPrecongSimpleL : Type (ℓ-suc (ℓ-suc ℓ))
  isPrecongSimpleL = is[_]PrecongSimple _ νF-Coalg squash/ (ℓ-suc ℓ)

  isPrecongSimpleS : Type (ℓ-suc ℓ)
  isPrecongSimpleS = is[_]PrecongSimple _ νF-Coalg squash/ ℓ

-- Proof:

-- For each coalgebra C, there is a coalgebra morphism to νF which factors to wνF.
-- Therefore, to prove that νF is complete is enough to show that it is strongly extensional. 
-- We know that every s-extensional coalgebra is strongly extensional.

  isPrecongSimpleL→isSimple : isPrecongSimpleL → is[ ℓ ]Simple νF-Coalg squash/
  isPrecongSimpleL→isSimple = isPrecongSimple→isSimple (ℓ-suc ℓ) νF-Coalg squash/ squash/

-- And νF, being the quotient of a coalgebra by the largest preconruence, is s-extensional.
  open import MaxQuotExt Fun _ wνF-Coalg
  isPrecongSimpleS-νF : isPrecongSimpleS
  isPrecongSimpleS-νF = isPrecongSimple-MaxQuot squash₂ ℓ

-- To put everything together we need propositional resizing.

-- Since we know that νF is s-extensional wrt. ℓ-valued
-- precongruences, but theorem isPrecongSimpleL→isSimple requires s-extensionality
-- wrt. (ℓ + 1)-valued precongruences.
  module SetUTerminalWithPropResizing (PR : PropRes ℓ (ℓ-suc ℓ)) where

    isPrecongSimpleL-νF : isPrecongSimpleL
    isPrecongSimpleL-νF x y S@(R , p , q) r s = isPrecongSimpleS-νF x y S' r' s'
      where          
        R' : νF → νF → Type ℓ
        R' x₁ x₂ = PR (R x₁ x₂) (p x₁ x₂) .fst

        e : ∀ x₁ x₂ → R x₁ x₂ ≃ R' x₁ x₂
        e x₁ x₂ = PR (R x₁ x₂) (p x₁ x₂) .snd
  
        p' : isPropRel R'
        p' x₁ x₂ = isOfHLevelRespectEquiv 1 (e x₁ x₂) (p x₁ x₂)
        
        open EquivQuot _ R R' e
  
        q' :  isPrecong (ℓ-suc ℓ) νF-Coalg squash/ R'
        q' x₁ x₂ r' =
          map _ [_] (coalg-νF x₁)
          ≡⟨ refl ⟩
          map _ (changeQuot ∘ [_]) (coalg-νF x₁)
          ≡⟨ map∘ _ ⟩
          map _ changeQuot (map _ [_] (coalg-νF x₁))
          ≡⟨ cong (map _ changeQuot) (q x₁ x₂ (invEq (e x₁ x₂) r')) ⟩
          map _ changeQuot (map _ [_] (coalg-νF x₂))
          ≡⟨ sym (map∘ _) ⟩
          map _ (changeQuot ∘ [_]) (coalg-νF x₂)
          ≡⟨ refl ⟩
          map _ [_] (coalg-νF x₂)
          ∎
  
        S' : Precong (ℓ-suc ℓ) νF-Coalg squash/ ℓ
        S' = R' , p' , q'
  
        r' : isReflRel R'
        r' z = equivFun (e z z) (r z)
  
        s' : R' x y
        s' = equivFun (e x y) s
  
    uniq-mor : is[ ℓ ]Simple νF-Coalg squash/
    uniq-mor = isPrecongSimpleL→isSimple isPrecongSimpleL-νF
  
    setuterminal : is[ ℓ ]Terminal νF-Coalg squash/
    setuterminal C .fst =
      CoalgHom∘ {C = C}{wνF-Coalg}{νF-Coalg}
                (coalg-MaxQuot-CoalgHom _ _ squash₂)
                (unfold-CoalgHom C)
    setuterminal C .snd = uniq-mor _ _



