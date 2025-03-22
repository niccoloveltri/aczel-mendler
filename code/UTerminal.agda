{-# OPTIONS --cubical #-}

module UTerminal where

open import Utilities

-- ==============================================

-- Construction of the U-terminal coalgebra, assuming propositional
-- resizing.
-- There are two versions, depending of whether the functor F is
-- of the form
-- 1) F : ∀{ℓ} → Type ℓ → Type (ℓ-max υ ℓ)
--    in module UTerminalSmall      
-- 2) F : ∀{ℓ} → Type ℓ → Type (ℓ-max (ℓ-suc υ) ℓ)
--    in module UTerminalLarge

module UTerminalSmall (υ : Level) (Fun : Functor υ) where

  open Functor Fun
  open import Coalgebras Fun
  open import WeaklyUTerminal Fun υ
  open import Precongruences Fun

-- The ℓ-uterminal coalgebra is the set-quotient of the weakly final
-- coalgebra by the maximal precongruence.

  νF : Type (ℓ-suc υ)
  νF = MaxQuot _ wνF-Coalg υ

  coalg-νF : νF → F νF
  coalg-νF = coalg-MaxQuot _ wνF-Coalg

  νF-Coalg : Coalg (ℓ-suc υ)
  νF-Coalg = MaxQuot-Coalg _ wνF-Coalg υ

  isPrecongSimpleL : Type (ℓ-suc (ℓ-suc υ))
  isPrecongSimpleL = is[_]PrecongSimple _ νF-Coalg (ℓ-suc υ)

  isPrecongSimpleS : Type (ℓ-suc υ)
  isPrecongSimpleS = is[_]PrecongSimple _ νF-Coalg υ

-- Proof:

-- For each coalgebra C, there is a coalgebra morphism to νF which factors to wνF.
-- Therefore, to prove that νF is uterminal is enough to show that it is strongly extensional. 
-- We know that every s-extensional coalgebra is strongly extensional.

  isPrecongSimpleL→isSimple : isPrecongSimpleL → is[ υ ]Simple νF-Coalg
  isPrecongSimpleL→isSimple = isPrecongSimple→isSimple (ℓ-suc υ) νF-Coalg squash/

-- And νF, being the quotient of a coalgebra by the largest preconruence, is s-extensional.
  open import MaxQuotExt Fun _ wνF-Coalg
  isPrecongSimpleS-νF : isPrecongSimpleS
  isPrecongSimpleS-νF = isPrecongSimple-MaxQuot υ

-- To put everything together we need propositional resizing.

-- Since we know that νF is s-extensional wrt. υ-valued
-- precongruences, but theorem sExtL→isSimple requires s-extensionality
-- wrt. (υ + 1)-valued precongruences.
  module UTerminalWithPropResizing (PR : PropRes υ (ℓ-suc υ)) where

    isPrecongSimpleL-νF : isPrecongSimpleL
    isPrecongSimpleL-νF x y S@(R , p , q) r s = isPrecongSimpleS-νF x y S' r' s'
      where          
        R' : νF → νF → Type υ
        R' x₁ x₂ = PR (R x₁ x₂) (p x₁ x₂) .fst

        e : ∀ x₁ x₂ → R x₁ x₂ ≃ R' x₁ x₂
        e x₁ x₂ = PR (R x₁ x₂) (p x₁ x₂) .snd
  
        p' : isPropRel R'
        p' x₁ x₂ = isOfHLevelRespectEquiv 1 (e x₁ x₂) (p x₁ x₂)
        
        open EquivQuot _ R R' e
  
        q' :  isPrecong (ℓ-suc υ) νF-Coalg R'
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
  
        S' : Precong (ℓ-suc υ) νF-Coalg υ
        S' = R' , p' , q'
  
        r' : isReflRel R'
        r' z = equivFun (e z z) (r z)
  
        s' : R' x y
        s' = equivFun (e x y) s
  
    uniq-mor : is[ υ ]Simple νF-Coalg
    uniq-mor = isPrecongSimpleL→isSimple isPrecongSimpleL-νF
  
    uterminal : is[ υ ]Terminal νF-Coalg
    uterminal C .fst =
      CoalgHom∘ {C = C}{wνF-Coalg}{νF-Coalg}
                (coalg-MaxQuot-CoalgHom _ _)
                (unfold-CoalgHom C)
    uterminal C .snd = uniq-mor _ _

-- =====================================================

module UTerminalLarge (υ : Level) (Fun : Functor (ℓ-suc υ)) where

  open Functor Fun
  open import Coalgebras Fun
  open import WeaklyUTerminal Fun υ
  open import Precongruences Fun

-- The υ-uterminal coalgebra is the set-quotient of the weakly final
-- coalgebra by the maximal precongruence.

  νF : Type (ℓ-suc υ)
  νF = MaxQuot _ wνF-Coalg υ

  coalg-νF : νF → F νF
  coalg-νF = coalg-MaxQuot _ wνF-Coalg

  νF-Coalg : Coalg (ℓ-suc υ)
  νF-Coalg = MaxQuot-Coalg _ wνF-Coalg υ

  isPrecongSimpleL : Type (ℓ-suc (ℓ-suc υ))
  isPrecongSimpleL = is[_]PrecongSimple _ νF-Coalg (ℓ-suc υ)

  isPrecongSimpleS : Type (ℓ-suc υ)
  isPrecongSimpleS = is[_]PrecongSimple _ νF-Coalg υ

-- Proof:

-- For each coalgebra C, there is a coalgebra morphism to νF which factors to wνF.
-- Therefore, to prove that νF is uterminal is enough to show that it is strongly extensional. 
-- We know that every s-extensional coalgebra is strongly extensional.

  isPrecongSimpleL→isSimple : isPrecongSimpleL → is[ υ ]Simple νF-Coalg
  isPrecongSimpleL→isSimple = isPrecongSimple→isSimple (ℓ-suc υ) νF-Coalg squash/

-- And νF, being the quotient of a coalgebra by the largest preconruence, is s-extensional.
  open import MaxQuotExt Fun _ wνF-Coalg
  isPrecongSimpleS-νF : isPrecongSimpleS
  isPrecongSimpleS-νF = isPrecongSimple-MaxQuot υ

-- To put everything together we need propositional resizing.

-- Since we know that νF is s-extensional wrt. υ-valued
-- precongruences, but theorem isPrecongSimpleL→isSimple requires s-extensionality
-- wrt. (υ + 1)-valued precongruences.
  module UTerminalWithPropResizing (PR : PropRes υ (ℓ-suc υ)) where

    isPrecongSimpleL-νF : isPrecongSimpleL
    isPrecongSimpleL-νF x y S@(R , p , q) r s = isPrecongSimpleS-νF x y S' r' s'
      where          
        R' : νF → νF → Type υ
        R' x₁ x₂ = PR (R x₁ x₂) (p x₁ x₂) .fst

        e : ∀ x₁ x₂ → R x₁ x₂ ≃ R' x₁ x₂
        e x₁ x₂ = PR (R x₁ x₂) (p x₁ x₂) .snd
  
        p' : isPropRel R'
        p' x₁ x₂ = isOfHLevelRespectEquiv 1 (e x₁ x₂) (p x₁ x₂)
        
        open EquivQuot _ R R' e
  
        q' :  isPrecong (ℓ-suc υ) νF-Coalg R'
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
  
        S' : Precong (ℓ-suc υ) νF-Coalg υ
        S' = R' , p' , q'
  
        r' : isReflRel R'
        r' z = equivFun (e z z) (r z)
  
        s' : R' x y
        s' = equivFun (e x y) s
  
    uniq-mor : is[ υ ]Simple νF-Coalg
    uniq-mor = isPrecongSimpleL→isSimple isPrecongSimpleL-νF
  
    uterminal : is[ υ ]Terminal νF-Coalg
    uterminal C .fst =
      CoalgHom∘ {C = C}{wνF-Coalg}{νF-Coalg}
                (coalg-MaxQuot-CoalgHom _ _)
                (unfold-CoalgHom C)
    uterminal C .snd = uniq-mor _ _



