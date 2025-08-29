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

-- The u-terminal coalgebra is the set-quotient of the weakly terminal
-- coalgebra by the maximal precongruence.

  νF : Type (ℓ-suc υ)
  νF = MaxQuot _ wνF-Coalg υ

  coalg-νF : νF → F νF
  coalg-νF = coalg-MaxQuot _ wνF-Coalg

  νF-Coalg : Coalg (ℓ-suc υ)
  νF-Coalg = MaxQuot-Coalg _ wνF-Coalg υ

  isPrecongSimpleS : Type (ℓ-suc υ)
  isPrecongSimpleS = is[_]PrecongSimple _ νF-Coalg υ

-- Proof:

-- For each small coalgebra C, there is a coalgebra morphism to νF which factors to wνF.
-- Therefore, to prove that νF is u-terminal it is enough to show that it is u-simple.
-- We know that every locally u-small and u-precongruence simple coalgebra is u-simple:

  isPrecongSimpleS→isSimple : isLocally[ υ ]Small νF → isPrecongSimpleS
    → is[ υ ]Simple νF-Coalg
  isPrecongSimpleS→isSimple =
    isPrecongSimple×LocallySmall→isSimple _ νF-Coalg squash/ 
  
-- And νF, being the quotient of a coalgebra by the largest preconruence, is u-precongruence simple.
  open import MaxQuotExt Fun _ wνF-Coalg
  isPrecongSimpleS-νF : isPrecongSimpleS
  isPrecongSimpleS-νF = isPrecongSimple-MaxQuot υ

-- To put everything together we need propositional resizing.
-- We know that νF is u-precongruence simple, but to prove that it is also locally
-- u-small requires propositional resizing.
  module UTerminalWithPropResizing (PR : PropRes υ (ℓ-suc υ)) where

    isLocallySmall-νF : isLocally[ υ ]Small νF
    isLocallySmall-νF x y = PR (x ≡ y) (squash/ x y)

    uniq-mor : is[ υ ]Simple νF-Coalg
    uniq-mor = isPrecongSimpleS→isSimple isLocallySmall-νF isPrecongSimpleS-νF
  
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

-- The υ-terminal coalgebra is the set-quotient of the weakly terminal
-- coalgebra by the maximal precongruence.

  νF : Type (ℓ-suc υ)
  νF = MaxQuot _ wνF-Coalg υ

  coalg-νF : νF → F νF
  coalg-νF = coalg-MaxQuot _ wνF-Coalg

  νF-Coalg : Coalg (ℓ-suc υ)
  νF-Coalg = MaxQuot-Coalg _ wνF-Coalg υ

  isPrecongSimpleS : Type (ℓ-suc υ)
  isPrecongSimpleS = is[_]PrecongSimple _ νF-Coalg υ

-- Proof:

-- For each small coalgebra C, there is a coalgebra morphism to νF which factors to wνF.
-- Therefore, to prove that νF is u-terminal it is enough to show that it is u-simple.
-- We know that every locally u-small and u-precongruence simple coalgebra is u-simple:

  isPrecongSimpleS→isSimple : isLocally[ υ ]Small νF → isPrecongSimpleS
    → is[ υ ]Simple νF-Coalg
  isPrecongSimpleS→isSimple =
    isPrecongSimple×LocallySmall→isSimple _ νF-Coalg squash/ 

-- And νF, being the quotient of a coalgebra by the largest preconruence, is u-precongruence simple.
  open import MaxQuotExt Fun _ wνF-Coalg
  isPrecongSimpleS-νF : isPrecongSimpleS
  isPrecongSimpleS-νF = isPrecongSimple-MaxQuot υ

-- To put everything together we need propositional resizing.
-- We know that νF is u-precongruence simple, but to prove that it is also locally
-- u-small requires propositional resizing.
  module UTerminalWithPropResizing (PR : PropRes υ (ℓ-suc υ)) where

    isLocallySmall-νF : isLocally[ υ ]Small νF
    isLocallySmall-νF x y = PR (x ≡ y) (squash/ x y)

    uniq-mor : is[ υ ]Simple νF-Coalg
    uniq-mor = isPrecongSimpleS→isSimple isLocallySmall-νF isPrecongSimpleS-νF
  
    uterminal : is[ υ ]Terminal νF-Coalg
    uterminal C .fst =
      CoalgHom∘ {C = C}{wνF-Coalg}{νF-Coalg}
                (coalg-MaxQuot-CoalgHom _ _)
                (unfold-CoalgHom C)
    uterminal C .snd = uniq-mor _ _



