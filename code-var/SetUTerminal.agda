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

-- The ℓ-complete coalgebra is the set-quotient of the weakly terminal
-- coalgebra by the maximal precongruence.

  νF : Type (ℓ-suc ℓ)
  νF = MaxQuot _ wνF-Coalg squash₂ ℓ

  coalg-νF : νF → F νF
  coalg-νF = coalg-MaxQuot _ wνF-Coalg squash₂

  νF-Coalg : Coalg (ℓ-suc ℓ)
  νF-Coalg = MaxQuot-Coalg _ wνF-Coalg squash₂ ℓ

  isPrecongSimpleS : Type (ℓ-suc ℓ)
  isPrecongSimpleS = is[_]PrecongSimple _ νF-Coalg squash/ ℓ

-- Proof:

-- For each small coalgebra C, there is a coalgebra morphism to νF which factors to wνF.
-- Therefore, to prove that νF is ℓ-terminal it is enough to show that it is ℓ-simple.
-- We know that every locally ℓ-small and ℓ-precongruence simple coalgebra is ℓ-simple:

  isPrecongSimpleS→isSimple : isLocally[ ℓ ]Small νF → isPrecongSimpleS
    → is[ ℓ ]Simple νF-Coalg squash/
  isPrecongSimpleS→isSimple = isPrecongSimple×LocallySmall→isSimple (ℓ-suc ℓ) νF-Coalg squash/ squash/

-- And νF, being the quotient of a coalgebra by the largest preconruence, is ℓ-precongurence simple:
  open import MaxQuotExt Fun _ wνF-Coalg
  isPrecongSimpleS-νF : isPrecongSimpleS
  isPrecongSimpleS-νF = isPrecongSimple-MaxQuot squash₂ ℓ

-- To put everything together we need propositional resizing.
-- We know that νF is ℓ-precongruence simple, but to prove that it is also locally
-- ℓ-small requires propositional resizing.
  module SetUTerminalWithPropResizing (PR : PropRes ℓ (ℓ-suc ℓ)) where

    isLocallySmall-νF : isLocally[ ℓ ]Small νF
    isLocallySmall-νF x y = PR (x ≡ y) (squash/ x y)

    uniq-mor : is[ ℓ ]Simple νF-Coalg squash/
    uniq-mor = isPrecongSimpleS→isSimple isLocallySmall-νF isPrecongSimpleS-νF

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

-- The ℓ-complete coalgebra is the set-quotient of the weakly terminal
-- coalgebra by the maximal precongruence.

  νF : Type (ℓ-suc ℓ)
  νF = MaxQuot _ wνF-Coalg squash₂ ℓ

  coalg-νF : νF → F νF
  coalg-νF = coalg-MaxQuot _ wνF-Coalg squash₂

  νF-Coalg : Coalg (ℓ-suc ℓ)
  νF-Coalg = MaxQuot-Coalg _ wνF-Coalg squash₂ ℓ

  isPrecongSimpleS : Type (ℓ-suc ℓ)
  isPrecongSimpleS = is[_]PrecongSimple _ νF-Coalg squash/ ℓ

-- Proof:

-- For each small coalgebra C, there is a coalgebra morphism to νF which factors to wνF.
-- Therefore, to prove that νF is ℓ-terminal it is enough to show that it is ℓ-simple.
-- We know that every locally ℓ-small and ℓ-precongruence simple coalgebra is ℓ-simple:

  isPrecongSimpleS→isSimple : isLocally[ ℓ ]Small νF → isPrecongSimpleS
    → is[ ℓ ]Simple νF-Coalg squash/
  isPrecongSimpleS→isSimple =
    isPrecongSimple×LocallySmall→isSimple _ νF-Coalg squash/ squash/ 

-- And νF, being the quotient of a coalgebra by the largest preconruence, is ℓ-precongruence simple:
  open import MaxQuotExt Fun _ wνF-Coalg
  isPrecongSimpleS-νF : isPrecongSimpleS
  isPrecongSimpleS-νF = isPrecongSimple-MaxQuot squash₂ ℓ

-- To put everything together we need propositional resizing.
-- We know that νF is ℓ-precongruence simple, but to prove that it is also locally
-- ℓ-small requires propositional resizing.
  module SetUTerminalWithPropResizing (PR : PropRes ℓ (ℓ-suc ℓ)) where

    isLocallySmall-νF : isLocally[ ℓ ]Small νF
    isLocallySmall-νF x y = PR (x ≡ y) (squash/ x y)

    uniq-mor : is[ ℓ ]Simple νF-Coalg squash/
    uniq-mor = isPrecongSimpleS→isSimple isLocallySmall-νF isPrecongSimpleS-νF
  
    setuterminal : is[ ℓ ]Terminal νF-Coalg squash/
    setuterminal C .fst =
      CoalgHom∘ {C = C}{wνF-Coalg}{νF-Coalg}
                (coalg-MaxQuot-CoalgHom _ _ squash₂)
                (unfold-CoalgHom C)
    setuterminal C .snd = uniq-mor _ _



