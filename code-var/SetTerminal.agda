{-# OPTIONS --cubical #-}

module SetTerminal where

open import Utilities
open import Multiset
open import SetUBased
open import SetUTerminal
import Coalgebras

-- ==============================================

-- FROM U-TERMINAL TO TERMINAL

-- If a set(υ,ℓ)-based functor F has an set(υ,ℓ)-terminal coalgebra,
-- then this is also setℓ-terminal.

module SetUTerminalToSetterminal
  {ℓz υ ℓl} (Fun : Functor ℓz)
             (SB : isSetBased υ ℓl Fun)
             (D : Coalgebras.Coalg Fun ℓl)
             (setD : isSet ⟨ D ⟩)
             (setuterminalD : Coalgebras.is[_]Terminal Fun υ D setD) where 

  open Functor Fun
  open Coalgebras Fun  
  
  setuterminal→setterminal : isTerminalSet D setD
  setuterminal→setterminal C setC = fCH , isSetterminal-f
    where
      open SubCoalg Fun SB C setC

      uCH : (Y : P∞ υ ⟨ C ⟩) → CoalgHom (C^ Y) D setD
      uCH Y = setuterminalD (C^ Y) .fst

      u : (Y : P∞ υ ⟨ C ⟩) → ⟨ C^ Y ⟩ → ⟨ D ⟩
      u Y = uCH Y .fst

      f : ⟨ C ⟩ → ⟨ D ⟩
      f a = u (ηP∞ a) (up (ηP∞ a) tt*)

      eq-f' : (x : ⟨ C ⟩) (a : ⟨ C^ (ηP∞ x) ⟩) →
        uCH (ηP∞ (C^Hom (ηP∞ x) .fst a))
          ≡ CoalgHom∘ {C'' = D} (uCH (ηP∞ x)) (C^lift (ηP∞ x) (ηP∞ a) .fst)
      eq-f' x a = setuterminalD (C^ (ηP∞ (C^Hom (ηP∞ x) .fst a))) .snd _

      eq-f : ∀ x → f ∘ C^Hom (ηP∞ x) .fst ≡ u (ηP∞ x)
      eq-f x = funExt (λ a →
        let a' = C^Hom (ηP∞ x) .fst a in
        u (ηP∞ a') (up (ηP∞ a') tt*)
        ≡⟨ (λ i → eq-f' x a i .fst (up (ηP∞ a') tt*)) ⟩
        u (ηP∞ x) (C^lift (ηP∞ x) (ηP∞ a) .fst .fst (up (ηP∞ a') tt*))
        ≡⟨ refl ⟩
        u (ηP∞ x) a
        ∎)

      coalgHom-f' : ∀ a → map setD f (coalg C a) ≡ coalg D (f a)
      coalgHom-f' a =
        map _ f (coalg C a)
        ≡⟨ cong (map _ f) (sym (up-eq (ηP∞ a) tt*)) ⟩
        map _ f (map _ (ι (Σnext (ηP∞ a))) (coalg (C^ (ηP∞ a)) (up (ηP∞ a) tt*)))
        ≡⟨ sym (map∘ _) ⟩
        map _ (f ∘ ι (Σnext (ηP∞ a))) (coalg (C^ (ηP∞ a)) (up (ηP∞ a) tt*))
        ≡⟨ cong (λ g → map _ g (coalg (C^ (ηP∞ a)) (up (ηP∞ a) tt*))) (eq-f a) ⟩
        map _ (u (ηP∞ a)) (coalg (C^ (ηP∞ a)) (up (ηP∞ a) tt*))
        ≡⟨ (λ i → uCH (ηP∞ a) .snd i (up (ηP∞ a) tt*)) ⟩
        coalg D (u (ηP∞ a) (up (ηP∞ a) tt*))
        ≡⟨ refl ⟩
        coalg D (f a)
        ∎

      coalgHom-f : map _ f ∘ coalg C ≡ coalg D ∘ f
      coalgHom-f = funExt coalgHom-f'

      fCH : CoalgHom C D setD
      fCH = f , coalgHom-f

      isSetterminal-f' : (v : CoalgHom C D setD) (a : ⟨ C ⟩)
        → uCH (ηP∞ a) ≡ CoalgHom∘ {C'' = D} v (C^Hom (ηP∞ a))
      isSetterminal-f' v a = setuterminalD (C^ (ηP∞ a)) .snd _

      isSetterminal-f : (v : CoalgHom C D setD) → fCH ≡ v
      isSetterminal-f v =
        Σ≡Prop (λ _ → isSetΠ (λ _ → isSetF) _ _)
               (funExt (λ a → 
                 u (ηP∞ a) (up (ηP∞ a) tt*)
                 ≡⟨ (λ i → isSetterminal-f' v a i .fst (up (ηP∞ a) tt*)) ⟩
                 v .fst (C^Hom (ηP∞ a) .fst (up (ηP∞ a) tt*))
                 ≡⟨ refl ⟩
                 v .fst a
                 ∎))

-- ==============================================

-- THE SET-TERMINAL COALGEBRA THEOREM

-- Assuming propositional resizing, 
-- every (υ,υ+1)-set-based functor F has a set-terminal coalgebra.

-- The theorem comes in two forms, depending on whether
-- F : ∀{ℓ} → Type ℓ → Type (ℓ-max υ ℓ)
-- or
-- F : ∀{ℓ} → Type ℓ → Type (ℓ-max (ℓ-suc υ) ℓ)

module SetTerminalSmall {ℓ} (Fun : Functor ℓ)
                    (SB : isSetBased ℓ (ℓ-suc ℓ) Fun)
                    (PR : PropRes ℓ (ℓ-suc ℓ)) where 

  open Coalgebras Fun  
  open import SetUTerminal
  open SetUTerminalSmall ℓ Fun
  open SetUTerminalWithPropResizing PR
  open SetUTerminalToSetterminal Fun SB νF-Coalg squash/ setuterminal

  setterminal : isTerminalSet νF-Coalg _
  setterminal = setuterminal→setterminal

module SetTerminalLarge {ℓ} (Fun : Functor (ℓ-suc ℓ))
                    (SB : isSetBased ℓ (ℓ-suc ℓ) Fun)
                    (PR : PropRes ℓ (ℓ-suc ℓ)) where 

  open Coalgebras Fun  
  open import SetUTerminal
  open SetUTerminalLarge ℓ Fun
  open SetUTerminalWithPropResizing PR
  open SetUTerminalToSetterminal Fun SB νF-Coalg squash/ setuterminal

  setterminal : isTerminalSet νF-Coalg _
  setterminal = setuterminal→setterminal


