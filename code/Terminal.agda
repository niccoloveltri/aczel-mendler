{-# OPTIONS --cubical #-}

module Terminal where

open import Utilities
open import Multiset
open import UBased
open import UTerminal
import Coalgebras

-- ==============================================

-- FROM U-TERMINAL TO TERMINAL

-- If a (υ,ℓ)-based functor F has an (υ,ℓ)-terminal coalgebra,
-- then this is also ℓ-terminal.

module UTerminalToTerminal
  {ℓ' υ ℓ} (Fun : Functor ℓ')
             (SB : isBased υ ℓ Fun)
             (D : Coalgebras.Coalg Fun ℓ)
             (setD : isSet ⟨ D ⟩)
             (uterminalD : Coalgebras.is[_]Terminal Fun υ D) where 

  open Functor Fun
  open Coalgebras Fun  
  
  uterminal→terminal : isTerminal D
  uterminal→terminal C = fCH , isFinal-f
    where
      open SubCoalg Fun SB C

      uCH : (Y : P∞ υ ⟨ C ⟩) → CoalgHom (C^ Y) D
      uCH Y = uterminalD (C^ Y) .fst

      u : (Y : P∞ υ ⟨ C ⟩) → ⟨ C^ Y ⟩ → ⟨ D ⟩
      u Y = uCH Y .fst

      f : ⟨ C ⟩ → ⟨ D ⟩
      f a = u (ηP∞ a) (up (ηP∞ a) tt*)

      eq-f' : ∀ a x →
        uCH (ηP∞ (ι (Σnext (ηP∞ a)) x))
          ≡ CoalgHom∘ {C'' = D} (uCH (ηP∞ a)) (C^lift (ηP∞ a) (ηP∞ x) .fst)
      eq-f' a x = uterminalD (C^ (ηP∞ (ι (Σnext (ηP∞ a)) x))) .snd _

      eq-f : ∀ a → f ∘ ι (Σnext (ηP∞ a)) ≡ u (ηP∞ a)
      eq-f a = funExt (λ x → 
        u (ηP∞ (ι (Σnext (ηP∞ a)) x)) (up (ηP∞ (ι (Σnext (ηP∞ a)) x)) tt*)
        ≡⟨ (λ i → eq-f' a x i .fst (up (ηP∞ (ι (Σnext (ηP∞ a)) x)) tt*)) ⟩
        u (ηP∞ a) (C^lift (ηP∞ a) (ηP∞ x) .fst .fst (up (ηP∞ (ι (Σnext (ηP∞ a)) x)) tt*))
        ≡⟨ refl ⟩
        u (ηP∞ a) x
        ∎)

      coalgHom-f' : ∀ a → map f (coalg C a) ≡ coalg D (f a)
      coalgHom-f' a =
        map f (coalg C a)
        ≡⟨ cong (map f) (sym (up-eq (ηP∞ a) tt*)) ⟩
        map f (map (ι (Σnext (ηP∞ a))) (coalg (C^ (ηP∞ a)) (up (ηP∞ a) tt*)))
        ≡⟨ sym (map∘ _) ⟩
        map (f ∘ ι (Σnext (ηP∞ a))) (coalg (C^ (ηP∞ a)) (up (ηP∞ a) tt*))
        ≡⟨ cong (λ g → map g (coalg (C^ (ηP∞ a)) (up (ηP∞ a) tt*))) (eq-f a) ⟩
        map (u (ηP∞ a)) (coalg (C^ (ηP∞ a)) (up (ηP∞ a) tt*))
        ≡⟨ (λ i → uCH (ηP∞ a) .snd i (up (ηP∞ a) tt*)) ⟩
        coalg D (u (ηP∞ a) (up (ηP∞ a) tt*))
        ≡⟨ refl ⟩
        coalg D (f a)
        ∎

      coalgHom-f : map f ∘ coalg C ≡ coalg D ∘ f
      coalgHom-f = funExt coalgHom-f'

      fCH : CoalgHom C D
      fCH = f , coalgHom-f

      isFinal-f' : (v : CoalgHom C D) (a : ⟨ C ⟩)
        → uCH (ηP∞ a) ≡ CoalgHom∘ {C'' = D} v (C^Hom (ηP∞ a))
      isFinal-f' v a = uterminalD (C^ (ηP∞ a)) .snd _

      isFinal-f : (v : CoalgHom C D) → fCH ≡ v
      isFinal-f v =
        Σ≡Prop (λ _ → isSetΠ (λ _ → isSetF setD) _ _)
               (funExt (λ a → 
                 u (ηP∞ a) (up (ηP∞ a) tt*)
                 ≡⟨ (λ i → isFinal-f' v a i .fst (up (ηP∞ a) tt*)) ⟩
                 v .fst (ι (Σnext (ηP∞ a)) (up (ηP∞ a) tt*))
                 ≡⟨ refl ⟩
                 v .fst a
                 ∎))

-- ==============================================

-- THE TERMINAL COALGEBRA THEOREM

-- Assuming propositional resizing, 
-- every (υ,υ+1)-based functor F has a terminal coalgebra.

-- The theorem comes in two forms, depending on whether
-- F : ∀{ℓ} → Type ℓ → Type (ℓ-max υ ℓ)
-- or
-- F : ∀{ℓ} → Type ℓ → Type (ℓ-max (ℓ-suc υ) ℓ)

module TerminalSmall {υ} (Fun : Functor υ)
                    (SB : isBased υ (ℓ-suc υ) Fun)
                    (PR : PropRes υ (ℓ-suc υ)) where 

  open Coalgebras Fun  
  open import UTerminal
  open UTerminalSmall υ Fun
  open UTerminalWithPropResizing PR
  open UTerminalToTerminal Fun SB νF-Coalg squash/ uterminal

  terminal : isTerminal νF-Coalg
  terminal = uterminal→terminal

module TerminalLarge {υ} (Fun : Functor (ℓ-suc υ))
                    (SB : isBased υ (ℓ-suc υ) Fun)
                    (PR : PropRes υ (ℓ-suc υ)) where 

  open Coalgebras Fun  
  open import UTerminal
  open UTerminalLarge υ Fun
  open UTerminalWithPropResizing PR
  open UTerminalToTerminal Fun SB νF-Coalg squash/ uterminal

  terminal : isTerminal νF-Coalg
  terminal = uterminal→terminal


