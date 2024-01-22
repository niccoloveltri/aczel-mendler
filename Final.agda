{-# OPTIONS --cubical #-}

module Final where

open import Utilities
open import Multiset
open import SetBased
open import Complete
import Coalgebras

-- ==============================================

-- FROM COMPLETENESS TO FINALITY

-- If a (ℓs,ℓl)-set-based functor F has an (ℓs,ℓl)-complete coalgebra,
-- then this is also ℓl-final,

module CompleteToFinal
  {ℓz ℓs ℓl} (Fun : Functor ℓz)
             (SB : isSetBased ℓs ℓl Fun)
             (D : Coalgebras.Coalg Fun ℓl)
             (setD : isSet ⟨ D ⟩)
             (completeD : Coalgebras.isComplete Fun ℓs D) where 

  open Functor Fun
  open Coalgebras Fun  
  
  complete→final : isFinal D
  complete→final C = fCH , isFinal-f
    where
      open SubCoalg Fun SB C

      uCH : (Y : M ℓs ⟨ C ⟩) → CoalgHom (C^ Y) D
      uCH Y = completeD (C^ Y) .fst

      u : (Y : M ℓs ⟨ C ⟩) → ⟨ C^ Y ⟩ → ⟨ D ⟩
      u Y = uCH Y .fst

      f : ⟨ C ⟩ → ⟨ D ⟩
      f a = u (ηM a) (up (ηM a) tt*)

      eq-f' : ∀ a x →
        uCH (ηM (ι (Σnext (ηM a)) x))
          ≡ CoalgHom∘ {C'' = D} (uCH (ηM a)) (C^lift (ηM a) (ηM x) .fst)
      eq-f' a x = completeD (C^ (ηM (ι (Σnext (ηM a)) x))) .snd _

      eq-f : ∀ a → f ∘ ι (Σnext (ηM a)) ≡ u (ηM a)
      eq-f a = funExt (λ x → 
        u (ηM (ι (Σnext (ηM a)) x)) (up (ηM (ι (Σnext (ηM a)) x)) tt*)
        ≡⟨ (λ i → eq-f' a x i .fst (up (ηM (ι (Σnext (ηM a)) x)) tt*)) ⟩
        u (ηM a) (C^lift (ηM a) (ηM x) .fst .fst (up (ηM (ι (Σnext (ηM a)) x)) tt*))
        ≡⟨ refl ⟩
        u (ηM a) x
        ∎)

      coalgHom-f' : ∀ a → map f (coalg C a) ≡ coalg D (f a)
      coalgHom-f' a =
        map f (coalg C a)
        ≡⟨ cong (map f) (sym (up-eq (ηM a) tt*)) ⟩
        map f (map (ι (Σnext (ηM a))) (coalg (C^ (ηM a)) (up (ηM a) tt*)))
        ≡⟨ sym (map∘ _) ⟩
        map (f ∘ ι (Σnext (ηM a))) (coalg (C^ (ηM a)) (up (ηM a) tt*))
        ≡⟨ cong (λ g → map g (coalg (C^ (ηM a)) (up (ηM a) tt*))) (eq-f a) ⟩
        map (u (ηM a)) (coalg (C^ (ηM a)) (up (ηM a) tt*))
        ≡⟨ (λ i → uCH (ηM a) .snd i (up (ηM a) tt*)) ⟩
        coalg D (u (ηM a) (up (ηM a) tt*))
        ≡⟨ refl ⟩
        coalg D (f a)
        ∎

      coalgHom-f : map f ∘ coalg C ≡ coalg D ∘ f
      coalgHom-f = funExt coalgHom-f'

      fCH : CoalgHom C D
      fCH = f , coalgHom-f

      isFinal-f' : (v : CoalgHom C D) (a : ⟨ C ⟩)
        → uCH (ηM a) ≡ CoalgHom∘ {C'' = D} v (C^Hom (ηM a))
      isFinal-f' v a = completeD (C^ (ηM a)) .snd _

      isFinal-f : (v : CoalgHom C D) → fCH ≡ v
      isFinal-f v =
        Σ≡Prop (λ _ → isSetΠ (λ _ → isSetF setD) _ _)
               (funExt (λ a → 
                 u (ηM a) (up (ηM a) tt*)
                 ≡⟨ (λ i → isFinal-f' v a i .fst (up (ηM a) tt*)) ⟩
                 v .fst (ι (Σnext (ηM a)) (up (ηM a) tt*))
                 ≡⟨ refl ⟩
                 v .fst a
                 ∎))

-- ==============================================

-- THE GENERAL FINAL COALGEBRA THEOREM

-- Assuming propositional resizing, 
-- every (ℓs,ℓs+1)-set-based functor F has a ℓs-final coalgebra.

-- The theorem comes in two forms, depending on whether
-- F : ∀{ℓ} → Type ℓ → Type (ℓ-max ℓs ℓ)
-- or
-- F : ∀{ℓ} → Type ℓ → Type (ℓ-max (ℓ-suc ℓs) ℓ)

module FinalitySmall {ℓ} (Fun : Functor ℓ)
                    (SB : isSetBased ℓ (ℓ-suc ℓ) Fun)
                    (PR : PropRes ℓ (ℓ-suc ℓ)) where 

  open Coalgebras Fun  
  open import Complete
  open CompleteSmall ℓ Fun
  open CompleteWithPropResizing PR
  open CompleteToFinal Fun SB νF-Coalg squash/ complete

  final : isFinal νF-Coalg
  final = complete→final

module FinalityLarge {ℓ} (Fun : Functor (ℓ-suc ℓ))
                    (SB : isSetBased ℓ (ℓ-suc ℓ) Fun)
                    (PR : PropRes ℓ (ℓ-suc ℓ)) where 

  open Coalgebras Fun  
  open import Complete
  open CompleteLarge ℓ Fun
  open CompleteWithPropResizing PR
  open CompleteToFinal Fun SB νF-Coalg squash/ complete

  final : isFinal νF-Coalg
  final = complete→final


