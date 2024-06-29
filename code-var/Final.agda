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
             (completeD : Coalgebras.isComplete Fun ℓs D setD) where 

  open Functor Fun
  open Coalgebras Fun  
  
  complete→final : isFinalSet D setD
  complete→final C setC = fCH , isFinal-f
    where
      open SubCoalg Fun SB C setC

      uCH : (Y : M ℓs ⟨ C ⟩) → CoalgHom (C^ Y) D setD
      uCH Y = completeD (C^ Y) .fst

      u : (Y : M ℓs ⟨ C ⟩) → ⟨ C^ Y ⟩ → ⟨ D ⟩
      u Y = uCH Y .fst

      f : ⟨ C ⟩ → ⟨ D ⟩
      f a = u (ηM a) (up (ηM a) tt*)

      eq-f' : (x : ⟨ C ⟩) (a : ⟨ C^ (ηM x) ⟩) →
        uCH (ηM (C^Hom (ηM x) .fst a))
          ≡ CoalgHom∘ {C'' = D} (uCH (ηM x)) (C^lift (ηM x) (ηM a) .fst)
      eq-f' x a = completeD (C^ (ηM (C^Hom (ηM x) .fst a))) .snd _

      eq-f : ∀ x → f ∘ C^Hom (ηM x) .fst ≡ u (ηM x)
      eq-f x = funExt (λ a →
        let a' = C^Hom (ηM x) .fst a in
        u (ηM a') (up (ηM a') tt*)
        ≡⟨ (λ i → eq-f' x a i .fst (up (ηM a') tt*)) ⟩
        u (ηM x) (C^lift (ηM x) (ηM a) .fst .fst (up (ηM a') tt*))
        ≡⟨ refl ⟩
        u (ηM x) a
        ∎)

      coalgHom-f' : ∀ a → map setD f (coalg C a) ≡ coalg D (f a)
      coalgHom-f' a =
        map _ f (coalg C a)
        ≡⟨ cong (map _ f) (sym (up-eq (ηM a) tt*)) ⟩
        map _ f (map _ (ι (Σnext (ηM a))) (coalg (C^ (ηM a)) (up (ηM a) tt*)))
        ≡⟨ sym (map∘ _) ⟩
        map _ (f ∘ ι (Σnext (ηM a))) (coalg (C^ (ηM a)) (up (ηM a) tt*))
        ≡⟨ cong (λ g → map _ g (coalg (C^ (ηM a)) (up (ηM a) tt*))) (eq-f a) ⟩
        map _ (u (ηM a)) (coalg (C^ (ηM a)) (up (ηM a) tt*))
        ≡⟨ (λ i → uCH (ηM a) .snd i (up (ηM a) tt*)) ⟩
        coalg D (u (ηM a) (up (ηM a) tt*))
        ≡⟨ refl ⟩
        coalg D (f a)
        ∎

      coalgHom-f : map _ f ∘ coalg C ≡ coalg D ∘ f
      coalgHom-f = funExt coalgHom-f'

      fCH : CoalgHom C D setD
      fCH = f , coalgHom-f

      isFinal-f' : (v : CoalgHom C D setD) (a : ⟨ C ⟩)
        → uCH (ηM a) ≡ CoalgHom∘ {C'' = D} v (C^Hom (ηM a))
      isFinal-f' v a = completeD (C^ (ηM a)) .snd _

      isFinal-f : (v : CoalgHom C D setD) → fCH ≡ v
      isFinal-f v =
        Σ≡Prop (λ _ → isSetΠ (λ _ → isSetF) _ _)
               (funExt (λ a → 
                 u (ηM a) (up (ηM a) tt*)
                 ≡⟨ (λ i → isFinal-f' v a i .fst (up (ηM a) tt*)) ⟩
                 v .fst (C^Hom (ηM a) .fst (up (ηM a) tt*))
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

  final : isFinalSet νF-Coalg _
  final = complete→final

module FinalityLarge {ℓ} (Fun : Functor (ℓ-suc ℓ))
                    (SB : isSetBased ℓ (ℓ-suc ℓ) Fun)
                    (PR : PropRes ℓ (ℓ-suc ℓ)) where 

  open Coalgebras Fun  
  open import Complete
  open CompleteLarge ℓ Fun
  open CompleteWithPropResizing PR
  open CompleteToFinal Fun SB νF-Coalg squash/ complete

  final : isFinalSet νF-Coalg _
  final = complete→final


