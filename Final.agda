{-# OPTIONS --cubical #-}


module Final where

open import Utilities
open import Cubical.Foundations.Everything
open import Cubical.HITs.SetQuotients
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Multiset
import Coalgebras

module ToFinal (Fun : Functor) {ℓs ℓl} (SB : isSetBased Fun ℓs ℓl)
               (D : Coalgebras.Coalg Fun ℓl)
               (completeD : Coalgebras.isComplete Fun ℓs D) where 

  open Functor Fun
  open Coalgebras Fun  
  
  complete→final : isFinal D
  complete→final C = fCH , isFinal-f
    where
      open SubCoalg Fun SB C

      uCH : (Y : M ℓs ⟨ C ⟩) → CoalgHom (subcoalg Y) D
      uCH Y = completeD (subcoalg Y) .fst

      u : (Y : M ℓs ⟨ C ⟩) → ⟨ subcoalg Y ⟩ → ⟨ D ⟩
      u Y = uCH Y .fst

      f : ⟨ C ⟩ → ⟨ D ⟩
      f a = u (ηM a) (up (ηM a) tt*)

      eq-f' : ∀ a x →
        uCH (ηM (ι (lim (ηM a)) x)) ≡ CoalgHom∘ {C'' = D} (uCH (ηM a)) (subcoalgComp (ηM a) (ηM x) .fst)
      eq-f' a x = completeD (subcoalg (ηM (ι (lim (ηM a)) x))) .snd _

      eq-f : ∀ a → f ∘ ι (lim (ηM a)) ≡ u (ηM a)
      eq-f a = funExt (λ x → 
        u (ηM (ι (lim (ηM a)) x)) (up (ηM (ι (lim (ηM a)) x)) tt*)
        ≡⟨ (λ i → eq-f' a x i .fst (up (ηM (ι (lim (ηM a)) x)) tt*)) ⟩
        u (ηM a) (subcoalgComp (ηM a) (ηM x) .fst .fst (up (ηM (ι (lim (ηM a)) x)) tt*))
        ≡⟨ refl ⟩
        u (ηM a) x
        ∎)

      coalgHom-f' : ∀ a → map f (coalg C a) ≡ coalg D (f a)
      coalgHom-f' a =
        map f (coalg C a)
        ≡⟨ cong (map f) (sym (up-eq (ηM a) tt*)) ⟩
        map f (map (ι (lim (ηM a))) (coalg (subcoalg (ηM a)) (up (ηM a) tt*)))
        ≡⟨ sym (map∘ _) ⟩
        map (f ∘ ι (lim (ηM a))) (coalg (subcoalg (ηM a)) (up (ηM a) tt*))
        ≡⟨ cong (λ g → map g (coalg (subcoalg (ηM a)) (up (ηM a) tt*))) (eq-f a) ⟩
        map (u (ηM a)) (coalg (subcoalg (ηM a)) (up (ηM a) tt*))
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
        → uCH (ηM a) ≡ CoalgHom∘ {C'' = D} v (subcoalgHom (ηM a))
      isFinal-f' v a = completeD (subcoalg (ηM a)) .snd _

      isFinal-f : (v : CoalgHom C D) → fCH ≡ v
      isFinal-f v =
        Σ≡Prop (λ _ → isSetΠ (λ _ → isSetF) _ _)
               (funExt (λ a → 
                 u (ηM a) (up (ηM a) tt*)
                 ≡⟨ (λ i → isFinal-f' v a i .fst (up (ηM a) tt*)) ⟩
                 v .fst (ι (lim (ηM a)) (up (ηM a) tt*))
                 ≡⟨ refl ⟩
                 v .fst a
                 ∎))


--  lemma3-4' : (Y : M ℓs ⟨ C ⟩)
--    → Σ[ A₀ ∈ M ℓs ⟨ C ⟩ ] ((a : ⟨ A₀ ⟩) → Σ[ a' ∈ F ⟨ A₀ ⟩ ] map (ι A₀) a' ≡ coalg C (ι A₀ a))

{-
  lemma3-3 : (Y : M ℓs ⟨ C ⟩)
    → Σ[ Y' ∈ M ℓs ⟨ C ⟩ ] ((a : ⟨ Y ⟩) → Σ[ a' ∈ F ⟨ Y' ⟩ ] map (ι Y') a' ≡ coalg C (ι Y a))
  lemma3-3 Y = Y' , pY'
    where
      Y' : M ℓs ⟨ C ⟩
      Y' = bindM coalgM Y

      pY' : (a : ⟨ Y ⟩) → Σ[ a' ∈ F ⟨ Y' ⟩ ] map (ι Y') a' ≡ coalg C (ι Y a)
      pY' a = map (a ,_) (SB (coalg C (ι Y a)) .snd .fst) ,
        sym (map∘ _) ∙ SB (coalg C (ι Y a)) .snd .snd
-}


