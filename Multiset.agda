{-# OPTIONS --cubical #-}


module Multiset where

open import Utilities
open import Cubical.Foundations.Everything
open import Cubical.HITs.SetQuotients
open import Cubical.Data.Sigma
open import Cubical.Data.Nat

M : ∀ {ℓl} ℓs → Type ℓl → Type (ℓ-max ℓl (ℓ-suc ℓs))
M ℓs X = Σ[ A ∈ Type ℓs ] (A → X)

ι : ∀ {ℓ₁ ℓ₂} {X : Type ℓ₁} (X' : M ℓ₂ X) → ⟨ X' ⟩ → X
ι = snd

ι-lem : ∀ {ℓ₁ ℓ₂} {X : Type ℓ₁} {A B : M ℓ₂ X} (a : ⟨ A ⟩) (eq : A ≡ B)
  → ι A a ≡ ι B (transport (cong fst eq) a)
ι-lem {A = A} a = J (λ B eq → ι A a ≡ ι B (transport (cong fst eq) a)) (λ i → ι A (transportRefl a (~ i)))

mapM : ∀{ℓl₁ ℓl₂ ℓs} {X : Type ℓl₁} {Y : Type ℓl₂}
  → (X → Y)
  → M ℓs X → M ℓs Y
mapM f (A , ιA) = A , f ∘ ιA

ηM : ∀{ℓl ℓs} {X : Type ℓl} → X → M ℓs X
ηM x = Unit* , (λ _ → x)
  
bindM : ∀{ℓl₁ ℓl₂ ℓs} {X : Type ℓl₁} {Y : Type ℓl₂}
  → (X → M ℓs Y)
  → M ℓs X → M ℓs Y
bindM f (A , ιA) = (Σ[ a ∈ A ] f (ιA a) .fst) , uncurry (λ a → f (ιA a) .snd)

bindmapM : ∀{ℓl₁ ℓl₂ ℓl₃ ℓs} {X : Type ℓl₁} {Y : Type ℓl₂} {Z : Type ℓl₃}
  → {g : Y → M ℓs Z} {f : X → Y}
  → (x : M ℓs X)
  → bindM g (mapM f x) ≡ bindM (g ∘ f) x
bindmapM x = refl  

bindM* : ∀{ℓl ℓs} {X : Type ℓl} (f : X → M ℓs X) → ℕ → M ℓs X → M ℓs X
bindM* f zero Y = Y
bindM* f (suc n) Y = bindM f (bindM* f n Y)
-- bindM* f n (bindM f Y)

bindM∞ : ∀{ℓl ℓs} {X : Type ℓl} (f : X → M ℓs X) → M ℓs X → M ℓs X
bindM∞ f Y = (Σ[ n ∈ ℕ ] bindM* f n Y .fst) , uncurry (λ n → bindM* f n Y .snd)

bindM*eq : ∀{ℓl ℓs} {X : Type ℓl} (f : X → M ℓs X) (n : ℕ) (Y : M ℓs X)
  → bindM* f (suc n) Y ≡ bindM* f n (bindM f Y)
bindM*eq f zero Y = refl
bindM*eq f (suc n) Y = cong (bindM f) (bindM*eq f n Y)

-- bindM*fun : ∀{ℓl ℓs} {X : Type ℓl} (f : X → M ℓs X) (n : ℕ) (Y : M ℓs X)
--   → ⟨ bindM* f (suc n) Y ⟩ → ⟨ bindM* f n (bindM f Y) ⟩
-- bindM*fun f zero Y x = x
-- bindM*fun f (suc n) Y (x , z) = bindM*fun f n Y x , {!!}
-- 
-- bindM*fun' : ∀{ℓl ℓs} {X : Type ℓl} (f : X → M ℓs X) (n : ℕ) (Y : M ℓs X)
--   → ⟨ bindM* f (suc n) Y ⟩ → ⟨ bindM* f n (bindM f Y) ⟩
-- bindM*fun' f n Y x = transport (cong fst (bindM*eq f n Y)) x
-- 
-- bindM*eq' : ∀{ℓl ℓs} {X : Type ℓl} (f : X → M ℓs X) (n : ℕ) (Y : M ℓs X)
--   → (x : ⟨ bindM* f (suc n) Y ⟩)
--   → ι (bindM* f (suc n) Y) x ≡ ι (bindM* f n (bindM f Y)) {!x .fst!}


isSetBased : Functor → ∀ ℓs ℓl → Type (ℓ-suc (ℓ-max ℓs ℓl))
isSetBased Fun ℓs ℓl =
  let open Functor Fun in
  {X : Type ℓl} (x : F X) → Σ[ X' ∈ M ℓs X ] Σ[ x₀ ∈ F ⟨ X' ⟩ ] map (ι X') x₀ ≡ x

--isSetBasedM : ∀ ℓs ℓl {X : Type ℓl} (x : M ℓs X) → Σ[ X' ∈ M ℓs X ] Σ[ x₀ ∈ M ℓs ⟨ X' ⟩ ] mapM (ι X') x₀ ≡ x
--isSetBasedM ℓs ℓl x@(A , ιA) = x , (A , λ a → a) , refl

import Coalgebras

module SubCoalg (Fun : Functor) {ℓs ℓl} (SB : isSetBased Fun ℓs ℓl) (C : Coalgebras.Coalg Fun ℓl) where 

  open Functor Fun
  open Coalgebras Fun

  map-lem : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {X : A → Type ℓ'} {Y : Type ℓ''}
    → {a : A} {f : X a → Y} {x : F (X a)} 
    → {a' : A} (eq : a ≡ a')
    → {f' : X a' → Y} (eqf : ∀ x → f x ≡ f' (transport (cong X eq) x)) 
    → {x' : F (X a')} (eqx : PathP (λ i → F (X (eq i))) x x') 
    → map f x ≡ map f' x'
  map-lem {X = X}{Y} {a = a}{f}{x} = 
    J (λ a' eq → {f' : X a' → Y} (eqf : ∀ x → f x ≡ f' (transport (cong X eq) x)) 
               → {x' : F (X a')} (eqx : PathP (λ i → F (X (eq i))) x x') 
               → map f x ≡ map f' x')
      (λ {f'} eqf → cong₂ map (funExt eqf ∙ funExt (λ z → cong f' (transportRefl z))))


  elems : {X : Type ℓl} → F X → M ℓs X
  elems x = SB x .fst

  index : {X : Type ℓl} (x : F X) → F ⟨ elems x ⟩
  index x = SB x .snd .fst

  index-eq : {X : Type ℓl} (x : F X) → map (ι (elems x)) (index x) ≡ x
  index-eq x = SB x .snd .snd

  coalgM : ⟨ C ⟩ → M ℓs ⟨ C ⟩
  coalgM x = elems (coalg C x)

  next : M ℓs ⟨ C ⟩ → M ℓs ⟨ C ⟩
  next = bindM coalgM

  inext : ℕ → M ℓs ⟨ C ⟩ → M ℓs ⟨ C ⟩
  inext n = bindM* coalgM n

  lim : M ℓs ⟨ C ⟩ → M ℓs ⟨ C ⟩
  lim = bindM∞ coalgM


{-
  Let Y' = bindM coalgM Y

  ⟨ Y ⟩ ------> F ⟨ Y' ⟩
    |             |
    |             |
    V             V
  ⟨ C ⟩ ------> F ⟨ C ⟩ 
-}

  pick : (Y : M ℓs ⟨ C ⟩) → ⟨ Y ⟩ → F ⟨ next Y ⟩
  pick Y a = map (a ,_) (index (coalg C (ι Y a)))

  lemma3-3 : (Y : M ℓs ⟨ C ⟩) (a : ⟨ Y ⟩)
    → Σ[ a' ∈ F ⟨ next Y ⟩ ] map (ι (next Y)) a' ≡ coalg C (ι Y a)
  lemma3-3 Y a = 
    pick Y a , 
    sym (map∘ _) ∙ SB (coalg C (ι Y a)) .snd .snd

{-
  ⟨ Yₙ ⟩ ------> F ⟨ Yₛₙ ⟩
    |             |
    |             |
    V             V
  ⟨ C ⟩ ------> F ⟨ C ⟩ 
-}

  lemma3-3* : (Y : M ℓs ⟨ C ⟩) (n : ℕ) (a : ⟨ inext n Y ⟩)
    → Σ[ a' ∈ F ⟨ inext (suc n) Y ⟩ ]
         map (ι (inext (suc n) Y)) a' ≡ coalg C (ι (inext n Y) a)
  lemma3-3* Y n = lemma3-3 (inext n Y)
  --lemma3-3 (bindM* coalgM n Y)

{-
  ⟨ ∪ₙYₙ ⟩ ------> F ⟨ ∪ₙYₙ ⟩
    |             |
    |             |
    V             V
  ⟨ C ⟩ ------> F ⟨ C ⟩ 
-}

  subcoalg : M ℓs ⟨ C ⟩ → Coalg ℓs
  subcoalg Y = A₀ , coalgA₀
    where
      A₀ = ⟨ lim Y ⟩
      
      coalgA₀ : A₀ → F A₀
      coalgA₀ (n , a) = map (λ y → suc n , y) (lemma3-3* Y n a .fst)

  subcoalgHom : (Y : M ℓs ⟨ C ⟩) → CoalgHom (subcoalg Y) C
  subcoalgHom Y = f , coalgHom-f
    where
      f : ⟨ subcoalg Y ⟩ → ⟨ C ⟩
      f (n , a) = ι (inext n Y) a

      coalgHom-f : map f ∘ coalg (subcoalg Y) ≡ coalg C ∘ f
      coalgHom-f = funExt (λ x → sym (map∘ _) ∙ lemma3-3* Y (fst x) (snd x) .snd) 

  up : (Y : M ℓs ⟨ C ⟩) → ⟨ Y ⟩ → ⟨ subcoalg Y ⟩
  up Y y = 0 , y

  up-eq : (Y : M ℓs ⟨ C ⟩) (y : ⟨ Y ⟩)
    → map (subcoalgHom Y .fst) (coalg (subcoalg Y) (up Y y)) ≡ coalg C (ι Y y)
  up-eq Y y = funExt⁻ (subcoalgHom Y .snd) (0 , y)
  
  lemma3-4 : (Y : M ℓs ⟨ C ⟩)
    → Σ[ C₀ ∈ Coalg ℓs ] CoalgHom C₀ C × (⟨ Y ⟩ → ⟨ C₀ ⟩)
  lemma3-4 Y = subcoalg Y , subcoalgHom Y , up Y

  subcoalgComp : (Y : M ℓs ⟨ C ⟩) (Z : M ℓs ⟨ subcoalg Y ⟩)
    → Σ[ h ∈ CoalgHom (subcoalg (mapM (subcoalgHom Y .fst) Z)) (subcoalg Y) ]
         ∀ z → ι (lim (mapM (subcoalgHom Y .fst) Z)) z ≡ ι (lim Y) (h .fst z)
  subcoalgComp Y Z = (h , coalgHom-h) , hι
    where
      Z' = mapM (subcoalgHom Y .fst) Z

      h' : (n : ℕ) (z : ⟨ inext n Z' ⟩)
        → Σ[ n' ∈ ℕ ] Σ[ z' ∈ ⟨ inext n' Y ⟩ ] ι (inext n Z') z ≡ ι (inext n' Y) z'
      h' zero z = ι Z z .fst , ι Z z .snd , refl
      h' (suc n) (z , zₛₙ) = suc n' , (z' , zₛₙ') , eq'
        where
          n' = h' n z .fst
          z' = h' n z .snd .fst
          zₛₙ' = transport (λ i → coalgM (h' n z .snd .snd i) .fst) zₛₙ
          
          eq' : ι (coalgM (ι (inext n Z') z)) zₛₙ ≡ ι (coalgM (ι (inext n' Y) z')) zₛₙ'
          eq' = ι-lem zₛₙ (λ i → coalgM (h' n z .snd .snd i))


      h : ⟨ subcoalg Z' ⟩ → ⟨ subcoalg Y ⟩
      h (n , z) = h' n z .fst , h' n z .snd .fst

      hι : ∀ z → ι (lim Z') z ≡ ι (lim Y) (h z)
      hι (n , z) = h' n z .snd .snd

      coalgHom-h' : ∀ z → map h (coalg (subcoalg Z') z) ≡ coalg (subcoalg Y) (h z)
      coalgHom-h' (n , z) =
        sym (map∘ _) ∙ sym (map∘ _)
        ∙ map-lem {X = λ a → ⟨ elems (coalg C a) ⟩}
                   (hι (n , z))
                   (λ _ → refl)
                   (λ i → index (coalg C (hι (n , z) i)))
        ∙ map∘ _

      coalgHom-h : map h ∘ coalg (subcoalg (mapM (subcoalgHom Y .fst) Z)) ≡ coalg (subcoalg Y) ∘ h
      coalgHom-h = funExt coalgHom-h'

--       h : ⟨ subcoalg (mapM (subcoalgHom Y .fst) Z) ⟩ → ⟨ subcoalg Y ⟩  --⟨ bindM∞ coalgM (mapM (subcoalgHom Y .fst) Z) ⟩ → ⟨ bindM∞ coalgM Y ⟩
--       h-eq : (z : ⟨ subcoalg (mapM (subcoalgHom Y .fst) Z) ⟩)
--         → ι (bindM* coalgM (z .fst) (mapM (subcoalgHom Y .fst) Z)) (z .snd) ≡ ι (bindM* coalgM (h z .fst) Y) (h z .snd)
-- 
--       h (zero , z₀) = ι Z z₀
--       h (suc n , z , zₛₙ) = suc (h (n , z) .fst) , (h (n , z) .snd , transport (cong (λ a → coalgM a .fst) (h-eq (n , z))) zₛₙ)
-- 
--       h-eq (zero , z) = refl
--       h-eq (suc n , (z , zₛₙ)) = {!h-eq (n , z)!} 

      --with h (n , z)
--      ... | (n' , z') = suc n'  , (z' , {!!})
--         where
--           t : ⟨ C ⟩
--           t = ι (bindM* coalgM (h (n , z) .fst) Y) (h (n , z) .snd)
-- 
--           t' : ⟨ C ⟩
--           t' = ι (bindM* coalgM n (⟨ Z ⟩ , (λ y → ι (bindM* coalgM (fst (ι Z y)) Y) (snd (ι Z y))))) z
--
--         map h (coalg (subcoalg (mapM (subcoalgHom Y .fst) Z)) (n , z))
--         ≡⟨ sym (map∘ _) ∙ sym (map∘ _) ⟩
--         {!!}
--         ≡⟨ {!!} ⟩
--         map ((λ section₁ → suc (h (n , z) .fst) , section₁) ∘ (snd (h (n , z)) ,_)) (SB (coalg C (ι (bindM* coalgM (fst (h (n , z))) Y) (snd (h (n , z)))))
--            .snd .fst)
--         ≡⟨ map∘ _ ⟩
--         map (suc (h (n , z) .fst) ,_) (pick (bindM* coalgM (h (n , z) .fst) Y) (h (n , z) .snd))
--         ≡⟨ refl ⟩
--         coalg (subcoalg Y) (h (n , z))
--         ∎
--        ∙ map∘ _
--       (zero , z) =
--         sym (map∘ _) ∙ sym (map∘ _)
--         ∙ cong (λ s → map s (SB (coalg C (ι (mapM (subcoalgHom Y .fst) Z) z)) .snd .fst))
--                (funExt (λ z₁ i → suc (snd Z z .fst) , snd Z z .snd , transportRefl z₁ i))
--         ∙ map∘ _
--       h-eq' (suc n , (z , zₛₙ)) = 
--         sym (map∘ _) ∙ sym (map∘ _)
--         ∙ {!!}
--         ∙ {!h-eq' (n , z) ∙ sym (map∘ _)!}
--         ∙ map∘ _

--         where
--           eq' : coalgM ∘ subcoalgHom Y .fst ≡ {!!}
-- 
--           eq : bindM coalgM (bindM* coalgM n (mapM (subcoalgHom Y .fst) Z)) ≡ bindM* coalgM n (bindM (coalgM ∘ subcoalgHom Y .fst) Z)
--           eq = {!coalgM ∘ subcoalgHom Y .fst!}
          --bindM*eq coalgM n (mapM (subcoalgHom Y .fst) Z)

--          z' : bindM* coalgM n (bindM coalgM (mapM (subcoalgHom Y .fst) Z)) .fst
--          z' = transport (λ i → eq i .fst) z

{-
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
-}

