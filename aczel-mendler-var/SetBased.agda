{-# OPTIONS --cubical #-}


module SetBased where

open import Utilities
open import Multiset
import Coalgebras

-- ==============================================

-- SET-BASED FUNCTORS (in the sense of Aczel-Mendler)

-- A functor F is (ℓs,ℓl)-set-based if forall (large) ℓl-type and x : F X,
-- there are:
-- 1) a (small) ℓs-set Y with ι : Y → X
-- 2) an element x₀ : F Y
-- 3) a proof that map ι x₀ ≡ x
-- This is a form of accessibility, where instead of cardinals we use universe levels.

isSetBased : ∀ {ℓz} ℓs ℓl → Functor ℓz → Type (ℓ-max (ℓ-max ℓz (ℓ-suc ℓs)) (ℓ-suc ℓl))
isSetBased ℓs ℓl Fun =
  let open Functor Fun in
  {X : Type ℓl} (setX : isSet X) (x : F X) → Σ[ Y ∈ M ℓs X ] Σ[ x₀ ∈ F ⟨ Y ⟩ ] map setX (ι Y) x₀ ≡ x

module SetBasedDestr {ℓz ℓs ℓl}
                     (Fun : Functor ℓz)
                     (SB : isSetBased ℓs ℓl Fun) where

  open Functor Fun

  index : {X : Type ℓl} (setX : isSet X) → F X → M ℓs X
  index setX x = SB setX x .fst

  coll : {X : Type ℓl} (setX : isSet X) (x : F X) → F ⟨ index setX x ⟩
  coll setX x = SB setX x .snd .fst

  coll-eq : {X : Type ℓl} (setX : isSet X) (x : F X)
    → map setX (ι (index setX x)) (coll setX x) ≡ x
  coll-eq setX x = SB setX x .snd .snd

-- ==============================================

-- Given a (ℓs,ℓl)-set-based functor F and a ℓl-coalgebra C, then each
-- ℓs-multiset Y of C determines a ℓs-coalgebra C^Y and a coalgebra
-- morphism from C^Y to C.

module SubCoalg {ℓz ℓs ℓl}
                (Fun : Functor ℓz)
                (SB : isSetBased ℓs ℓl Fun)
                (C : Coalgebras.Coalg Fun ℓl)
                (setC : isSet ⟨ C ⟩) where 

  open Functor Fun
  open Coalgebras Fun
  open SetBasedDestr Fun SB

  coalgM : ⟨ C ⟩ → M ℓs ⟨ C ⟩
  coalgM x = index setC (coalg C x)

  next : M ℓs ⟨ C ⟩ → M ℓs ⟨ C ⟩
  next = bindM coalgM

  next* : ℕ → M ℓs ⟨ C ⟩ → M ℓs ⟨ C ⟩
  next* n = bindM* coalgM n

  Σnext : M ℓs ⟨ C ⟩ → M ℓs ⟨ C ⟩
  Σnext = bindM∞ coalgM


{-

  ⟨ Y ⟩ ------> F ⟨ next Y ⟩
    |             |
    |             |
    V             V
  ⟨ C ⟩ ------> F ⟨ C ⟩ 
-}

  run : (Y : M ℓs ⟨ C ⟩) → ⟨ Y ⟩ → F ⟨ next Y ⟩
  run Y a = map (isSetΣ (setM Y) (λ y → setM (coalgM (ι Y y)))) (a ,_) (coll setC (coalg C (ι Y a)))

  run-eq : (Y : M ℓs ⟨ C ⟩) (a : ⟨ Y ⟩)
    → map setC (ι (next Y)) (run Y a) ≡ coalg C (ι Y a)
  run-eq Y a = sym (map∘ _) ∙ coll-eq setC (coalg C (ι Y a))

{-
  This can be iterated:

  ⟨ next* n Y ⟩ ------> F ⟨ next* (suc n) Y ⟩
    |                      |
    |                      |
    V                      V
  ⟨ C ⟩ --------------> F ⟨ C ⟩

  and the disj. union (the "colimit" of next*) gives a coalgebra

  ⟨ Σnext Y ⟩ ------> F ⟨ Σnext Y ⟩
    |                            |
    |                            |
    V                            V
  ⟨ C ⟩ ---------------------> F ⟨ C ⟩ 
-}

  C^ : M ℓs ⟨ C ⟩ → Coalg ℓs
  C^ Y = A₀ , coalgA₀
    where
      A₀ = ⟨ Σnext Y ⟩
      
      coalgA₀ : A₀ → F A₀
      coalgA₀ (n , a) = map (setM (Σnext Y)) (λ y → suc n , y) (run (next* n Y) a)

  C^Hom : (Y : M ℓs ⟨ C ⟩) → CoalgHom (C^ Y) C setC
  C^Hom Y = f , coalgHom-f
    where
      f : ⟨ C^ Y ⟩ → ⟨ C ⟩
      f (n , a) = ι (next* n Y) a

      coalgHom-f : map setC f ∘ coalg (C^ Y) ≡ coalg C ∘ f
      coalgHom-f = funExt (λ x → sym (map∘ _) ∙ run-eq (next* (fst x) Y) (snd x)) 

  up : (Y : M ℓs ⟨ C ⟩) → ⟨ Y ⟩ → ⟨ C^ Y ⟩
  up Y y = 0 , y

  up-eq : (Y : M ℓs ⟨ C ⟩) (y : ⟨ Y ⟩)
    → map setC (C^Hom Y .fst) (coalg (C^ Y) (up Y y)) ≡ coalg C (ι Y y)
  up-eq Y y = funExt⁻ (C^Hom Y .snd) (0 , y)


-- Given
-- Y a ℓs-multiset of C and
-- Z a ℓs-multiset of C^Y then
-- there is a coalgebra morphism from C^Z' to C^Y, where
-- Z' is the ℓs-multiset of C associated to Z.

  C^lift : (Y : M ℓs ⟨ C ⟩) (Z : M ℓs ⟨ C^ Y ⟩) → 
    let Z' = mapM (C^Hom Y .fst) Z in
      Σ[ h ∈ CoalgHom (C^ Z') (C^ Y) (setM (Σnext Y)) ]
         ∀ z → C^Hom Z' .fst z ≡ C^Hom Y .fst (h .fst z)
  C^lift Y Z = (h , coalgHom-h) , hι
    where
      Z' = mapM (C^Hom Y .fst) Z

      h' : (n : ℕ) (z : ⟨ next* n Z' ⟩)
        → Σ[ n' ∈ ℕ ] Σ[ z' ∈ ⟨ next* n' Y ⟩ ] ι (next* n Z') z ≡ ι (next* n' Y) z'
      h' zero z = ι Z z .fst , ι Z z .snd , refl
      h' (suc n) (z , zₛₙ) = suc n' , (z' , zₛₙ') , eq'
        where
          n' = h' n z .fst
          z' = h' n z .snd .fst
          zₛₙ' = transport (λ i → coalgM (h' n z .snd .snd i) .fst) zₛₙ
          
          eq' : ι (coalgM (ι (next* n Z') z)) zₛₙ ≡ ι (coalgM (ι (next* n' Y) z')) zₛₙ'
          eq' = ι-lem zₛₙ (λ i → coalgM (h' n z .snd .snd i))


      h : ⟨ C^ Z' ⟩ → ⟨ C^ Y ⟩
      h (n , z) = h' n z .fst , h' n z .snd .fst

      hι : ∀ z → ι (Σnext Z') z ≡ ι (Σnext Y) (h z)
      hι (n , z) = h' n z .snd .snd

      coalgHom-h' : ∀ z → map (setM (Σnext Y)) h (coalg (C^ Z') z) ≡ coalg (C^ Y) (h z)
      coalgHom-h' (n , z) =
        sym (map∘ _) ∙ sym (map∘ _)
        ∙ map-lem Fun
                  {X = λ a → ⟨ index setC (coalg C a) ⟩}
                   (hι (n , z))
                   (λ _ → refl)
                   (λ i → coll setC (coalg C (hι (n , z) i)))
        ∙ map∘ _

      coalgHom-h : map (setM (Σnext Y)) h ∘ coalg (C^ Z') ≡ coalg (C^ Y) ∘ h
      coalgHom-h = funExt coalgHom-h'


  C^lift-eq : (Y : M ℓs ⟨ C ⟩) (Z : M ℓs ⟨ C^ Y ⟩) → 
    let Z' = mapM (C^Hom Y .fst) Z in
    (z' : ⟨ Z' ⟩) → C^lift Y Z .fst .fst (up Z' z') ≡ ι Z z'
  C^lift-eq Y Z z' = refl

