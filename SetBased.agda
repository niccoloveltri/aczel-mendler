{-# OPTIONS --cubical #-}


module SetBased where

open import Utilities
open import Multiset
import Coalgebras

-- ==============================================

-- SET-BASED FUNCTORS (in the sense of Aczel-Mendler)

-- A functor F is (ℓs,ℓl)-set-based if forall (large) ℓl-type and x : F X,
-- there are:
-- 1) a (small) ℓs-type Y with ι : Y → X
-- 2) an element x₀ : F Y
-- 3) a proof that map ι x₀ ≡ x
-- This is a form of accessibility, where instead of cardinals we use universe levels.

isSetBased : ∀ {ℓz} ℓs ℓl → Functor ℓz → Type (ℓ-max (ℓ-max ℓz (ℓ-suc ℓs)) (ℓ-suc ℓl))
isSetBased ℓs ℓl Fun =
  let open Functor Fun in
  {X : Type ℓl} (x : F X) → Σ[ Y ∈ M ℓs X ] Σ[ x₀ ∈ F ⟨ Y ⟩ ] map (ι Y) x₀ ≡ x

module SetBasedDestr {ℓz ℓs ℓl}
                     (Fun : Functor ℓz)
                     (SB : isSetBased ℓs ℓl Fun) where

  open Functor Fun

  index : {X : Type ℓl} → F X → M ℓs X
  index x = SB x .fst

  coll : {X : Type ℓl} (x : F X) → F ⟨ index x ⟩
  coll x = SB x .snd .fst

  coll-eq : {X : Type ℓl} (x : F X) → map (ι (index x)) (coll x) ≡ x
  coll-eq x = SB x .snd .snd

-- ==============================================

-- Given a (ℓs,ℓl)-set-based functor F and a ℓl-coalgebra C, then each
-- ℓs-multiset Y of C determines a ℓs-coalgebra C^Y and a coalgebra
-- morphism from C^Y to C.

module SubCoalg {ℓz ℓs ℓl}
                (Fun : Functor ℓz)
                (SB : isSetBased ℓs ℓl Fun)
                (C : Coalgebras.Coalg Fun ℓl) where 

  open Functor Fun
  open Coalgebras Fun
  open SetBasedDestr Fun SB

  coalgM : ⟨ C ⟩ → M ℓs ⟨ C ⟩
  coalgM x = index (coalg C x)

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
  run Y a = map (a ,_) (coll (coalg C (ι Y a)))

  run-eq : (Y : M ℓs ⟨ C ⟩) (a : ⟨ Y ⟩)
    → map (ι (next Y)) (run Y a) ≡ coalg C (ι Y a)
  run-eq Y a = sym (map∘ _) ∙ coll-eq (coalg C (ι Y a))

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
      coalgA₀ (n , a) = map (λ y → suc n , y) (run (next* n Y) a)

  C^Hom : (Y : M ℓs ⟨ C ⟩) → CoalgHom (C^ Y) C
  C^Hom Y = f , coalgHom-f
    where
      f : ⟨ C^ Y ⟩ → ⟨ C ⟩
      f (n , a) = ι (next* n Y) a

      coalgHom-f : map f ∘ coalg (C^ Y) ≡ coalg C ∘ f
      coalgHom-f = funExt (λ x → sym (map∘ _) ∙ run-eq (next* (fst x) Y) (snd x)) 

  up : (Y : M ℓs ⟨ C ⟩) → ⟨ Y ⟩ → ⟨ C^ Y ⟩
  up Y y = 0 , y

  up-eq : (Y : M ℓs ⟨ C ⟩) (y : ⟨ Y ⟩)
    → map (C^Hom Y .fst) (coalg (C^ Y) (up Y y)) ≡ coalg C (ι Y y)
  up-eq Y y = funExt⁻ (C^Hom Y .snd) (0 , y)


-- Given
-- Y a ℓs-multiset of C and
-- Z a ℓs-multiset of C^Y then
-- there is a coalgebra morphism from C^Z' to C^Y, where
-- Z' is the ℓs-multiset of C associated to Z.

  C^lift : (Y : M ℓs ⟨ C ⟩) (Z : M ℓs ⟨ C^ Y ⟩) → 
    let Z' = mapM (C^Hom Y .fst) Z in
      Σ[ h ∈ CoalgHom (C^ Z') (C^ Y) ]
         ∀ z → ι (Σnext (mapM (C^Hom Y .fst) Z)) z ≡ ι (Σnext Y) (h .fst z)
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

      coalgHom-h' : ∀ z → map h (coalg (C^ Z') z) ≡ coalg (C^ Y) (h z)
      coalgHom-h' (n , z) =
        sym (map∘ _) ∙ sym (map∘ _)
        ∙ map-lem Fun
                  {X = λ a → ⟨ index (coalg C a) ⟩}
                   (hι (n , z))
                   (λ _ → refl)
                   (λ i → coll (coalg C (hι (n , z) i)))
        ∙ map∘ _

      coalgHom-h : map h ∘ coalg (C^ Z') ≡ coalg (C^ Y) ∘ h
      coalgHom-h = funExt coalgHom-h'






isSetBasedRel : ∀ {ℓz} ℓs ℓl (Fun : Functor ℓz)
  → isSetBased ℓs ℓl Fun
  → Type (ℓ-max (ℓ-max ℓz (ℓ-suc ℓs)) (ℓ-suc ℓl))
isSetBasedRel ℓs ℓl Fun SB =
  let open Functor Fun
      open SetBasedDestr Fun SB in
  {X Y : Type ℓl} {R : X → Y → Type ℓl} {x : F X} {y : F Y} (r : relLift' Fun R x y)
    → Σ[ R₀ ∈ (⟨ index x ⟩ → ⟨ index y ⟩ → Type ℓs) ]
         Σ[ ι ∈ (∀ a b → R₀ a b → R (ι (index x) a) (ι (index y) b)) ]
            relLift' Fun R₀ (coll x) (coll y)

-- Assume given (A , ιA) : P X and (B , ιB) : P Y
-- and (S , ιS) : P (Σ x y. R x y) such that
-- P fst (S , ιS) ≡ (A , ιA) and P (fst ∘ snd) (S , ιS) ≡ (B , ιB).
-- This means that there are
--   eA : A ≃ S such that forall a : A, fst (ιS (eA a)) ≡ ιA a, and
--   eB : B ≃ S such that forall b : B, fst (snd (ιS (eB b))) ≡ ιB b
-- Take e : A ≃ B composition of eA and the inverse of eB.

-- Define R₀ : A → B → Type ℓs
--        R₀ a b = e a ≡ b
-- or     R₀ a b = eA a ≡ eB b

-- Prove that R₀ a b implies R (ιA a) (ιB b).
-- Assume eA a ≡ eB b then
-- snd (snd (ιS (eA a))) : R (fst (ιS (eA a))) (fst (snd (ιS (eA a)))).
-- But we know
-- fst (ιS (eA a)) ≡ ιA a and
-- fst (snd (ιS (eA a))) ≡ fst (snd (ιS (eB b))) ≡ ιB b

-- Prove that relLift' Fun R₀ x₀ y₀,
-- with x₀ = (A , id) and y₀ = (B , id)
-- This means find (S' , ιS') : P (Σ a b. R₀ a b) such that
-- P fst (S' , ιS') ≡ (A , id) and P (fst ∘ snd) (S' , ιS') ≡ (B , id).
-- Pick S' = S and
--      ιS' s = (eA-1 s, eB-1 s, p : eA (eA-1 s) ≡ s ≡ eB (eB-1 s))


{-
-- OLD

-- Assume given (A , ιA) : P X and (B , ιB) : P X
-- such that P [_]R (A , ιA) ≡ P [_]R (B , ιB).
-- This means that there is e : A ≃ B and forall a : A,
-- [ ιA a ]R ≡ [ ιB (e a) ]R

-- Define R₀ : A → B → Type ℓs
--        R₀ a b = e a ≡ b

-- Prove that R₀ a b implies R (ιA a) (ιB b).
-- If R is effective, then yes, since we know
-- [ ιA a ]R ≡ [ ιB (e a) ]R ≡ [ ιB b ]R

-- Prove that relLift Fun R₀ x₀ y₀,
-- with x₀ = (A , id) and y₀ = (B , id)
-- We have e : A ≃ B, we need to show
-- [ a ]R₀ = [ e a ]R₀, which is true since
-- R₀ a (e a).
-}
