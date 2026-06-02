{-# OPTIONS --cubical --guardedness #-}

module SetUBased where

open import Utilities
open import Multiset
import Coalgebras

-- ==============================================

-- U-BASED FUNCTORS ("set-based" in the terminology of Aczel-Mendler)

-- A functor F is (υ,ℓ)-set-based if forall (large) ℓ-set and x : F X,
-- there are:
-- 1) a (small) υ-set Y with ι : Y → X
-- 2) an element x₀ : F Y
-- 3) a proof that map ι x₀ ≡ x
-- This is a form of accessibility, where instead of cardinals we use universe levels.

isSetBased : ∀ {ℓz} υ ℓl → Functor ℓz → Type (ℓ-max (ℓ-max ℓz (ℓ-suc υ)) (ℓ-suc ℓl))
isSetBased υ ℓl Fun =
  let open Functor Fun in
  {X : Type ℓl} (setX : isSet X) (x : F X) → Σ[ Y ∈ P∞ υ X ] Σ[ x₀ ∈ F ⟨ Y ⟩ ] map setX (ι Y) x₀ ≡ x

module SetBasedDestr {ℓz υ ℓl}
                     (Fun : Functor ℓz)
                     (SB : isSetBased υ ℓl Fun) where

  open Functor Fun

  index : {X : Type ℓl} (setX : isSet X) → F X → P∞ υ X
  index setX x = SB setX x .fst

  coll : {X : Type ℓl} (setX : isSet X) (x : F X) → F ⟨ index setX x ⟩
  coll setX x = SB setX x .snd .fst

  coll-eq : {X : Type ℓl} (setX : isSet X) (x : F X)
    → map setX (ι (index setX x)) (coll setX x) ≡ x
  coll-eq setX x = SB setX x .snd .snd

-- ==============================================

-- Given a (υ,ℓl)-set-based functor F and a ℓl-coalgebra C, then each
-- υ-multiset Y of C determines a υ-coalgebra C^Y and a coalgebra
-- morphism from C^Y to C.

module SubCoalg {ℓz υ ℓl}
                (Fun : Functor ℓz)
                (SB : isSetBased υ ℓl Fun)
                (C : Coalgebras.Coalg Fun ℓl)
                (setC : isSet ⟨ C ⟩) where 

  open Functor Fun
  open Coalgebras Fun
  open SetBasedDestr Fun SB

  coalgP∞ : ⟨ C ⟩ → P∞ υ ⟨ C ⟩
  coalgP∞ x = index setC (coalg C x)

  next : P∞ υ ⟨ C ⟩ → P∞ υ ⟨ C ⟩
  next = bind coalgP∞

  next* : ℕ → P∞ υ ⟨ C ⟩ → P∞ υ ⟨ C ⟩
  next* n = bind* coalgP∞ n

  Σnext : P∞ υ ⟨ C ⟩ → P∞ υ ⟨ C ⟩
  Σnext = bind∞ coalgP∞


{-

  ⟨ Y ⟩ ------> F ⟨ next Y ⟩
    |             |
    |             |
    V             V
  ⟨ C ⟩ ------> F ⟨ C ⟩ 
-}

  run : (Y : P∞ υ ⟨ C ⟩) → ⟨ Y ⟩ → F ⟨ next Y ⟩
  run Y a = map (isSetΣ (setP∞ Y) (λ y → setP∞ (coalgP∞ (ι Y y)))) (a ,_) (coll setC (coalg C (ι Y a)))

  run-eq : (Y : P∞ υ ⟨ C ⟩) (a : ⟨ Y ⟩)
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

  C^ : P∞ υ ⟨ C ⟩ → Coalg υ
  C^ Y = A₀ , coalgA₀
    where
      A₀ = ⟨ Σnext Y ⟩
      
      coalgA₀ : A₀ → F A₀
      coalgA₀ (n , a) = map (setP∞ (Σnext Y)) (λ y → suc n , y) (run (next* n Y) a)

  C^Hom : (Y : P∞ υ ⟨ C ⟩) → CoalgHom (C^ Y) C setC
  C^Hom Y = f , coalgHom-f
    where
      f : ⟨ C^ Y ⟩ → ⟨ C ⟩
      f (n , a) = ι (next* n Y) a

      coalgHom-f : map setC f ∘ coalg (C^ Y) ≡ coalg C ∘ f
      coalgHom-f = funExt (λ x → sym (map∘ _) ∙ run-eq (next* (fst x) Y) (snd x)) 

  up : (Y : P∞ υ ⟨ C ⟩) → ⟨ Y ⟩ → ⟨ C^ Y ⟩
  up Y y = 0 , y

  up-eq : (Y : P∞ υ ⟨ C ⟩) (y : ⟨ Y ⟩)
    → map setC (C^Hom Y .fst) (coalg (C^ Y) (up Y y)) ≡ coalg C (ι Y y)
  up-eq Y y = funExt⁻ (C^Hom Y .snd) (0 , y)


-- Given
-- Y a υ-multiset of C and
-- Z a υ-multiset of C^Y then
-- there is a coalgebra morphism from C^Z' to C^Y, where
-- Z' is the υ-multiset of C associated to Z.

  C^lift : (Y : P∞ υ ⟨ C ⟩) (Z : P∞ υ ⟨ C^ Y ⟩) → 
    let Z' = mapP∞ (C^Hom Y .fst) Z in
      Σ[ h ∈ CoalgHom (C^ Z') (C^ Y) (setP∞ (Σnext Y)) ]
         ((z : ⟨ Z ⟩) → h .fst (up Z' z) ≡ ι Z z)
  C^lift Y Z = (h , coalgHom-h) , λ _ → refl
    where
      Z' = mapP∞ (C^Hom Y .fst) Z

      h' : (n : ℕ) (z : ⟨ next* n Z' ⟩)
        → Σ[ n' ∈ ℕ ] Σ[ z' ∈ ⟨ next* n' Y ⟩ ] ι (next* n Z') z ≡ ι (next* n' Y) z'
      h' zero z = ι Z z .fst , ι Z z .snd , refl
      h' (suc n) (z , zₛₙ) = suc n' , (z' , zₛₙ') , eq'
        where
          n' = h' n z .fst
          z' = h' n z .snd .fst
          zₛₙ' = transport (λ i → coalgP∞ (h' n z .snd .snd i) .fst) zₛₙ
          
          eq' : ι (coalgP∞ (ι (next* n Z') z)) zₛₙ ≡ ι (coalgP∞ (ι (next* n' Y) z')) zₛₙ'
          eq' = ι-lem zₛₙ (λ i → coalgP∞ (h' n z .snd .snd i))


      h : ⟨ C^ Z' ⟩ → ⟨ C^ Y ⟩
      h (n , z) = h' n z .fst , h' n z .snd .fst

      hι : ∀ z → ι (Σnext Z') z ≡ ι (Σnext Y) (h z)
      hι (n , z) = h' n z .snd .snd

      coalgHom-h' : ∀ z → map (setP∞ (Σnext Y)) h (coalg (C^ Z') z) ≡ coalg (C^ Y) (h z)
      coalgHom-h' (n , z) =
        sym (map∘ _) ∙ sym (map∘ _)
        ∙ map-lem Fun
                  {X = λ a → ⟨ index setC (coalg C a) ⟩}
                   (hι (n , z))
                   (λ _ → refl)
                   (λ i → coll setC (coalg C (hι (n , z) i)))
        ∙ map∘ _

      coalgHom-h : map (setP∞ (Σnext Y)) h ∘ coalg (C^ Z') ≡ coalg (C^ Y) ∘ h
      coalgHom-h = funExt coalgHom-h'


  C^lift-eq : (Y : P∞ υ ⟨ C ⟩) (Z : P∞ υ ⟨ C^ Y ⟩) → 
    let Z' = mapP∞ (C^Hom Y .fst) Z in
    (z' : ⟨ Z' ⟩) → C^lift Y Z .fst .fst (up Z' z') ≡ ι Z z'
  C^lift-eq Y Z z' = refl

