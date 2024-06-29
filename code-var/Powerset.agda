{-# OPTIONS --cubical #-}

open import Utilities 

module Powerset (ℓs : Level) where

open import Cubical.Functions.Embedding

-- The powerset functor

P : ∀{ℓ} → Type ℓ → Type (ℓ-max (ℓ-suc ℓs) ℓ)
P X = Σ[ U ∈ Type ℓs ] U ↪ X

-- P X is always a set

isSetP : ∀{ℓ} {X : Type ℓ} → isSet (P X)
isSetP {X = X} x@(_ , _ , embf) y@(_ , _ , embg) =
  isOfHLevelRespectEquiv 1
    (EmbeddingIP x y)
    (isProp× (isPropΠ (λ _ → isPropΠ (λ _ → isEmbedding→hasPropFibers embg _)))
             (isPropΠ (λ _ → isPropΠ (λ _ → isEmbedding→hasPropFibers embf _))))

-- A generalization of the kernel of a function.
Ker : ∀{ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} (f : X → Y)
  → (R : Y → Y → Type ℓ)
  → Type ℓ
Ker {X = X} f R = X / λ x x' → R (f x) (f x')  

-- Some useful lemmata
Inj→isEmbedding : ∀{ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'}
  → isSet X → isSet Y
  → (f : X → Y)
  → (∀ w x → f w ≡ f x → w ≡ x)
  → isEmbedding f
Inj→isEmbedding setX setY f inj x y =
  isoToIsEquiv (iso (cong f)
                    (inj x y)
                    (λ _ → setY _ _ _ _)
                    (λ _ → setX _ _ _ _))
                    
_∼_ : ∀{ℓ} {X : Type ℓ} → P X → P X → Type (ℓ-max ℓs ℓ)
(U , f , embf) ∼ (V , g , embg) =
  Σ[ e ∈ (U ≃ V) ] f ≡ g ∘ equivFun e

encodeP : ∀{ℓ} {X : Type ℓ} (s t : P X) → s ∼ t → s ≡ t
encodeP {X = X} s@(U , f , embf) t@(V , g , embg) eq@(e , eqf) =
  EquivJ (λ W e → (f : W → X) (embf : isEmbedding f)
            → f ≡ (λ x → g (equivFun e x)) → (W , f , embf) ≡ (V , g , embg))
         (λ f' embf' eqf' →
           cong₂ _,_ refl (Σ≡Prop (λ _ → isPropIsEmbedding) eqf'))
         e f embf eqf


-- We now start assuming propositional resizing.

module AssumePropRes (propRes : ∀ ℓ → PropRes ℓs ℓ) where

-- Thanks to propositional resizing, every set is locally small,
-- i.e. its path types live in universe ℓs.

  Eq : ∀{ℓ}{X : Type ℓ} (setX : isSet X) → X → X → Type ℓs
  Eq setX x y = propRes _ (x ≡ y) (setX x y) .fst
  
  EqEquiv : ∀{ℓ}{X : Type ℓ} (setX : isSet X) (x y : X)
    → (x ≡ y) ≃ Eq setX x y
  EqEquiv setX x y =  propRes _ (x ≡ y) (setX x y) .snd

-- Thanks to propositional resizing, the image of a set-valued
-- function is ℓs-small. More concretely, we prove that it is
-- equivalent to the kernel of the function.

  ImSet : ∀{ℓ} {U : Type ℓs} {X : Type ℓ} → isSet X
    → (f : U → X)
    → Type (ℓ-max ℓs ℓ)
  ImSet {U = U}{X} setX f = Σ[ x ∈ X ] ∃[ u ∈ U ] Eq setX (f u) x
  
  isSetImSet : ∀{ℓ} {U : Type ℓs} {X : Type ℓ} (setX : isSet X)
    → (f : U → X)
    → isSet (ImSet setX f)
  isSetImSet setX f = isSetΣ setX (λ _ → isProp→isSet squash₁)  
  
  Ker→ImSet : ∀{ℓ} {U : Type ℓs} {X : Type ℓ} (setX : isSet X)
    → (f : U → X)
    → Ker f (Eq setX) → ImSet setX f
  Ker→ImSet setX f =
    rec (isSetImSet setX f)
        (λ u → f u , ∣ u , equivFun (EqEquiv setX _ _) refl ∣₁)
        λ u u' eq → Σ≡Prop (λ _ → squash₁) (invEq (EqEquiv setX _ _) eq)
  
  ImSet→Ker : ∀{ℓ} {U : Type ℓs} {X : Type ℓ} (setX : isSet X)
    → (f : U → X)
    → ImSet setX f → Ker f (Eq setX)
  ImSet→Ker setX f (x , p) =
    rec→Set squash/
            (λ z → [ z .fst ])
            (λ { (u , p) (v , q) →
              eq/ u v (equivFun (EqEquiv setX _ _) (invEq (EqEquiv setX _ _) p
                       ∙ sym (invEq (EqEquiv setX _ _) q) )) })
            p  
  
  IsoKerImSet : ∀{ℓ} {U : Type ℓs} {X : Type ℓ} (setX : isSet X)
    → (f : U → X)
    → Iso (Ker f (Eq setX)) (ImSet setX f)
  IsoKerImSet setX f = iso (Ker→ImSet setX f) (ImSet→Ker setX f) sec ret
    where
      sec : section (Ker→ImSet setX f) (ImSet→Ker setX f)
      sec (x , p) =
        elimP {P = λ p → Ker→ImSet setX f (ImSet→Ker setX f (x , p)) ≡ (x , p)}
              (λ _ → isSetImSet setX f _ _)
              (λ { (u , q) → Σ≡Prop (λ _ → squash₁) (invEq (EqEquiv setX _ _) q) })
              p
  
      ret : retract (Ker→ImSet setX f) (ImSet→Ker setX f)
      ret = elimProp (λ _ → squash/ _ _)
                     (λ u → refl)
  
-- Action of powerset on set-valued functions.

  mapP : ∀{ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'}
    → isSet Y
    → (X → Y) → P X → P Y
  mapP setY f (U , ι , embι) =
    Ker (f ∘ ι) (Eq setY) ,
    rec setY (f ∘ ι) (λ _ _ eq → invEq (EqEquiv setY _ _) eq) ,
    Inj→isEmbedding squash/ setY _
                     (elimProp2 (λ _ _ → isPropΠ (λ _ → squash/ _ _))
                                λ x y eq → eq/ x y (equivFun (EqEquiv setY _ _) eq))
                                
-- mapP preserves composition.

  mapP∘ : {ℓ ℓ' ℓ'' : Level} {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''}
        {setY : isSet Y} {setZ : isSet Z} {g : Y → Z} {f : X → Y}
        (x : P X) →
        mapP setZ (g ∘ f) x ≡ mapP setZ g (mapP setY f x)
  mapP∘ {setY = setY}{setZ}{g}{f} (U , ι , embι) = 
    encodeP _ _ (isoToEquiv e ,
                 funExt (elimProp (λ _ → setZ _ _)
                                  λ _ → refl))
    where
      e : Iso (Ker (g ∘ f ∘ ι) (Eq setZ)) (Ker (g ∘ rec setY (f ∘ ι) (λ _ _ eq → invEq (EqEquiv setY _ _) eq)) (Eq setZ))
      Iso.fun e = rec squash/ (λ u → [ [ u ] ]) (λ u v eq → eq/ _ _ eq)
      Iso.inv e = rec squash/
                      (rec squash/
                           [_]
                           (λ u v eq → eq/ _ _ (equivFun (EqEquiv setZ _ _) (cong g (invEq (EqEquiv setY _ _) eq)))))
                      (elimProp2 (λ _ _ → isPropΠ (λ _ → squash/ _ _)) eq/)
      Iso.rightInv e = elimProp (λ _ → squash/ _ _) (elimProp (λ _ → squash/ _ _) λ _ → refl)
      Iso.leftInv e = elimProp (λ _ → squash/ _ _) (λ _ → refl)

-- P is a set-valued functor
  FunP : Functor (ℓ-suc ℓs)
  FunP = record { F = P ;
                  map = mapP ;
                  map∘ = λ {_}{_}{_}{_}{_}{_}{setY}{setZ}{g}{f} → mapP∘ {setY = setY}{setZ}{g}{f} ;
                  isSetF = isSetP }
  
  
  open import SetBased

-- P is set-based
  isSetBasedP : ∀ ℓ → isSetBased ℓs ℓ FunP
  isSetBasedP ℓ setX s@(U , ι , embι) =
    (U , setU , ι) ,
    (U , idfun U , λ _ _ → idIsEquiv _) ,
    encodeP _ _ (e , funExt (elimProp (λ _ → setX _ _) (λ _ → refl)))
    where
      setU : isSet U
      setU = Embedding-into-isSet→isSet (ι , embι) setX
  
      f : Ker (idfun U) _ → U
      f = rec setU (idfun U) (λ u v p → isEmbedding→Inj embι u v (invEq (EqEquiv setX _ _) p))
  
      ret : retract f [_]
      ret = elimProp (λ _ → squash/ _ _) (λ _ → refl)
  
      e : Ker (idfun U) _ ≃ U
      e = isoToEquiv (iso f [_] (λ _ → refl) ret)
  
  
  open import Final
  open FinalityLarge FunP (isSetBasedP (ℓ-suc ℓs)) (propRes (ℓ-suc ℓs))
  open import Coalgebras FunP
  open import Complete
  open CompleteLarge ℓs FunP

-- P admits a terminal coalgebra wrt. sets

  finalP : isFinalSet νF-Coalg _
  finalP = final

