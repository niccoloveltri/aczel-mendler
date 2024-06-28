{-# OPTIONS --cubical #-}

open import Utilities 

module Powerset {ℓs : Level}
                (propRes : ∀ ℓ → PropRes ℓs ℓ) where

open import Cubical.Functions.Embedding

Eq : ∀{ℓ}{X : Type ℓ} (setX : isSet X) → X → X → Type ℓs
Eq setX x y = propRes _ (x ≡ y) (setX x y) .fst

EqEquiv : ∀{ℓ}{X : Type ℓ} (setX : isSet X) (x y : X)
  → (x ≡ y) ≃ Eq setX x y
EqEquiv setX x y =  propRes _ (x ≡ y) (setX x y) .snd

P : ∀{ℓ} → Type ℓ → Type (ℓ-max (ℓ-suc ℓs) ℓ)
P X = Σ[ U ∈ Type ℓs ] isSet U × (U ↪ X)

_∼_ : ∀{ℓ} {X : Type ℓ} → P X → P X → Type (ℓ-max ℓs ℓ)
(U , setU , f , embf) ∼ (V , setV , g , embg) =
  Σ[ e ∈ U ≃ V ] f ≡ g ∘ equivFun e

encodeP : ∀{ℓ} {X : Type ℓ} (s t : P X) → s ∼ t → s ≡ t
encodeP s@(U , setU , f , embf) t@(V , setV , g , embg) eq@(e , tr) = {!!}

decodeP : ∀{ℓ} {X : Type ℓ} (s t : P X) → s ≡ t → s ∼ t
decodeP s t = J (λ t eq → s ∼ t) (idEquiv _ , refl) 

~Equiv : ∀{ℓ} {X : Type ℓ} (s t : P X) → (s ∼ t) ≃ (s ≡ t)
~Equiv = {!!}

Ker : ∀{ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} (f : X → Y)
  → (R : Y → Y → Type ℓ)
  → Type ℓ
Ker {X = X} f R = X / λ x x' → R (f x) (f x')  

isInj→isEmbedding : ∀{ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'}
  → isSet X → isSet Y
  → (f : X → Y)
  → (∀ w x → f w ≡ f x → w ≡ x)
  → isEmbedding f
isInj→isEmbedding setX setY f inj x y =
  isoToIsEquiv (iso (cong f)
                    (inj x y)
                    (λ _ → setY _ _ _ _)
                    (λ _ → setX _ _ _ _))

mapP : ∀{ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'}
  → isSet Y
  → (X → Y) → P X → P Y
mapP setY f (U , setU , ι , embι) =
  Ker (f ∘ ι) (Eq setY) ,
  squash/ ,
  rec setY (f ∘ ι) (λ _ _ eq → invEq (EqEquiv setY _ _) eq) ,
  isInj→isEmbedding squash/ setY _
                     (elimProp2 (λ _ _ → isPropΠ (λ _ → squash/ _ _))
                                λ x y eq → eq/ x y (equivFun (EqEquiv setY _ _) eq))

mapP∘ : {ℓ ℓ' ℓ'' : Level} {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''}
      {setY : isSet Y} {setZ : isSet Z} {g : Y → Z} {f : X → Y}
      (x : P X) →
      mapP setZ (g ∘ f) x ≡ mapP setZ g (mapP setY f x)
mapP∘ {setY = setY}{setZ}{g}{f} (U , setU , ι , embι) =
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

isProp∼ : ∀{ℓ} {X : Type ℓ} (s t : P X) → isProp (s ∼ t)
isProp∼ (U , setU , f , embf) (V , setV , g , embg) (e , tr) (e' , tr') = {!!}

isSetP : ∀{ℓ} {X : Type ℓ} → isSet (P X)
isSetP {X = X} x y = isOfHLevelRespectEquiv 1 (~Equiv x y) {!!}

FunP : Functor (ℓ-suc ℓs)
FunP = record { F = P ;
                map = mapP ;
                map∘ = λ {_}{_}{_}{_}{_}{_}{setY}{setZ}{g}{f} → mapP∘ {setY = setY}{setZ}{g}{f} ;
                isSetF = isSetP }
