{-# OPTIONS --cubical --guardedness #-}

module Multiset where

open import Utilities

-- The υ-multiset functor

P∞ : ∀ {ℓl} υ → Type ℓl → Type (ℓ-max ℓl (ℓ-suc υ))
P∞ υ X = Σ[ A ∈ Type υ ] (A → X)

ι : ∀ {ℓ₁ ℓ₂} {X : Type ℓ₁} (X' : P∞ ℓ₂ X) → ⟨ X' ⟩ → X
ι = snd

ι-lem : ∀ {ℓ₁ ℓ₂} {X : Type ℓ₁} {A B : P∞ ℓ₂ X} (a : ⟨ A ⟩) (eq : A ≡ B)
  → ι A a ≡ ι B (transport (cong fst eq) a)
ι-lem {A = A} a = J (λ B eq → ι A a ≡ ι B (transport (cong fst eq) a)) (λ i → ι A (transportRefl a (~ i)))

mapP∞ : ∀{ℓl₁ ℓl₂ υ} {X : Type ℓl₁} {Y : Type ℓl₂}
  → (X → Y)
  → P∞ υ X → P∞ υ Y
mapP∞ f (A , ιA) = A , f ∘ ιA

-- P∞ is a monad

ηP∞ : ∀{ℓl υ} {X : Type ℓl} → X → P∞ υ X
ηP∞ x = Unit* , (λ _ → x)
  
bind : ∀{ℓl₁ ℓl₂ υ} {X : Type ℓl₁} {Y : Type ℓl₂}
  → (X → P∞ υ Y)
  → P∞ υ X → P∞ υ Y
bind f (A , ιA) = (Σ[ a ∈ A ] f (ιA a) .fst) , uncurry (λ a → f (ιA a) .snd)

bindmapP∞ : ∀{ℓl₁ ℓl₂ ℓl₃ υ} {X : Type ℓl₁} {Y : Type ℓl₂} {Z : Type ℓl₃}
  → {g : Y → P∞ υ Z} {f : X → Y}
  → (x : P∞ υ X)
  → bind g (mapP∞ f x) ≡ bind (g ∘ f) x
bindmapP∞ x = refl  

-- Kleisli extension can be iterated, and one can form the collection
-- of all iterations.

bind* : ∀{ℓl υ} {X : Type ℓl} (f : X → P∞ υ X) → ℕ → P∞ υ X → P∞ υ X
bind* f zero Y = Y
bind* f (suc n) Y = bind f (bind* f n Y)

bind∞ : ∀{ℓl υ} {X : Type ℓl} (f : X → P∞ υ X) → P∞ υ X → P∞ υ X
bind∞ f Y = (Σ[ n ∈ ℕ ] bind* f n Y .fst) , uncurry (λ n → bind* f n Y .snd)

