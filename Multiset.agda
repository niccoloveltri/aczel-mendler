{-# OPTIONS --cubical #-}


module Multiset where

open import Utilities

-- The ℓs-multiset functor

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

-- M is a monad

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

-- Kleisli extension can be iterated, and one can form the collection
-- of all iterations.

bindM* : ∀{ℓl ℓs} {X : Type ℓl} (f : X → M ℓs X) → ℕ → M ℓs X → M ℓs X
bindM* f zero Y = Y
bindM* f (suc n) Y = bindM f (bindM* f n Y)

bindM∞ : ∀{ℓl ℓs} {X : Type ℓl} (f : X → M ℓs X) → M ℓs X → M ℓs X
bindM∞ f Y = (Σ[ n ∈ ℕ ] bindM* f n Y .fst) , uncurry (λ n → bindM* f n Y .snd)

