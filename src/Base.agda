{-# OPTIONS --rewriting --confluence-check #-}

module Base where

open import Agda.Primitive public
open import Prelude.Semiring public
open import Prelude.Function public
open import Prelude.Nat renaming ( Nat to ℕ ) public
open import Prelude.List using ( List; []; _∷_; _++_; map ) public
open import Prelude.Sum renaming ( Either to _⊎_ ) using ( left; right ) public
open import Prelude.Equality using (_≡_; refl; sym; trans; transport; cong) public
open import Container.List using ( All; []; _∷_ ) public

record · {a} : Set a where
  instance constructor ∗

infixr 4 _,_
infix 2 Σ-syntax

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

Σ-syntax : ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ b)
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ[ x ∈ A ] B

_×′_ : ∀ {a b} (A : Set a) (B : {{x : A}} → Set b) → Set (a ⊔ b)
A ×′ B = Σ[ x ∈ A ] B {{x}}

{-# BUILTIN REWRITE _≡_ #-}
