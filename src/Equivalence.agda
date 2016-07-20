{-# OPTIONS --without-K --rewriting #-}

module Equivalence where

open import Telescope
open import Equality

record _≃₁_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    fun : A → B
    linv : B → A
    is-linv : ∀ x → linv (fun x) ≡₁ x
    rinv : B → A
    is-rinv : ∀ y → fun (rinv y) ≡₁ y

open _≃₁_ public

_≃_ : ∀ {ls₁} {ls₂} (T₁ : Tel ls₁) (T₂ : Tel ls₂) → Set _
T₁ ≃ T₂ = ⟦ T₁ ⟧ ≃₁ ⟦ T₂ ⟧
