{-# OPTIONS --rewriting --confluence-chec #-}

module Telescopic.Equivalence where

open import Telescopic.Base
open import Telescopic.Telescope
open import Telescopic.Equality

record _≃_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    fun : A → B
    linv : B → A
    is-linv : ∀ x → linv (fun x) ≡ x
    rinv : B → A
    is-rinv : ∀ y → fun (rinv y) ≡ y

open _≃_ public

_≃ⁿ_ : ∀ {ls₁} {ls₂} (T₁ : Tel ls₁) (T₂ : Tel ls₂) → Set _
T₁ ≃ⁿ T₂ = ⟦ T₁ ⟧ ≃ ⟦ T₂ ⟧
