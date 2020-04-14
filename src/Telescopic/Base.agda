{-# OPTIONS --rewriting --confluence-check #-}

module Telescopic.Base where

open import Agda.Primitive public
open import Agda.Builtin.Sigma public
open import Prelude.Semiring public
open import Prelude.Function public
open import Prelude.Nat renaming ( Nat to ℕ ) public
open import Prelude.List using ( List; []; _∷_; _++_; map ) public
open import Prelude.Sum renaming ( Either to _⊎_ ) using ( left; right ) public
open import Prelude.Equality using (_≡_; refl; sym; trans; transport; cong; Eq; _==_) public
open import Prelude.Decidable using (Dec; yes; no)
open import Container.List using ( All; []; _∷_; Any; zero; suc; _∈_ ) public

record · {a} : Set a where
  instance constructor ∗

open Σ public

infix 2 Σ-syntax
Σ-syntax : ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ b)
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ[ x ∈ A ] B

_×′_ : ∀ {a b} (A : Set a) (B : {{x : A}} → Set b) → Set (a ⊔ b)
A ×′ B = Σ[ x ∈ A ] B {{x}}

{-# BUILTIN REWRITE _≡_ #-}

lookup∈ : ∀ {a} {A : Set a} {{eqA : Eq A}}
       → (x : A) (xs : List A) → Dec (x ∈ xs)
lookup∈ x [] = no (λ ())
lookup∈ x (y ∷ xs) with x == y
... | yes x≡y = yes (zero x≡y)
... | no  x≢y with lookup∈ x xs
... | yes x∈xs = yes (suc x∈xs)
... | no  x∉xs = no (λ where
  (zero x≡y)  → x≢y x≡y
  (suc  x∈xs) → x∉xs x∈xs)
