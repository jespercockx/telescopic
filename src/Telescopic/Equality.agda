{-# OPTIONS --rewriting --confluence-check --show-implicit #-}

module Telescopic.Equality where

open import Telescopic.Base
open import Telescopic.Telescope

J : ∀ {a b} {A : Set a} {x : A} (Φ : (x' : A) → x ≡ x' → Set b) →
           Φ x refl → {x' : A} → (e : x ≡ x') → Φ x' e
J Φ φ refl = φ

_≡ⁿ_ : ∀ {ls} {T : Tel ls} → ⟦ T ⟧ → ⟦ T ⟧ → Tel ls
_≡ⁿ_ {[]}     ∗        ∗        = ∗
_≡ⁿ_ {l ∷ ls} (x , xs) (y , ys) = e ∈ x ≡ y , (transport _ e xs) ≡ⁿ ys

reflⁿ : ∀ {ls} {T : Tel ls} {ts : ⟦ T ⟧} → ⟦ ts ≡ⁿ ts ⟧
reflⁿ {ls = []}     = ∗
reflⁿ {ls = l ∷ ls} = refl , reflⁿ

Jⁿ : ∀ {ls b} {T : Tel ls} {rs : ⟦ T ⟧}
    (Φ : (ss : ⟦ T ⟧) → ⟦ rs ≡ⁿ ss ⟧ → Set b) →
    Φ rs reflⁿ → {ss : ⟦ T ⟧} → (es : ⟦ rs ≡ⁿ ss ⟧) → Φ ss es
Jⁿ {ls = []} {T = ∗₁}    {∗}      Φ φ {∗}      ∗           = φ
Jⁿ {l ∷ ls}  {T = A , T} {r , rs} Φ φ {_ , ss} (refl , es) = Jⁿ (λ ss es → Φ (r , ss) (refl , es)) φ es

transportⁿ : ∀ {ls b} {T : Tel ls} (Φ : ⟦ T ⟧ → Set b) →
          {rs ss : ⟦ T ⟧} → ⟦ rs ≡ⁿ ss ⟧ → Φ rs → Φ ss
transportⁿ Φ es φ = Jⁿ (λ x _ → Φ x) φ es

Jⁿ-refl : ∀ {ls b} {T : Tel ls} {rs : ⟦ T ⟧}
         (Φ : (ss : ⟦ T ⟧) → ⟦ rs ≡ⁿ ss ⟧ → Set b) →
         (φ : Φ rs reflⁿ) → Jⁿ Φ φ reflⁿ ≡ φ
Jⁿ-refl {ls = []}     {rs = ∗}      Φ φ = refl
Jⁿ-refl {ls = l ∷ ls} {rs = r , rs} Φ φ = Jⁿ-refl {rs = rs} _ φ

{-# REWRITE Jⁿ-refl #-}

congⁿ : ∀ {ls b} {T : Tel ls} {Φ : ⟦ T ⟧ → Set b} →
       (f : (ts : ⟦ T ⟧) → Φ ts) → {rs ss : ⟦ T ⟧} →
       (es : ⟦ rs ≡ⁿ ss ⟧) → transportⁿ _ es (f rs) ≡ f ss
congⁿ {[]}     f ∗           = refl
congⁿ {l ∷ ls} f (refl , es) = congⁿ (λ ts → f (_ , ts)) es

congⁿ-refl : ∀ {ls b} {T : Tel ls} {Φ : ⟦ T ⟧ → Set b} →
            (f : (ts : ⟦ T ⟧) → Φ ts) → (rs : ⟦ T ⟧) →
            congⁿ f (reflⁿ {ts = rs}) ≡ refl
congⁿ-refl {[]}     f ∗        = refl
congⁿ-refl {l ∷ ls} f (r , rs) = congⁿ-refl (λ rs → f (r , rs)) rs

{-# REWRITE congⁿ-refl #-}
