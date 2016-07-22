{-# OPTIONS --without-K --rewriting #-}

module Equality where

open import Base
open import Telescope

open import Prelude.Equality using () renaming
  (_≡_ to _≡₁_;
   refl to refl₁;
   sym to sym₁;
   trans to trans₁;
   transport to subst₁;
   cong to cong₁)
  public

J₁ : ∀ {a b} {A : Set a} {x : A} (Φ : (x' : A) → x ≡₁ x' → Set b) →
           Φ x refl₁ → {x' : A} → (e : x ≡₁ x') → Φ x' e
J₁ Φ φ refl₁ = φ

[_]₁ : ∀ {a b} {A : Set a} {r s : A} → r ≡₁ s →
         {Φ : A → Set b} → Φ r → Φ s
[_]₁ {a} {b} {A} {r} {s} e {Φ} = subst₁ {a} {b} {A} Φ {r} {s} e

_≡_ : ∀ {ls} {T : Tel ls} → ⟦ T ⟧ → ⟦ T ⟧ → Tel ls
_≡_ {[]}     ∗        ∗        = ∗
_≡_ {l ∷ ls} (x , xs) (y , ys) = e ∈ x ≡₁ y , ([ e ]₁ xs) ≡ ys

refl : ∀ {ls} {T : Tel ls} {ts : ⟦ T ⟧} → ⟦ ts ≡ ts ⟧
refl {ls = []}     = ∗
refl {ls = l ∷ ls} = refl₁ , refl

J' : ∀ {ls b} {T : Tel ls} {rs : ⟦ T ⟧}
    (Φ : (ss : ⟦ T ⟧) → ⟦ rs ≡ ss ⟧ → Set b) →
    Φ rs refl → {ss : ⟦ T ⟧} → (es : ⟦ rs ≡ ss ⟧) → Φ ss es
J' {ls = []}     {T = ∗₁}    {∗}      Φ φ {∗}      ∗        = φ
J' {l ∷ ls} {T = A , T} {r , rs} Φ φ {.r , ss} (refl₁ , es) = J' (λ ss es → Φ (r , ss) (refl₁ , es)) φ es

subst' : ∀ {ls b} {T : Tel ls} (Φ : ⟦ T ⟧ → Set b) →
          {rs ss : ⟦ T ⟧} → ⟦ rs ≡ ss ⟧ → Φ rs → Φ ss
subst' Φ es φ = J' (λ x _ → Φ x) φ es

[_]' : ∀ {ls b} {T : Tel ls} {rs ss : ⟦ T ⟧} → ⟦ rs ≡ ss ⟧ →
      {Φ : ⟦ T ⟧ → Set b} → Φ rs → Φ ss
[_]' {ls} {b} {T} {rs} {ss} e {Φ} = subst' {ls} {b} {T} Φ {rs} {ss} e

J'-refl : ∀ {ls b} {T : Tel ls} {rs : ⟦ T ⟧}
         (Φ : (ss : ⟦ T ⟧) → ⟦ rs ≡ ss ⟧ → Set b) →
         (φ : Φ rs refl) → J' Φ φ refl ≡₁ φ
J'-refl {ls = []}     {rs = ∗}      Φ φ = refl₁
J'-refl {ls = l ∷ ls} {rs = r , rs} Φ φ = J'-refl {rs = rs} _ φ

{-# BUILTIN REWRITE _≡₁_ #-}
{-# REWRITE J'-refl #-}

cong' : ∀ {ls b} {T : Tel ls} {Φ : ⟦ T ⟧ → Set b} →
       (f : (ts : ⟦ T ⟧) → Φ ts) → {rs ss : ⟦ T ⟧} →
       (es : ⟦ rs ≡ ss ⟧) → [ es ]' (f rs) ≡₁ f ss
cong' {[]} f ∗ = refl₁
cong' {l ∷ ls} f (refl₁ , es) = cong' (λ ts → f (_ , ts)) es

cong'-refl : ∀ {ls b} {T : Tel ls} {Φ : ⟦ T ⟧ → Set b} →
            (f : (ts : ⟦ T ⟧) → Φ ts) → (rs : ⟦ T ⟧) →
            cong' f (refl {ts = rs}) ≡₁ refl₁
cong'-refl {[]}     f ∗        = refl₁
cong'-refl {l ∷ ls} f (r , rs) = cong'-refl (λ rs → f (r , rs)) rs

{-# REWRITE cong'-refl #-}

J : ∀ {ls₁ ls₂} {T₁ : Tel ls₁} {rs : ⟦ T₁ ⟧}
    (T₂ : (ss : ⟦ T₁ ⟧) → ⟦ rs ≡ ss ⟧ → Tel ls₂) →
    ⟦ T₂ rs refl ⟧ → {ss : ⟦ T₁ ⟧} → (es : ⟦ rs ≡ ss ⟧) → ⟦ T₂ ss es ⟧
J T₂ = J' (λ ss es → ⟦ T₂ ss es ⟧)

subst : ∀ {ls₁ ls₂} {T₁ : Tel ls₁} (T₂ : ⟦ T₁ ⟧ → Tel ls₂) →
           {rs ss : ⟦ T₁ ⟧} → ⟦ rs ≡ ss ⟧ → ⟦ T₂ rs ⟧ → ⟦ T₂ ss ⟧
subst T₂ es φ = J (λ x _ → T₂ x) φ es

[_] : ∀ {ls₁ ls₂} {T₁ : Tel ls₁} {rs ss : ⟦ T₁ ⟧} → ⟦ rs ≡ ss ⟧ →
         {T₂ : ⟦ T₁ ⟧ → Tel ls₂} → ⟦ T₂ rs ⟧ → ⟦ T₂ ss ⟧
[_]  e {Φ} = subst Φ e

cong : ∀ {ls₁ ls₂} {T₁ : Tel ls₁} {T₂ : ⟦ T₁ ⟧ → Tel ls₂} →
         (f : (ts : ⟦ T₁ ⟧) → ⟦ T₂ ts ⟧) → {rs ss : ⟦ T₁ ⟧} →
         (es : ⟦ rs ≡ ss ⟧) → ⟦ [ es ] (f rs) ≡ f ss ⟧
cong {[]}     f ∗            = refl
cong {l ∷ ls} f (refl₁ , es) = cong (λ ts → f (_ , ts)) es

cong-refl : ∀ {ls₁ ls₂} {T₁ : Tel ls₁} {T₂ : ⟦ T₁ ⟧ → Tel ls₂} →
            (f : (ts : ⟦ T₁ ⟧) → ⟦ T₂ ts ⟧) → (rs : ⟦ T₁ ⟧) →
            cong f (refl {ts = rs}) ≡₁ refl
cong-refl {[]}     f ∗        = refl₁
cong-refl {l ∷ ls} f (r , rs) = cong-refl (λ rs → f (r , rs)) rs


{-# REWRITE cong-refl #-}
