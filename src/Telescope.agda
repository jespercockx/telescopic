{-# OPTIONS --without-K --rewriting #-}

module Telescope where

open import Agda.Primitive public
open import Data.Nat using (ℕ; zero; suc; _+_) public
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂) public
open import Data.List using (List; []; _∷_; _++_) public

record · {a} : Set a where
  constructor ∗

LevelTel : Set
LevelTel = List Level

telLevel : LevelTel → Level
telLevel [] = lzero
telLevel (a ∷ as) = a ⊔ (telLevel as)

Tel : ∀ as → Set (lsuc (telLevel as))
Tel []       = ·
Tel (a ∷ as) = Σ[ A ∈ Set a ] ((x : A) → Tel as)

⟦_⟧ : ∀ {as} → Tel as → Set (telLevel as)
⟦_⟧ {as = []}     ∗       = ·
⟦_⟧ {as = a ∷ as} (A , T) = Σ[ x ∈ A ] ⟦ T x ⟧

infixr 4 extend-tel

extend-tel : ∀ {a as} (A : Set a) → (A → Tel as) → Tel (a ∷ as)
extend-tel = _,_

-- Mmmmm, delicious sugar
syntax extend-tel A (λ x → B) = x ∈ A , B

extend-tel′ : ∀ {ls l} (T : Tel ls) (B : ⟦ T ⟧ → Set l) → Tel (ls ++ (l ∷ []))
extend-tel′ {ls = []} ∗ B = b ∈ B ∗ , ∗
extend-tel′ {ls = x ∷ ls} (A , T) B = x ∈ A , extend-tel′ (T x) (λ xs → B (x , xs))

syntax extend-tel′ T (λ ts → B) = ts ∈ T ,′ B

Σ→Tel : ∀ {a b} {A : Set a} {B : A → Set b} →
        Σ[ x ∈ A ] (B x) → ⟦ x ∈ A , y ∈ B x , ∗ ⟧
Σ→Tel (x , y) = (x , y , ∗)

Tel→Σ : ∀ {a b} {A : Set a} {B : A → Set b} →
        ⟦ x ∈ A , y ∈ B x , ∗ ⟧ → Σ[ x ∈ A ] (B x)
Tel→Σ (x , y , ∗) = (x , y)

concat : ∀ {ls₁ ls₂} (T₁ : Tel ls₁) (T₂ : ⟦ T₁ ⟧ → Tel ls₂) → Tel (ls₁ ++ ls₂)
concat {ls₁ = []}      {ls₂} ∗        T₂ = T₂ ∗
concat {ls₁ = l ∷ ls₁} {ls₂} (A , T₁) T₂ = x ∈ A , concat (T₁ x) (λ xs → T₂ (x , xs))

syntax concat T₁ (λ xs → T₂) = xs ∈ T₁ ++ T₂

flatten : ∀ {ls₁ ls₂} {T₁ : Tel ls₁} {T₂ : ⟦ T₁ ⟧ → Tel ls₂} →
          (xs : ⟦ T₁ ⟧) → ⟦ T₂ xs ⟧ → ⟦ xs ∈ T₁ ++ T₂ xs ⟧
flatten {ls₁ = []}      ∗        ys = ys
flatten {ls₁ = l ∷ ls₁} (x , xs) ys = x , flatten xs ys

syntax flatten xs ys = xs +++ ys

chunk : ∀ {ls₁ ls₂} {T₁ : Tel ls₁} {T₂ : ⟦ T₁ ⟧ → Tel ls₂} →
        ⟦ xs ∈ T₁ ++ T₂ xs ⟧ → Σ[ xs ∈ ⟦ T₁ ⟧ ] ⟦ T₂ xs ⟧
chunk {ls₁ = []}      {ls₂} {∗}      {T₂} ys       = ∗ , ys
chunk {ls₁ = l ∷ ls₁} {ls₂} {A , T₁} {T₂} (x , xs) = (x , (proj₁ rec)) , (proj₂ rec)
  where
    rec : ⟦ xs ∈ ⟦ T₁ x ⟧ , T₂ (x , xs) ⟧
    rec = chunk xs

infixl 0 _$_

_$_ : ∀ {a ls b} {A : Set a} {T : A → Tel ls} {B : ⟦ a ∈ A , T a ⟧ → Set b}
      (f : (x : ⟦ a ∈ A , T a ⟧) → B x) → (a : A) → (t : ⟦ T a ⟧) → B (a , t)
(f $ a) t = f (a , t)

arrⁿ : ∀ {ls b} (T : Tel ls) (B : ⟦ T ⟧ → Set b) → Set (telLevel ls ⊔ b)
arrⁿ {ls = []}     ∗       B = B ∗
arrⁿ {ls = l ∷ ls} (A , T) B = (x : A) → arrⁿ (T x) (λ xs → B (x , xs))

syntax arrⁿ T (λ xs → B) = xs ∈ T →ⁿ B

lamⁿ : ∀ {ls b} {T : Tel ls} {B : ⟦ T ⟧ → Set b} →
       ((xs : ⟦ T ⟧) → B xs) → xs ∈ T →ⁿ B xs
lamⁿ {ls = []}     f   = f ∗
lamⁿ {ls = l ∷ ls} f x = lamⁿ (λ xs → f (x , xs))

syntax lamⁿ (λ xs → t) = λⁿ xs →ⁿ t

_$ⁿ_ : ∀ {ls b} {T : Tel ls} {B : ⟦ T ⟧ → Set b} →
       xs ∈ T →ⁿ B xs → (xs : ⟦ T ⟧) → B xs
_$ⁿ_ {ls = []}     f ∗        = f
_$ⁿ_ {ls = l ∷ ls} f (x , xs) = f x $ⁿ xs

test = _+_ $ⁿ (1 , 1 , ∗)
