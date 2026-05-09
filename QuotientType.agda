{-# OPTIONS --rewriting --prop #-}

-- quotient types as in
-- https://jesper.sikanda.be/posts/hack-your-type-theory.html

module QuotientType where

open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import Level using (Level)
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

private variable
  ℓ : Level
  A : Set
  R : A → A → Set
  x y : A

postulate
  _//_ : (A : Set ℓ) (R : A → A → Set) → Set ℓ
  proj : A → A // R
  quot : R x y → proj {R = R} x ≡ proj {R = R} y

  //-elim : (P : A // R → Set ℓ) →
            (proj* : (x : A) → P (proj x)) →
            (quot* : {x y : A} (r : R x y) → subst P (quot r) (proj* x) ≡ proj* y) →
            (x : A // R) → P x

  //-beta : (P : A // R → Set ℓ) →
            (proj* : (x : A) → P (proj x)) →
            (quot* : {x y : A} (r : R x y) → subst P (quot r) (proj* x) ≡ proj* y) →
            {u : A} → //-elim P proj* quot* (proj u) ≡ proj* u

  {-# REWRITE //-beta #-}