module ParallelProduct where

open import Cont
open import Categories.Category.Monoidal using (Monoidal; monoidalHelper)
open import Categories.Category.Monoidal.Braided using (Braided)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Functor.Bifunctor using (Bifunctor; flip-bifunctor)
open import Categories.Morphism Cont using (_≅_)

open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂; assocˡ; assocʳ)

open import ContMonoidal using (Idᶜ)
open _⇒_


-- PARALLEL PRODUCT AND UNIT

_⊗_ : Container → Container → Container
(S ⊲ P) ⊗ (S' ⊲ P') = (S × S') ⊲ λ {(s , s') → P s × P' s'}


-- PARALLEL PRODUCT IS FUNCTORIAL

⊗-bifunctor : Bifunctor Cont Cont Cont
⊗-bifunctor = record
  { F₀ = λ {(C , D) → C ⊗ D}
  ; F₁ = λ {(f , g) → _ ⊲ λ {_ (p , q) → pf f _ p , pf g _ q}}
  ; identity = refl
  ; homomorphism = refl
  ; F-resp-≈ = λ {(refl , refl) → refl}
  }


-- MONOIDAL STRUCTURE BASED ON PARALLEL PRODUCT AND UNIT

unitorˡ : Idᶜ ⊗ C ≅ C
unitorˡ = record
  { from = _ ⊲ λ _ → _ ,_
  ; to = _ ⊲ λ _ → proj₂
  ; iso = record { isoˡ = refl ; isoʳ = refl }
  }

unitorʳ : C ⊗ Idᶜ ≅ C
unitorʳ = record
  { from = _ ⊲ λ _ → _, _
  ; to = _ ⊲ λ _ → proj₁
  ; iso = record { isoˡ = refl ; isoʳ = refl }
  }

associator : (C ⊗ D) ⊗ E ≅ C ⊗ (D ⊗ E)
associator = record
  { from = _ ⊲ λ _ → assocˡ
  ; to = _ ⊲ λ _ → assocʳ
  ; iso = record { isoˡ = refl ; isoʳ = refl }
  }

⊗-monoidal : Monoidal Cont
⊗-monoidal = monoidalHelper Cont (record
  { ⊗ = ⊗-bifunctor
  ; unit = Idᶜ
  ; unitorˡ = unitorˡ
  ; unitorʳ = unitorʳ
  ; associator = associator
  ; unitorˡ-commute = refl
  ; unitorʳ-commute = refl
  ; assoc-commute = refl
  ; triangle = refl
  ; pentagon = refl
  })

⊗-braided : Braided ⊗-monoidal
⊗-braided = record
  { braiding = record
      { F⇒G = record { η = λ _ → _ ⊲ λ {s (a , b) → b , a} ; commute = λ _ → refl ; sym-commute = λ _ → refl }
      ; F⇐G = record { η = λ _ → _ ⊲ λ {s (a , b) → b , a} ; commute = λ _ → refl ; sym-commute = λ _ → refl }
      ; iso = λ _ → record { isoˡ = refl ; isoʳ = refl }
      }
  ; hexagon₁ = refl
  ; hexagon₂ = refl
  }

⊗-symmetric : Symmetric ⊗-monoidal
⊗-symmetric = record { braided = ⊗-braided ; commutative = refl }