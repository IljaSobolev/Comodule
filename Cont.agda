module Cont where

open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; isEquivalence)

open import Categories.Category using (Category)
open import Categories.Functor.Properties using (Contravariant)
open import Categories.Category.Instance.Sets using (Sets)


-- CONTAINERS AND CONTAINER MORPHISMS

record Container : Set₁ where
  constructor
    _⊲_
  field
    Shp : Set
    Pos : Shp → Set

open Container

variable
  C D E F : Container

infix 4 _⇒_
record _⇒_ C D : Set where
  constructor
    _⊲_
  field
    sf : Shp C → Shp D
    pf : ∀ s → Pos D (sf s) → Pos C s

open _⇒_


-- IDENTITY AND COMPOSITION

idC : C ⇒ C
idC = id ⊲ λ _ → id

infixr 5 _∘C_
_∘C_ : D ⇒ E → C ⇒ D → C ⇒ E
(f ⊲ g) ∘C (h ⊲ i) = (f ∘ h) ⊲ λ s → i s ∘ g (h s)


-- CONTAINERS FORM A CATEGORY

Cont : Category _ _ _
Cont = record
  { Obj = Container
  ; _⇒_ = _⇒_
  ; _≈_ = _≡_
  ; id = idC
  ; _∘_ = _∘C_
  ; assoc = refl
  ; sym-assoc = refl
  ; identityˡ = refl
  ; identityʳ = refl
  ; identity² = refl
  ; equiv = isEquivalence
  ; ∘-resp-≈ = λ {refl refl → refl}
  }


-- COINTERPRETATION OF CONTAINERS

⟪_⟫₀ : Container → Set
⟪ S ⊲ P ⟫₀ = ∀ s → P s

⟪_⟫₁ : C ⇒ D → ⟪ D ⟫₀ → ⟪ C ⟫₀
⟪ f ⊲ g ⟫₁ a s = g s (a (f s))

⟪⟫ : Contravariant Cont (Sets _)
⟪⟫ = record
  { F₀ = ⟪_⟫₀
  ; F₁ = ⟪_⟫₁
  ; identity = λ _ → refl
  ; homomorphism = λ _ → refl
  ; F-resp-≈ = λ {refl _ → refl}
  }