open import Axiom.Extensionality.Propositional using (Extensionality)

module ContainerMorphismEquality
  (ext-≡ : ∀ {a b} → Extensionality a b)
  where

open import Function using (_∘_)
open import Relation.Binary.HeterogeneousEquality using (_≅_; refl; cong; cong₂; ≅-to-type-≡)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Axiom.Extensionality.Heterogeneous using (≡-ext⇒≅-ext)

open import Cont

open Container
open _⇒_


-- HETEROGENEOUS FUNCTION EXTENSIONALITY

Extensionality-≅ : ∀ a b → Set _
Extensionality-≅ a b =
  {A : Set a} {P Q : A → Set b}
  {f : ∀ x → P x} {g : ∀ x → Q x} →
  (∀ x → f x ≅ g x) → f ≅ g

ext-≅ : ∀ {a b} → Extensionality-≅ a b
ext-≅ f≗g = ≡-ext⇒≅-ext ext-≡ (≅-to-type-≡ ∘ f≗g) f≗g


-- A VARIANT OF HETEROGENEOUS EXTENSIONALITY WHERE THE DOMAINS
-- OF THE FUNCTIONS MAY NOT BE DEFINITIONALLY EQUAL

Extensionality-≅' : ∀ a b → Set _
Extensionality-≅' a b =
  {A B : Set a} {P : A → Set b} {Q : B → Set b}
  {f : ∀ x → P x} {g : ∀ x → Q x} →
  A ≅ B → (∀ {x y} → x ≅ y → f x ≅ g y) → f ≅ g

ext-≅' : ∀ {a b} → Extensionality-≅' a b
ext-≅' refl f≗g = ext-≅ (λ _ → f≗g refl)


-- HETEROGENEOUS EQUALITY AT EQUAL TYPES IMPLIES PROPOSITIONAL EQUALITY

≅-to-≡ : {S : Set} {x y : S} → x ≅ y → x ≡ y
≅-to-≡ refl = _≡_.refl

≡-to-≅ : {S : Set} {x y : S} → x ≡ y → x ≅ y
≡-to-≅ _≡_.refl = refl


-- CHARACTERISATION OF EQUALITY BETWEEN TWO MORPHISMS

_⊲-≡_ : {f g : C ⇒ D} →
        (∀ s → sf f s ≅ sf g s) →
        (∀ s → pf f s ≅ pf g s) →
        ------
        f ≡ g

_⊲-≡_ shp-≅ pos-≅ =
  ≅-to-≡ (cong₂ _⊲_ (ext-≅ shp-≅) (ext-≅ pos-≅))

_⊲-≡'_ : {f g : C ⇒ D} →
         (∀ s → sf f s ≅ sf g s) →
         (∀ s {p p'} → p ≅ p' → pf f s p ≅ pf g s p') →
         ------
         f ≡ g

_⊲-≡'_ {D = D} shp-≅ pos-≅ =
  ≅-to-≡ (cong₂ _⊲_ (ext-≅ shp-≅) (ext-≅ (λ x → ext-≅' (cong (Pos D) (shp-≅ x)) (pos-≅ x))))