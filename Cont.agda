open import Axiom.Extensionality.Propositional using (Extensionality)

module Cont
  (ext-≡ : ∀ {a b} → Extensionality a b)
  where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (id; _∘_)
open import Relation.Binary.HeterogeneousEquality using (_≅_; refl; sym; cong; cong₂; ≅-to-type-≡)
open import Relation.Binary.PropositionalEquality using (_≡_; isEquivalence) renaming (refl to ≡-refl)
open import Axiom.Extensionality.Heterogeneous using (≡-ext⇒≅-ext)

open import Categories.Category
open import Categories.Object.Product

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
≅-to-≡ refl = ≡-refl


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
  eta-equality
  constructor
    _⊲_
  field
    sf : Shp C → Shp D
    pf : ∀ s → Pos D (sf s) → Pos C s

open _⇒_


-- CHARACTERISATION OF EQUALITY BETWEEN TWO MORPHISMS

_⊲-≡_ : {f g : C ⇒ D} →
        (∀ s → sf f s ≅ sf g s) →
        (∀ {s} → pf f s ≅ pf g s) →
        ------
        f ≡ g

_⊲-≡_ shp-≅ pos-≅ =
  ≅-to-≡ (cong₂ {C = λ _ _ → _ ⇒ _} _⊲_ (ext-≅ shp-≅) (ext-≅ (λ _ → pos-≅)))

_⊲-≡'_ : {f g : C ⇒ D} →
         (∀ s → sf f s ≅ sf g s) →
         (∀ {s p p'} → p ≅ p' → pf f s p ≅ pf g s p') →
         ------
         f ≡ g

_⊲-≡'_ {D = D} shp-≅ pos-≅ =
  ≅-to-≡ (cong₂ _⊲_ (ext-≅ shp-≅) (ext-≅ (λ x → ext-≅' (cong (Pos D) (shp-≅ x)) pos-≅)))


-- IDENTITY AND COMPOSITION

idᶜ : C ⇒ C
idᶜ = id ⊲ λ _ → id

infix 5 _∘ᶜ_
_∘ᶜ_ : D ⇒ E → C ⇒ D → C ⇒ E
(f ⊲ g) ∘ᶜ (h ⊲ i) = (f ∘ h) ⊲ λ s → i s ∘ g (h s)

-- CONTAINERS FORM A CATEGORY

Cont : Category _ _ _
Cont = record
  { Obj = Container
  ; _⇒_ = _⇒_
  ; _≈_ = _≡_
  ; id = idᶜ
  ; _∘_ = _∘ᶜ_
  ; assoc = (λ _ → refl) ⊲-≡ refl
  ; sym-assoc = (λ _ → refl) ⊲-≡ refl
  ; identityˡ = (λ _ → refl) ⊲-≡ refl
  ; identityʳ = (λ _ → refl) ⊲-≡ refl
  ; identity² = ≡-refl
  ; equiv = isEquivalence
  ; ∘-resp-≈ = λ {≡-refl ≡-refl → ≡-refl}
  }


-- CONT HAS BINARY PRODUCTS

_×ᶜ_ : Container → Container → Container
C ×ᶜ D = (Shp C × Shp D) ⊲ λ {(s , s') → Pos C s ⊎ Pos D s'}

proj₁ᶜ : C ×ᶜ D ⇒ C
proj₁ᶜ = proj₁ ⊲ λ _ → inj₁

proj₂ᶜ : C ×ᶜ D ⇒ D
proj₂ᶜ = proj₂ ⊲ λ _ → inj₂

⟨_,_⟩ᶜ : C ⇒ D → C ⇒ E → C ⇒ D ×ᶜ E
⟨ f ⊲ g , f' ⊲ g' ⟩ᶜ = (λ s → f s , f' s) ⊲ λ {s (inj₁ x) → g s x; s (inj₂ y) → g' s y}

_×-c_ : ∀ C D → Product Cont C D
C ×-c D = record
  { A×B = C ×ᶜ D
  ; π₁ = proj₁ᶜ
  ; π₂ = proj₂ᶜ
  ; ⟨_,_⟩ = ⟨_,_⟩ᶜ
  ; project₁ = (λ _ → refl) ⊲-≡ refl
  ; project₂ = (λ _ → refl) ⊲-≡ refl
  ; unique = λ {≡-refl ≡-refl → (λ _ → refl) ⊲-≡ ext-≅ λ {(inj₁ _) → refl; (inj₂ _) → refl}}
  }