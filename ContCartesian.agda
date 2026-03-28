open import Axiom.Extensionality.Propositional using (Extensionality)

module ContCartesian
  (ext-≡ : ∀ {a b} → Extensionality a b)
  where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.HeterogeneousEquality using (refl)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Object.Terminal using (Terminal)

open import Cont
open import ContainerMorphismEquality ext-≡


-- BINARY PRODUCTS

infix 7 _×ᶜ_
_×ᶜ_ : Container → Container → Container
(S ⊲ P) ×ᶜ (S' ⊲ P') = (S × S') ⊲ λ {(s , s') → P s ⊎ P' s'}

proj₁ᶜ : C ×ᶜ D ⇒ C
proj₁ᶜ = proj₁ ⊲ λ _ → inj₁

proj₂ᶜ : C ×ᶜ D ⇒ D
proj₂ᶜ = proj₂ ⊲ λ _ → inj₂

⟨_,_⟩ᶜ : C ⇒ D → C ⇒ E → C ⇒ D ×ᶜ E
⟨ f ⊲ g , f' ⊲ g' ⟩ᶜ = (λ s → f s , f' s) ⊲ λ {s (inj₁ x) → g s x; s (inj₂ y) → g' s y}

cont-binary-products : BinaryProducts Cont
BinaryProducts.product cont-binary-products {C} {D} = record
  { A×B = C ×ᶜ D
  ; π₁ = proj₁ᶜ
  ; π₂ = proj₂ᶜ
  ; ⟨_,_⟩ = ⟨_,_⟩ᶜ
  ; project₁ = _≡_.refl
  ; project₂ = _≡_.refl
  ; unique = λ {_≡_.refl _≡_.refl → (λ _ → refl) ⊲-≡ λ _ → ext-≅ λ {(inj₁ _) → refl; (inj₂ _) → refl}}
  }


-- TERMINAL OBJECT

𝟙ᶜ : Container
𝟙ᶜ = ⊤ ⊲ λ _ → ⊥

!ᶜ : C ⇒ 𝟙ᶜ
!ᶜ = (λ _ → tt) ⊲ λ _ ()

cont-terminal : Terminal Cont
cont-terminal = record
  { ⊤ = 𝟙ᶜ
  ; ⊤-is-terminal = record { ! = !ᶜ ; !-unique = λ _ → (λ _ → refl) ⊲-≡ λ _ → ext-≅ (λ ()) }
  }


-- CONT IS CARTESIAN

cont-cartesian : Cartesian Cont
cont-cartesian = record
  { terminal = cont-terminal
  ; products = cont-binary-products
  }