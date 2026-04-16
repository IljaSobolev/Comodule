open import Axiom.Extensionality.Propositional using (Extensionality)

module ContCocartesian
  (ext-≡ : ∀ {a b} → Extensionality a b)
  where

open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.HeterogeneousEquality using (refl)
open import Function using (id)

open import Categories.Category.Cocartesian using (Cocartesian; BinaryCoproducts)
open import Categories.Object.Initial using (Initial)

open import Cont
open import ContainerMorphismEquality ext-≡


-- BINARY COPRODUCTS

infix 6 _+ᶜ_
_+ᶜ_ : Container → Container → Container
(S ⊲ P) +ᶜ (S' ⊲ P') = (S ⊎ S') ⊲ [ P , P' ]

inj₁ᶜ : C ⇒ C +ᶜ D
inj₁ᶜ = inj₁ ⊲ λ _ → id

inj₂ᶜ : D ⇒ C +ᶜ D
inj₂ᶜ = inj₂ ⊲ λ _ → id

[_,_]ᶜ : C ⇒ E → D ⇒ E → C +ᶜ D ⇒ E
[ f ⊲ g , f' ⊲ g' ]ᶜ = [ f , f' ] ⊲ [ g , g' ]

𝟘ᶜ : Container
𝟘ᶜ = ⊥ ⊲ λ _ → ⊥

!ᶜ : 𝟘ᶜ ⇒ C
!ᶜ = (λ ()) ⊲ λ ()

cont-binary-coproducts : BinaryCoproducts Cont
BinaryCoproducts.coproduct cont-binary-coproducts {C} {D} = record
  { A+B = C +ᶜ D
  ; i₁ = inj₁ᶜ
  ; i₂ = inj₂ᶜ
  ; [_,_] = [_,_]ᶜ
  ; inject₁ = _≡_.refl
  ; inject₂ = _≡_.refl
  ; unique = λ {_≡_.refl _≡_.refl → [ (λ _ → refl) , (λ _ → refl) ] ⊲-≡ [ (λ _ → refl) , (λ _ → refl) ]}
  }


-- INITIAL OBJECT

cont-initial : Initial Cont
cont-initial = record
  { ⊥ = 𝟘ᶜ
  ; ⊥-is-initial = record { ! = !ᶜ ; !-unique = λ _ → (λ ()) ⊲-≡ λ ()}
  }


-- CONT IS COCARTESIAN

cont-cocartesian : Cocartesian Cont
cont-cocartesian = record
  { initial = cont-initial
  ; coproducts = cont-binary-coproducts
  }


-- COINTERPRETATION MAPS COPRODUCTS TO PRODUCTS

⟪⟫-proj₁ : ⟪ D +ᶜ E ⟫₀ → ⟪ D ⟫₀
⟪⟫-proj₁ c x = c (inj₁ x)

⟪⟫-proj₂ : ⟪ D +ᶜ E ⟫₀ → ⟪ E ⟫₀
⟪⟫-proj₂ c x = c (inj₂ x)

⟪⟫-pair : (⟪ C ⟫₀ → ⟪ D ⟫₀) → (⟪ C ⟫₀ → ⟪ E ⟫₀) → ⟪ C ⟫₀ → ⟪ D +ᶜ E ⟫₀
⟪⟫-pair f g c (inj₁ x) = f c x
⟪⟫-pair f g c (inj₂ y) = g c y

⟪⟫-× : ⟪ D ⟫₀ × ⟪ E ⟫₀ → ⟪ D +ᶜ E ⟫₀
⟪⟫-× (f , g) (inj₁ x) = f x
⟪⟫-× (f , g) (inj₂ x) = g x