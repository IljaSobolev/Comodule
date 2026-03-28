open import Categories.Category using (Category)
open import Categories.Monad using (Monad)

module Module {o ℓ e} {𝒞 : Category o ℓ e} (M : Monad 𝒞) (𝒟 : Category o ℓ e) where

open import Level using (_⊔_)

open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Properties using (Contravariant)
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ᵥ_) renaming (id to ntid)

open Monad M using () renaming (F to T; η to Tη; μ to Tμ)
open T using () renaming (F₀ to T₀)
open Category 𝒟 hiding (_⇒_)

record IsModule (F : Functor 𝒞 𝒟) (c : NaturalTransformation (F ∘F T) F) : Set (o ⊔ e) where
  open NaturalTransformation c renaming (η to cη)
  open Functor F using (F₁)
  field
    assoc : ∀ {X} → cη X ∘ cη (T₀ X) ≈ cη X ∘ F₁ (Tμ.η X)
    identity : ∀ {X} → cη X ∘ F₁ (Tη.η X) ≈ id

record Module : Set (o ⊔ ℓ ⊔ e) where
  field
    F        : Functor 𝒞 𝒟
    c        : NaturalTransformation (F ∘F T) F
    isModule : IsModule F c

record _⇒_ (X Y : Module) : Set (o ⊔ ℓ ⊔ e) where
  module X = Module X
  module Y = Module Y
  open NaturalTransformation using (η)
  field
    θ    : NaturalTransformation X.F Y.F
    comm : ∀ {X} → η θ X ∘ η X.c X ≈ η Y.c X ∘ η θ (T₀ X)

Mod : Category (o ⊔ ℓ ⊔ e) _ _
Mod = record
  { Obj = Module
  ; _⇒_ = _⇒_
  ; _≈_ = λ x y → ∀ {X} → η (θ x) X ≈ η (θ y) X
  ; id = record { θ = ntid ; comm = identityˡ ○ ⟺ identityʳ }
  ; _∘_ = λ x y → record { θ = θ x ∘ᵥ θ y ; comm = assoc ○ refl⟩∘⟨ comm y ○ sym-assoc ○ comm x ⟩∘⟨refl ○ assoc}
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv = record { refl = Equiv.refl; sym = λ z → ⟺ z ; trans = λ x y → x ○ y }
  ; ∘-resp-≈ = λ x y → x ⟩∘⟨ y
  }
  where
  open _⇒_ using (θ; comm)
  open NaturalTransformation using (η)
  open HomReasoning using (refl⟩∘⟨_; _⟩∘⟨refl; _⟩∘⟨_; ⟺; _○_)