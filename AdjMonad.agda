open import Categories.Category using (Category)
open import Categories.Adjoint using (Adjoint)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)

module AdjMonad
  {o o′ ℓ ℓ′ e e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′}
  (L : Functor C D) (R : Functor D C) (adjoint : Adjoint L R)
  where

open import Data.Product using (_,_)

open import Categories.Category.Construction.Functors using (Functors; product)
open import Categories.Category.Product using (Product; _⁂_)
open import Categories.Functor.Monoidal using (IsMonoidalFunctor)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper; _∘ₕ_; _∘ʳ_; _∘ˡ_) renaming (id to ntid)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Construction.Endofunctors using (Endofunctors-Monoidal; Endofunctors)

open Functor using (₀; ₁; identity; homomorphism; F-resp-≈)
open NaturalTransformation using (η; commute; sym-commute)
open Adjoint adjoint using (unit; counit; zig; zag)
open Category C
open HomReasoning

module CC = Monoidal (Endofunctors-Monoidal C)
module DD = Monoidal (Endofunctors-Monoidal D)

T : Functor (Functors D D) (Functors C C)
T = record
  { F₀ = λ F → R ∘F F ∘F L
  ; F₁ = λ f → R ∘ˡ f ∘ʳ L
  ; identity = identity R
  ; homomorphism = homomorphism R
  ; F-resp-≈ = λ z → F-resp-≈ R z
  }

ε : NaturalTransformation idF (₀ T idF)
ε = ntHelper record { η = unit.η ; commute = unit.commute }

μ : ∀ F G → NaturalTransformation ((R ∘F F ∘F L) ∘F (R ∘F G ∘F L)) (R ∘F (F ∘F G) ∘F L)
μ F G = ntHelper record { η = η (R ∘ˡ F ∘ˡ counit ∘ʳ (G ∘F L)) ; commute = commute (R ∘ˡ F ∘ˡ counit ∘ʳ (G ∘F L)) }

⊗-homo : NaturalTransformation (product ∘F (T ⁂ T)) (T ∘F product)
⊗-homo = ntHelper record
  { η = λ { (F , G) → μ F G }
  ; commute = λ { {F , G} {F' , G'} (h , h') →
    begin
      η (μ F' G') _ ∘ ₁ (R ∘F F' ∘F L ∘F R) (η h' _) ∘ ₁ R (η h _)
    ≈⟨ refl⟩∘⟨ sym-commute (R ∘ˡ h) _ ⟩
      η (μ F' G') _ ∘ ₁ R (η h _) ∘ ₁ (R ∘F F ∘F L ∘F R) (η h' _)
    ≈⟨ sym-assoc ○ sym-commute (R ∘ˡ h) _ ⟩∘⟨refl ○ assoc ⟩
      ₁ R (η h _) ∘ ₁ (R ∘F F) (counit.η _) ∘ ₁ (R ∘F F ∘F L ∘F R) (η h' _)
    ≈⟨ refl⟩∘⟨ commute (R ∘ˡ F ∘ˡ counit) _ ⟩
      ₁ R (η h _) ∘ ₁ (R ∘F F) (η h' _) ∘ η (μ F G) _
    ≈⟨ sym-assoc ○ (⟺ (homomorphism R) ○ F-resp-≈ R (commute h _)) ⟩∘⟨refl ⟩
      ₁ R (η (h ∘ₕ h') _) ∘ η (μ F G) _
    ∎ } }

associativity : ∀ {X Y Z : Functor D D} {x : Obj} →
                --------------------------------------------
                ₁ R (η (DD.associator.from {X} {Y} {Z}) _) ∘ η (η ⊗-homo (X ∘F Y , Z)) x ∘ η (η ⊗-homo (X , Y) ∘ₕ ntid {F = ₀ T Z}) _
                ≈
                η (η ⊗-homo (X , Y ∘F Z)) _ ∘ η (ntid {F = ₀ T X} ∘ₕ η ⊗-homo (Y , Z)) _ ∘ η (CC.associator.from {₀ T X} {₀ T Y} {₀ T Z}) _

associativity {X} {Y} {Z} =
  begin
    ₁ R (Category.id D) ∘ ₁ (R ∘F X ∘F Y) (counit.η _) ∘ ₁ (R ∘F X ∘F Y ∘F L) id ∘ ₁ (R ∘F X) (counit.η _)
  ≈⟨ identity R ⟩∘⟨refl ○ identityˡ ⟩
    ₁ (R ∘F X ∘F Y) (counit.η _) ∘ ₁ (R ∘F X ∘F Y ∘F L) id ∘ ₁ (R ∘F X) (counit.η _)
  ≈⟨ refl⟩∘⟨ (identity (R ∘F X ∘F Y ∘F L) ⟩∘⟨refl ○ identityˡ) ⟩
    ₁ (R ∘F X ∘F Y) (counit.η _) ∘ ₁ (R ∘F X) (counit.η _)
  ≈⟨ sym-commute (R ∘ˡ X ∘ˡ counit) _ ⟩
    ₁ (R ∘F X) (counit.η _) ∘ ₁ (R ∘F X ∘F L ∘F R ∘F Y) (counit.η _)
  ≈⟨ refl⟩∘⟨ ⟺ identityʳ ○ refl⟩∘⟨ ⟺ identityʳ ⟩
    ₁ (R ∘F X) (counit.η _) ∘ (₁ (R ∘F X ∘F L ∘F R ∘F Y) (counit.η _) ∘ id) ∘ id
  ∎

unitaryˡ : {X : Functor D D} {x : Obj} →
           -----------------------------------------------
           ₁ R (η (DD.unitorˡ.from {X}) _) ∘ η (η ⊗-homo (idF , X)) x ∘ η (ε ∘ₕ ntid {F = ₀ T X}) _
           ≈
           η (CC.unitorˡ.from {₀ T X}) _

unitaryˡ =
  begin
    ₁ R (Category.id D) ∘ ₁ R (η counit _) ∘ ₁ (R ∘F L) id ∘ η unit _
  ≈⟨ identity R ⟩∘⟨refl ○ identityˡ ⟩
    ₁ R (η counit _) ∘ ₁ (R ∘F L) id ∘ η unit _
  ≈⟨ refl⟩∘⟨ (identity (R ∘F L) ⟩∘⟨refl ○ identityˡ) ⟩
    ₁ R (η counit _) ∘ η unit _
  ≈⟨ zag ⟩
    id
  ∎

unitaryʳ : {X : Functor D D} {x : Obj} →
           -----------------------------------------------
           ₁ R (η (DD.unitorʳ.from {X}) _) ∘ η (η ⊗-homo (X , idF)) x ∘ η (ntid {F = ₀ T X} ∘ₕ ε) _
           ≈
           η (CC.unitorʳ.from {₀ T X}) _

unitaryʳ {X} =
  begin
    ₁ R (Category.id D) ∘ ₁ (R ∘F X) (counit.η _) ∘ ₁ (R ∘F X ∘F L) (unit.η _) ∘ id
  ≈⟨ identity R ⟩∘⟨refl ○ identityˡ ⟩
    ₁ (R ∘F X) (counit.η _) ∘ ₁ (R ∘F X ∘F L) (unit.η _) ∘ id
  ≈⟨ refl⟩∘⟨ identityʳ ⟩
    ₁ (R ∘F X) (counit.η _) ∘ ₁ (R ∘F X ∘F L) (unit.η _)
  ≈⟨ ⟺ (homomorphism (R ∘F X)) ○ F-resp-≈ (R ∘F X) zig ⟩
    ₁ (R ∘F X) (Category.id D)
  ≈⟨ identity (R ∘F X) ⟩
    id
  ∎

monoidal : IsMonoidalFunctor (Endofunctors D) (Endofunctors C) T
monoidal = record
  { ε = ε
  ; ⊗-homo = ⊗-homo
  ; associativity = λ {X} {Y} {Z} → associativity {X} {Y} {Z}
  ; unitaryˡ = λ {X} → unitaryˡ {X}
  ; unitaryʳ = λ {X} → unitaryʳ {X}
  }