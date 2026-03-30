open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.HeterogeneousEquality using (_≅_; refl; cong; cong₂; sym; trans)
open import Function using (_∘_)
open import Axiom.Extensionality.Propositional using (Extensionality)

module Tree
  (ext-≡ : ∀ {a b} → Extensionality a b)
  where

open import Cont
open import ContainerMorphismEquality ext-≡

open Container
open _⇒_

variable
  S : Set
  P : S → Set
  s p : S


-- TREES AND PATHS

data Tree (S : Set) (P : S → Set) : Set where
  leaf : Tree S P
  node : ∀ s → (P s → Tree S P) → Tree S P

data Path {S} {P} : Tree S P → Set where
  stop : Path leaf
  step : ∀ t → Path (t p) → Path (node s t)

variable
  t : Tree S P


-- TREE MONAD

𝒯 : Container → Container
𝒯 (S ⊲ P) = Tree S P ⊲ Path


-- UNIT OF TREE MONAD

η : ∀ C → C ⇒ 𝒯 C
η _ = (λ s → node s (λ _ → leaf)) ⊲ λ { _ (step {p = p} _ _) → p }


-- GRAFTING, PATH PROJECTIONS AND KLEISLI EXTENSION MAP OF TREE MONAD

graft : ∀ t → (Path t → Tree S P) → Tree S P
graft leaf f = f stop
graft (node s t) f = node s (λ p → graft (t p) (f ∘ step _))

pfst : {f : Path t → Tree S P} → Path (graft t f) → Path t
pfst {t = leaf} _ = stop
pfst {t = node _ _} (step _ q) = step _ (pfst q)

psnd : {f : Path t → Tree S P} (p : Path (graft t f)) → Path (f (pfst p))
psnd {t = leaf} q = q
psnd {t = node _ t} (step {p = p} _ q) = psnd {t = t p} q

shp† : C ⇒ 𝒯 D → Tree (Shp C) (Pos C) → Tree (Shp D) (Pos D)
shp† (f ⊲ g) leaf = leaf
shp† (f ⊲ g) (node s t) = graft (f s) (λ q → shp† (f ⊲ g) (t (g s q)))

pos† : (f : C ⇒ 𝒯 D) → Path (shp† f t) → Path t
pos† {t = leaf} _ q = stop
pos† {t = node s t} (f ⊲ g) q = step t (pos† _ (psnd {t = f s} q))

_† : C ⇒ 𝒯 D → 𝒯 C ⇒ 𝒯 D
f † = shp† f ⊲ λ t → pos† {t = t} f


-- LEFT UNIT

shp-id : ∀ t → shp† (η C) t ≅ t
shp-id leaf = refl
shp-id (node s t) = cong (node s) (ext-≅ (shp-id ∘ t))

pos-id : (t : Tree (Shp C) (Pos C)) → ∀ p → pos† {t = t} (η C) p ≅ p
pos-id leaf stop = refl
pos-id (node _ t) (step _ _) = cong₂ step (sym (ext-≅ (shp-id ∘ t))) (pos-id _ _)

η†≡id : η C † ≡ idC
η†≡id = shp-id ⊲-≡' λ _ → trans (pos-id _ _)


-- RIGHT UNIT

graft-id : (t : Tree S P) → graft t (λ _ → leaf) ≅ t
graft-id leaf = refl
graft-id (node s t) = cong (node s) (ext-≅ (graft-id ∘ t))

pfst-id : (t : Tree S P) → ∀ p → pfst {t = t} {f = λ _ → leaf} p ≅ p
pfst-id leaf stop = refl
pfst-id (node s t) (step _ p) = cong₂ step (sym (ext-≅ (graft-id ∘ t))) (pfst-id (t _) p)

f†∘η≡f : (f : C ⇒ 𝒯 D) → f † ∘C η C ≡ f
f†∘η≡f f = (graft-id ∘ _) ⊲-≡' λ _ → cong _ ∘ trans (pfst-id _ _)


-- ASSOCIATIVITY

graft-assoc : (v : Path t → Tree _ _)
              (w : ∀ {p} → Path (v p) → Tree _ _) →
              ---------------------------------------
              graft t (λ p → graft (v p) w)
              ≅
              graft (graft t v) (λ q → w (psnd {f = v} q))

graft-assoc {t = leaf} v w = refl
graft-assoc {t = node s t} v w = cong (node s) (ext-≅ (λ p → graft-assoc {t = t p} _ _))

graft-shp†-comm : (f : C ⇒ 𝒯 D) →
                  ∀ t v →
                  ---------------------------
                  shp† f (graft t v)
                  ≅
                  graft (shp† f t) (λ q → shp† f (v (pos† f q)))

graft-shp†-comm f leaf v =
  refl
graft-shp†-comm f (node s t) v =
  trans
    (cong (graft (sf f s)) (ext-≅ (λ x → graft-shp†-comm _ (t _) _)))
    (graft-assoc {t = sf f s} (λ z → shp† _ (t _)) _)

shp†-assoc : (f : C ⇒ 𝒯 D) (g : D ⇒ 𝒯 E) →
             ∀ t →
             ------------------
             shp† (g † ∘C f) t
             ≅
             shp† g (shp† f t)

shp†-assoc f g leaf =
  refl
shp†-assoc f g (node s t) = sym (
  trans
    (graft-shp†-comm _ (sf f s) _)
    (cong (graft (shp† _ (sf f s))) (ext-≅ (λ _ → sym (shp†-assoc _ _ (t _)))))
  )

[g†∘f]†≡g†∘f† : (f : C ⇒ 𝒯 D) (g : D ⇒ 𝒯 E) → (g † ∘C f) † ≡ g † ∘C f †
[g†∘f]†≡g†∘f† f g = shp†-assoc _ _ ⊲-≡' {!   !}