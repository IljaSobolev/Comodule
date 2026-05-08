open import Axiom.Extensionality.Propositional using (Extensionality)

module FiniteSupport (ext-≡ : ∀ {a b} → Extensionality a b) where

open import Relation.Binary.PropositionalEquality using (_≡_) renaming (sym to ≡-sym)
open import Relation.Binary.HeterogeneousEquality using (_≅_; refl; sym; trans; cong; cong₂)
open import Data.List using (List; []; _∷_; [_]; concat; map; _++_)
open import Data.List.Properties using (concat-concat; concat-map; concat-map-[_]; concat-[_]; concat-++; map-id; map-∘; map-++; ++-identityʳ; ++-assoc)
open import Function using (_∘_)

open import Categories.Monad using (Monad)

open import Cont
open import ContainerMorphismEquality ext-≡

open Container
open _⇒_

variable
  S S' : Set
  P : S → Set

data List∈ (P : S → Set) : List S → Set where
  []∈  : List∈ P []
  _∷∈_ : ∀ {x xs} → P x → List∈ P xs → List∈ P (x ∷ xs)


-- FREE ⊗-MONOID MONAD

T : Container → Container
T (S ⊲ P) = List S ⊲ List∈ P


-- UNIT

η : C ⇒ T C
η = [_] ⊲ λ {_ (x ∷∈ _) → x}

pfst : ∀ xs {ys} → List∈ P (xs ++ ys) → List∈ P xs
pfst [] p = []∈
pfst (_ ∷ xs) (x ∷∈ p) = x ∷∈ pfst xs p

psnd : ∀ {xs ys} → List∈ P (xs ++ ys) → List∈ P ys
psnd {xs = []} p = p
psnd {xs = _ ∷ xs} (x ∷∈ p) = psnd {xs = xs} p

ppair : ∀ {xs ys} → List∈ P xs → List∈ P ys → List∈ P (xs ++ ys)
ppair {xs = []} lx ly = ly
ppair {xs = _ ∷ _} (x ∷∈ lx) ly = x ∷∈ ppair lx ly

pfst-ppair : ∀ xs {ys} {l : List∈ P xs} {l'} → pfst xs {ys = ys} (ppair {xs = xs} l l') ≅ l
pfst-ppair [] {l = []∈} = refl
pfst-ppair (_ ∷ xs) {l = _ ∷∈ _} = cong (_ ∷∈_) (pfst-ppair xs)

psnd-ppair : ∀ xs {ys} {l : List∈ P xs} {l'} → psnd {xs = xs} {ys = ys} (ppair {xs = xs} l l') ≅ l'
psnd-ppair [] {l = []∈} = refl
psnd-ppair (_ ∷ xs) {l = _ ∷∈ _} = psnd-ppair xs

pair-ppair : ∀ xs {ys} {l : List∈ P (xs ++ ys)} → ppair {xs = xs} (pfst xs l) (psnd {xs = xs} l) ≅ l
pair-ppair [] = refl
pair-ppair (_ ∷ xs) {l = _ ∷∈ _} = cong (_ ∷∈_) (pair-ppair xs)


-- MULTIPLICATION

μp : ∀ s → List∈ P (concat s) → List∈ (List∈ P) s
μp [] _ = []∈
μp (_ ∷ _) xs = pfst _ xs ∷∈ μp _ (psnd xs)

μ : T (T C) ⇒ T C
μ = concat ⊲ μp


-- FUNCTORIALITY

T₁p : ∀ (f : C ⇒ D) → ∀ xs → List∈ (Pos D) (map (sf f) xs) → List∈ (Pos C) xs
T₁p f [] _ = []∈
T₁p f (_ ∷ _) (x ∷∈ xs) = pf f _ x ∷∈ T₁p f _ xs

T₁ : C ⇒ D → T C ⇒ T D
T₁ f = map (sf f) ⊲ T₁p f

_† : C ⇒ T D → T C ⇒ T D
f † = μ ∘C T₁ f

T₁p-id : ∀ xs p → T₁p {C} idC xs p ≅ p
T₁p-id [] []∈ = refl
T₁p-id (_ ∷ xs) (_ ∷∈ p) = cong₂ (λ z → _∷∈_ {xs = z} _) (sym (≡-to-≅ (map-id _))) (T₁p-id xs p)

T₁-id : T₁ idC ≡ idC {T C}
T₁-id = (≡-to-≅ ∘ map-id) ⊲-≡' λ _ → trans (T₁p-id _ _)

module _ (f : C ⇒ D) (g : D ⇒ E) where

  subst-comp : ∀ xs → List∈ P (map (sf (g ∘C f)) xs) → List∈ P (map (sf g) (map (sf f) xs))
  subst-comp [] p = p
  subst-comp (_ ∷ _) (x ∷∈ p) = x ∷∈ (subst-comp _ p)

  subst-comp-≅ : ∀ t p → subst-comp t p ≅ p
  subst-comp-≅ [] p = refl
  subst-comp-≅ (_ ∷ xs) (x ∷∈ p) = cong₂ (λ z → _∷∈_ {P = Pos E} {xs = z} _) (sym (≡-to-≅ (map-∘ _))) (subst-comp-≅ _ p)

  T₁p-comp : ∀ xs (p : List∈ (Pos E) (map (sf (g ∘C f)) xs)) → T₁p (g ∘C f) _ p ≅ T₁p f _ (T₁p g _ (subst-comp _ p))
  T₁p-comp [] p = refl
  T₁p-comp (_ ∷ xs) (_ ∷∈ p) = cong (_ ∷∈_) (T₁p-comp _ p)

  T₁-comp : T₁ (g ∘C f) ≡ T₁ g ∘C T₁ f
  T₁-comp = (≡-to-≅ ∘ map-∘) ⊲-≡' λ _ eq → trans (T₁p-comp _ _) (cong _ (trans (subst-comp-≅ _ _) eq))


-- UNITALITY

subst-idr : ∀ s → List∈ P (s ++ []) → List∈ P s
subst-idr [] p = p
subst-idr (_ ∷ s) (x ∷∈ p) = x ∷∈ subst-idr s p

subst-idr-≅ : ∀ s p → subst-idr {P = P} s p ≅ p
subst-idr-≅ [] p = refl
subst-idr-≅ (_ ∷ s) (_ ∷∈ p) = cong₂ (λ z → _∷∈_ {xs = z} _) (sym (≡-to-≅ (++-identityʳ _))) (subst-idr-≅ s p)

η-μ-p : ∀ s p → pf (η {T C}) s (μp _ p) ≅ subst-idr _ p
η-μ-p [] []∈ = refl
η-μ-p (_ ∷ s) (_ ∷∈ p) = cong (_ ∷∈_) (η-μ-p s p)

runit : μ ∘C η {T C} ≡ idC
runit = (≡-to-≅ ∘ concat-[_]) ⊲-≡' λ _ → trans (η-μ-p _ _) ∘ trans (subst-idr-≅ _ _)

subst-map : ∀ s → List∈ P (concat (map [_] s)) → List∈ P s
subst-map [] p = p
subst-map (_ ∷ s) (x ∷∈ p) = x ∷∈ subst-map s p

subst-map-≅ : ∀ s p → subst-map {P = P} s p ≅ p
subst-map-≅ [] p = refl
subst-map-≅ (_ ∷ s) (_ ∷∈ p) = cong₂ (λ z → _∷∈_ {xs = z} _) (sym (≡-to-≅ (concat-map-[_] _))) (subst-map-≅ s p)

η-μ-p' : ∀ s p → T₁p (η {C}) s (μp _ p) ≅ subst-map s p
η-μ-p' [] []∈ = refl
η-μ-p' (_ ∷ _) (_ ∷∈ _) = cong (_ ∷∈_) (η-μ-p' _ _)

lunit : μ ∘C T₁ η ≡ idC {T C}
lunit = (≡-to-≅ ∘ concat-map-[_]) ⊲-≡' λ _ → trans (η-μ-p' _ _) ∘ trans (subst-map-≅ _ _)


-- ASSOCIATIVITY

subst-assoc-++ : {xs ys zs : List S} → List∈ P (xs ++ (ys ++ zs)) → List∈ P ((xs ++ ys) ++ zs)
subst-assoc-++ {xs = []} l = l
subst-assoc-++ {xs = _ ∷ xs} (x ∷∈ l) = x ∷∈ subst-assoc-++ {xs = xs} l

subst-assoc-++-≅ : ∀ {xs ys zs} p → subst-assoc-++ {P = P} {xs} {ys} {zs} p ≅ p
subst-assoc-++-≅ {xs = []} p = refl
subst-assoc-++-≅ {xs = _ ∷ xs} (x ∷∈ p) = cong₂ (λ z → _∷∈_ {xs = z} x) (≡-to-≅ (++-assoc xs _ _)) (subst-assoc-++-≅ p)

subst-++ : ∀ xs {ys} → List∈ P (concat (xs ++ ys)) → List∈ P (concat xs ++ concat ys)
subst-++ [] p = p
subst-++ (xs ∷ xss) p = subst-assoc-++ {xs = xs} (ppair {xs = xs} (pfst _ p) (subst-++ xss (psnd p)))

pair-eq : ∀ {xs ys ys'} (p : List∈ P (xs ++ ys)) (q : List∈ P (xs ++ ys')) → ys ≅ ys' →
          pfst xs p ≅ pfst xs q → psnd {xs = xs} p ≅ psnd {xs = xs} q → p ≅ q
pair-eq {xs = xs} p q refl eq1 eq2 = trans (sym (pair-ppair xs)) (trans (cong₂ ppair eq1 eq2) (pair-ppair xs))

subst-++-≅ : ∀ xs {ys} p → subst-++ {S} {P} xs {ys} p ≅ p
subst-++-≅ [] p = refl
subst-++-≅ (xs ∷ xss) p =
  trans
    (subst-assoc-++-≅ _)
    (pair-eq _ _ (≡-to-≅ (concat-++ xss _)) (pfst-ppair xs) (trans (psnd-ppair xs) (subst-++-≅ xss _)))

subst-assoc : (s : List (List (List S))) → List∈ P (concat (concat s)) → List∈ P (concat (map concat s))
subst-assoc [] p = p
subst-assoc (x ∷ xs) p = ppair (pfst _ (subst-++ x p)) (subst-assoc xs (psnd (subst-++ x p)))

subst-assoc-≅ : ∀ s p → subst-assoc {S} {P} s p ≅ p
subst-assoc-≅ [] p = refl
subst-assoc-≅ (x ∷ xs) p =
  trans
    (pair-eq _ _ (≡-to-≅ (concat-concat xs)) (pfst-ppair (concat x)) (trans (psnd-ppair (concat x)) (subst-assoc-≅ xs _)))
    (subst-++-≅ x _)

list∈-1 : ∀ xs {ys zs} →
          (p : List∈ P (xs ++ (ys ++ zs))) →
          ------------------------------
          pfst xs (pfst (xs ++ ys) (subst-assoc-++ {xs = xs} p))
          ≅
          pfst xs p

list∈-1 [] p = refl
list∈-1 (_ ∷ xs) (_ ∷∈ p) = cong (_ ∷∈_) (list∈-1 xs p)

list∈-2 : ∀ xs {ys zs} →
          (p : List∈ P (xs ++ (ys ++ zs))) →
          --------------------------------------------
          psnd {xs = xs} (pfst (xs ++ ys) (subst-assoc-++ {xs = xs} p))
          ≅
          pfst ys (psnd {xs = xs} p)

list∈-2 [] p = refl
list∈-2 (_ ∷ xs) (_ ∷∈ p) = list∈-2 xs p

list∈-3 : ∀ xs {ys zs} →
          (p : List∈ P (xs ++ (ys ++ zs))) →
          -------------------------------------
          psnd {xs = xs ++ ys} (subst-assoc-++ {xs = xs} p)
          ≅
          psnd {xs = ys} (psnd {xs = xs} p)

list∈-3 [] p = refl
list∈-3 (_ ∷ xs) (_ ∷∈ p) = list∈-3 xs p

pfst-μp : ∀ xs {ys} → (p : List∈ P (concat (xs ++ ys))) → pfst xs (μp _ p) ≅ μp xs (pfst _ (subst-++ xs p))
pfst-μp [] p = refl
pfst-μp (x ∷ xs) p =
  cong₂ _∷∈_
    (trans (sym (pfst-ppair x)) (sym (list∈-1 x _)))
    (trans (pfst-μp xs _) (cong (μp xs) (sym (trans (list∈-2 x _) (cong (pfst _) (psnd-ppair x))))))

psnd-μp : ∀ xs {ys} → (p : List∈ P (concat (xs ++ ys))) → psnd {xs = xs} (μp _ p) ≅ μp ys (psnd (subst-++ xs p))
psnd-μp [] p = refl
psnd-μp (x ∷ xs) p =
  trans
    (psnd-μp xs _)
    (cong (μp _) (trans (cong (psnd {xs = concat xs}) (sym (psnd-ppair x))) (sym (list∈-3 x _))))

μp-assoc : ∀ {s} (p : List∈ P (concat (concat s))) → μp s (μp (concat s) p) ≅ T₁p μ s (μp _ (subst-assoc s p))
μp-assoc {s = []} p = refl
μp-assoc {s = s ∷ _} p =
  cong₂ _∷∈_
    (trans (pfst-μp _ p) (cong (pf μ s) (sym (pfst-ppair (concat s)))))
    (trans
      (trans (cong (μp _) (psnd-μp s p)) (μp-assoc _))
      (cong (λ z → T₁p μ _ (μp _ z)) (sym (psnd-ppair (concat s)))))

μ-assoc : μ ∘C T₁ μ ≡ μ {C} ∘C μ
μ-assoc = (≡-to-≅ ∘ concat-concat) ⊲-≡' λ s eq → trans (cong _ (trans eq (sym (subst-assoc-≅ s _)))) (sym (μp-assoc _))


-- NATURALITY OF MULTIPLICATION

subst-map-++ : ∀ (f : S → S') xs {ys} → List∈ P (map f (xs ++ ys)) → List∈ P (map f xs ++ map f ys)
subst-map-++ f [] p = p
subst-map-++ f (_ ∷ xs) (x ∷∈ p) = x ∷∈ subst-map-++ f xs p

subst-map-++-≅ : ∀ (f : S → S') xs {ys} p → subst-map-++ {P = P} f xs {ys} p ≅ p
subst-map-++-≅ f [] p = refl
subst-map-++-≅ f (_ ∷ xs) (_ ∷∈ p) = cong₂ (λ z → _∷∈_ {xs = z} _) (sym (≡-to-≅ (map-++ _ xs _))) (subst-map-++-≅ f xs p)

pfst-map : ∀ (f : C ⇒ D) xs {ys} →
          (p : List∈ (Pos D) (map (sf f) (xs ++ ys))) →
          ------------------------------------
          pfst xs (T₁p f _ p)
          ≅
          T₁p f _ (pfst (map (sf f) xs) (subst-map-++ (sf f) xs p))

pfst-map f [] p = refl
pfst-map f (_ ∷ xs) (_ ∷∈ p) = cong (_ ∷∈_) (pfst-map f xs p)

psnd-map : ∀ (f : C ⇒ D) xs {ys} →
          (p : List∈ (Pos D) (map (sf f) (xs ++ ys))) →
          ------------------------------------
          psnd {xs = xs} (T₁p f _ p)
          ≅
          T₁p f _ (psnd {xs = map (sf f) xs} (subst-map-++ (sf f) xs p))

psnd-map f [] p = refl
psnd-map f (_ ∷ xs) (_ ∷∈ p) = psnd-map f xs p

μ-nat-subst : (f : S → S') → ∀ s → List∈ P (map f (concat s)) → List∈ P (concat (map (map f) s))
μ-nat-subst f [] p = p
μ-nat-subst f (x ∷ xs) p = ppair (pfst _ (subst-map-++ f x p)) (μ-nat-subst f xs (psnd (subst-map-++ f x p)))

μ-nat-subst-≅ : ∀ (f : S → S') s p → μ-nat-subst {P = P} f s p ≅ p
μ-nat-subst-≅ f [] p = refl
μ-nat-subst-≅ f (x ∷ xs) p =
  trans
    (pair-eq _ _ (≡-to-≅ (concat-map xs)) (pfst-ppair _) (trans (psnd-ppair (map f x)) (μ-nat-subst-≅ f xs _)))
    (subst-map-++-≅ f x p)

μp-natural : ∀ (f : C ⇒ D) s p → μp s (T₁p f _ p) ≅ T₁p (T₁ f) s (μp _ (μ-nat-subst (sf f) s p))
μp-natural f [] p = refl
μp-natural f (x ∷ s) p = cong₂ _∷∈_
  (trans (pfst-map f x p) (cong (T₁p f x) (sym (pfst-ppair _))))
  (trans
    (cong (μp s) (psnd-map f x p))
    (trans
      (μp-natural f s _)
      (cong (T₁p _ s ∘ μp _) (sym (psnd-ppair (map (sf f) x))))))

μ-natural : (f : C ⇒ D) → T₁ f ∘C μ ≡ μ ∘C T₁ (T₁ f)
μ-natural f = (sym ∘ ≡-to-≅ ∘ concat-map) ⊲-≡' λ s eq → trans (μp-natural _ _ _) (cong _ (trans (μ-nat-subst-≅ (sf f) s _) eq))


-- NATURALITY OF UNIT

η-natural : (f : C ⇒ D) → η ∘C f ≡ T₁ f ∘C η
η-natural f = (λ _ → refl) ⊲-≡' λ {_ {_ ∷∈ _} refl → refl}


-- FREE ⊗-MONOID MONAD

free-⊗-monoid-monad : Monad Cont
free-⊗-monoid-monad = record
  { F = record
    { F₀ = T
    ; F₁ = T₁
    ; identity = T₁-id
    ; homomorphism = T₁-comp _ _
    ; F-resp-≈ = λ {_≡_.refl → _≡_.refl}
    }
  ; η = record { η = λ _ → η ; commute = η-natural ; sym-commute = λ f → ≡-sym (η-natural f) }
  ; μ = record { η = λ _ → μ ; commute = λ f → ≡-sym (μ-natural f) ; sym-commute = μ-natural }
  ; assoc = μ-assoc
  ; sym-assoc = ≡-sym μ-assoc
  ; identityˡ = lunit
  ; identityʳ = runit
  }