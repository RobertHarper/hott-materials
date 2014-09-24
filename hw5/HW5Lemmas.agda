{-# OPTIONS --type-in-type --without-K #-}

module HW5Lemmas where

  U = Set

  _∘_ : ∀ {A : U} {B : A → U} {C : (a : A) → B a → U}
        → (g : {a : A} → (b : B a) → C a b) → (f : (a : A) → B a)
        → (a : A) → (C a (f a))
  g ∘ f = λ x → g (f x)

  -- Top
  record ⊤ : U where
    constructor ✭

  -- Bottom
  data ⊥ : U where

  ¬_ : U → U
  ¬ A = A → ⊥

  abort : {A : U} → ⊥ → A
  abort ()

  -- Identity
  data _==_ {A : U} (a : A) : A → U where
    refl : a == a

  infixr 4 _∙_
  _∙_ : {A : U} {x y z : A} (p : x == y) (q : y == z) → x == z
  refl ∙ p = p

  _⁻¹ : {A : U} {x y : A} (p : x == y) → y == x
  refl ⁻¹ = refl

  ap : {A B : U} (f : A → B) {x y : A} (p : x == y) → f x == f y
  ap f refl = refl

  tr : {A : U} (B : A → U) {x y : A} (p : x == y) → B x → B y
  tr B refl b = b

  -- Sigma
  infixr 1 _,_
  record Σ (A : U) (B : A → U) : U where
    constructor _,_
    field
      fst : A
      snd : B fst
  open Σ public
  _×_ : U → U → U
  A × B = Σ A λ _ → B

  -- Truncation level
  is-contr : U → U
  is-contr A = Σ A λ x → ∀ y → x == y

  is-prop : U → U
  is-prop A = ∀ (x y : A) → x == y

  is-set : U → U
  is-set A = ∀ (x y : A) → is-prop (x == y)

  data tlevel : U where
    -2 : tlevel
    suc : tlevel → tlevel
  -1 = suc -2

  is-type : tlevel → U → U
  is-type -2 A = is-contr A
  is-type (suc l) A = (x y : A) → is-type l (x == y)

  -- Equivalence
  is-equiv : {A B : U} → (A → B) → U
  is-equiv {A}{B} f = (Σ (B → A) λ g → ∀ y → f (g y) == y)
                    × (Σ (B → A) λ g → ∀ x → g (f x) == x)

  _≃_ : U → U → U
  A ≃ B = Σ (A → B) is-equiv

  -- Section 2
  postulate
    prop-is-set : (A : U) → is-prop A → is-set A

  -- Section 3
  postulate
    funext : {A : U} {B : A → U} {f g : (x : A) → B x} → ((x : A) → f x == g x) → f == g

  postulate
    equiv-inv : {A B : U} → (A ≃ B) → (B ≃ A)
    equiv-compose : {A B C : U} → (B ≃ C) → (A ≃ B) → (A ≃ C)
    is-equiv-is-prop : {A B : U} (f : A → B) → is-prop (is-equiv f)
  _∘≃_ = equiv-compose

  postulate
    product-level : {A : U} {B : A → U} {n : tlevel}
      → ((x : A) → is-type n (B x))
      → is-type n ((x : A) → B x)
    sigma-level : {A : U} {B : A → U} {n : tlevel}
      → is-type n A → ((x : A) → is-type n (B x))
      → is-type n (Σ A B)

  postulate
    subtype-path : {A : U} {B : A → U} (β : (x : A) → is-prop (B x))
      (m n : Σ A B) → fst m == fst n → m == n
    subtype-path-equiv : {A : U} {B : A → U} (β : (x : A) → is-prop (B x))
      (m n : Σ A B) → (fst m == fst n) ≃ (m == n)

  -- Section 4
  postulate
    is-type-is-prop : (n : tlevel) (A : U) → is-prop (is-type n A)

  postulate
    ua : {A B : U} → (A ≃ B) → A == B
    ua-equiv : {A B : U} → (A ≃ B) ≃ (A == B)

