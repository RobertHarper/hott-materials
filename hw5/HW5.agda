{-# OPTIONS --type-in-type --without-K #-}

open import HW5Lemmas

module HW5 where

  prop-level : (A : U) → is-prop A → is-type -1 A
  prop-level A α x y = α x y , prop-is-set A α x y (α x y)

  contr-is-prop : (A : U) → is-contr A → is-prop A
  contr-is-prop A (a , α) x y = α x ⁻¹ ∙ α y

  raise-level : (A : U) (n : tlevel) → is-type n A → is-type (suc n) A
  raise-level A -2 = prop-level A ∘ contr-is-prop A
  raise-level A (suc n) = λ α x y → raise-level (x == y) n (α x y)

  prop-has-level-suc : (A : U) → (n : tlevel) → is-prop A → is-type (suc n) A
  prop-has-level-suc A -2 = prop-level A
  prop-has-level-suc A (suc n) = λ α → raise-level A (suc n) (prop-has-level-suc A n α)

  contr-equiv : (A B : U) → is-contr A → is-contr B → A ≃ B
  contr-equiv _ _ (a , α) (b , β) = (λ _ → b) , ((λ _ → a) , β) , ((λ _ → a) , α)

  equiv-is-contr : (A B : U) → is-contr A → is-contr B → is-contr (A ≃ B)
  equiv-is-contr A B α β = contr-equiv A B α β
                         , λ γ → subtype-path is-equiv-is-prop
                                    (contr-equiv A B α β) γ
                                    (funext λ a → snd β (fst γ a))

  subtype-level : (A : U) (B : A → U) (n : tlevel)
    → is-type (suc n) A → ((x : A) → is-prop (B x))
    → is-type (suc n) (Σ A B)
  subtype-level A B n α β = sigma-level α (λ x → prop-has-level-suc (B x) n (β x))

  bonus : Σ U λ A → Σ (A → U) λ B → is-contr A × ¬ is-contr (Σ A B)
  bonus = ⊤ , (λ _ → ⊥) , (✭ , λ _ → refl) , snd ∘ fst

  equiv-level : (A B : U) (n : tlevel) → is-type n A → is-type n B
    → is-type n (A ≃ B)
  equiv-level A B -2 = equiv-is-contr A B
  equiv-level A B (suc n) = λ _ β → subtype-level (A → B) is-equiv n (product-level (λ _ → β)) is-equiv-is-prop

  equiv-preserves-level : (A B : U) (n : tlevel) → A ≃ B → is-type n A → is-type n B
  equiv-preserves-level A B n e α = tr (is-type n) (ua e) α

  ntype : tlevel → U
  ntype n = Σ U (is-type n)

  ntype-path-equiv : (n : tlevel) → (A B : ntype n) → (fst A == fst B) ≃ (A == B)
  ntype-path-equiv n = subtype-path-equiv (is-type-is-prop n)

  ntype-level : (n : tlevel) → is-type (suc n) (ntype n)
  ntype-level n (A , α) (B , β) = equiv-preserves-level (A ≃ B) ((A , α) == (B , β)) n
    (ntype-path-equiv n (A , α) (B , β) ∘≃ ua-equiv)
    (equiv-level A B n α β)
