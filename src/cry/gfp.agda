module cry.gfp where

-- open import Agda.Primitive using (lsuc; _⊔_)
open import Level

open import Agda.Builtin.Equality
open import Algebra.FunctionProperties.Core using (Op₁; Op₂)
open import Relation.Nullary
-- open import Relation.Binary.Core using (Rel; Decidable; Substitutive)
-- open import Relation.Binary.PropositionalEquality.Core using (subst)
Rel : ∀ {a} → Set a → (ℓ : Level) → Set (a ⊔ suc ℓ)
Rel A ℓ = A → A → Set ℓ
Decidable : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
Decidable _∼_ = ∀ x y → Dec (x ∼ y)
_Respects_ : ∀ {a ℓ₁ ℓ₂} {A : Set a} → (A → Set ℓ₁) → Rel A ℓ₂ → Set _
P Respects _∼_ = ∀ {x y} → x ∼ y → P x → P y
Substitutive : ∀ {a ℓ₁} {A : Set a} → Rel A ℓ₁ → (ℓ₂ : Level) → Set _
Substitutive {A = A} _∼_ p = (P : A → Set p) → P Respects _∼_

subst : ∀ {a p} {A : Set a} → Substitutive (_≡_ {A = A}) p
subst P refl p = p

record RawField c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  10 _⁻¹
  infix  9 -_
  infixl 8 _²
  infixl 7 _*_
  infixl 6 _+_ _-_
  infix  4 _≈_ _≈?_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _≈?_    : Decidable _≈_
    _+_     : Op₂ Carrier
    _-_     : Op₂ Carrier
    _*_     : Op₂ Carrier
    _²      : Op₁ Carrier
    -_      : Op₁ Carrier
    _⁻¹     : Op₁ Carrier
    0#      : Carrier
    1#      : Carrier

open import Agda.Builtin.Nat as N using () renaming (Nat to ℕ)

_mod_ : (dividend divisor : ℕ) → ℕ
(d mod 0) = 0
(d mod N.suc s) = N.mod-helper 0 s d s

_div_ : (dividend divisor : ℕ) → ℕ
(d div 0) = 0
(d div N.suc s) = N.div-helper 0 s d s

module 𝔽ₚ (p : ℕ) where
    𝔽 : Set
    𝔽 = ℕ

    to𝔽 : ℕ → 𝔽
    to𝔽 i = i mod p

    _==_ : 𝔽 → 𝔽 → Set
    x == y = x ≡ y

    open N using (zero; suc)
    pred : ℕ → ℕ
    pred zero = N.zero
    pred (suc n) = n

    _≟_ : (x y : 𝔽) → Dec (x == y)
    zero  ≟ zero   = yes refl
    suc m ≟ suc n  with m ≟ n
    suc m ≟ suc .m | yes refl = yes refl
    suc m ≟ suc n  | no prf   = no λ x → prf ((λ p → subst (λ x → m ≡ pred x) p refl) x)
    zero  ≟ suc n  = no λ()
    suc m ≟ zero   = no λ()

    infix  10 _⁻¹
    infix  9 -_
    infixl 8 _²
    infixl 7 _*_
    infixl 6 _+_ _-_

    _+_ : 𝔽 → 𝔽 → 𝔽
    n + m = to𝔽 (n N.+ m)

    _*_ : 𝔽 → 𝔽 → 𝔽
    n * m = to𝔽 (n N.* m)

    _² : 𝔽 → 𝔽
    x ² = x * x

    -_ : 𝔽 → 𝔽
    - 0 = 0
    - N.suc n = (p N.- N.suc n)

    _-_ : 𝔽 → 𝔽 → 𝔽
    x - y = x + (- y)

    0# : 𝔽
    0# = 0

    1# : 𝔽
    1# = 1

    {-# TERMINATING #-}
    _^_ : 𝔽 → ℕ → 𝔽
    x ^ 0 = 1#
    x ^ n = f x n where
      f : 𝔽 → ℕ → 𝔽
      -- f u n = uⁿ
      g : 𝔽 → 𝔽 → ℕ → 𝔽
      -- g t u n = uⁿ t
      f u 1 = u
      f u n with n mod 2
      ... | 0 = f (u ²) (n div 2)
      ... | _ = g u (u ²) ((n N.- 1) div 2)
      g t u 1 = t * u
      g t u n with n mod 2
      ... | 0 = g t (u ²) (n div 2)
      ... | _ = g (t * u) (u ²) ((n N.- 1) div 2)

    _⁻¹ : 𝔽 → 𝔽
    x ⁻¹ = x ^ (p N.- 2)

gfp : ℕ → RawField _ _
gfp p = record
  { Carrier = 𝔽
  ; _≈_ = _==_
  ; _≈?_ = _≟_
  ; _+_ = _+_
  ; _-_ = _-_
  ; _*_ = _*_
  ; _² = _²
  ; -_ = -_
  ; _⁻¹ = _⁻¹
  ; 0# = 0#
  ; 1# = 1#
  } where open 𝔽ₚ p
