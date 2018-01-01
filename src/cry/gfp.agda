module cry.gfp where

import Data.Bool as B
import Data.Nat as N
import Data.Nat.DivMod as N/
import Data.Nat.Divisibility as N∣
-- import Data.Nat.Primality as N′
import Data.Nat.Properties as Np
import Data.Fin as F
import Data.Product as P
import Data.Unit as U

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (False; True; ⌊_⌋)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Function using (case_of_)
open import Algebra
open import Algebra.Structures
open import Algebra.FunctionProperties

-- GF(p): ring of integers modulo prime (without division)
module _ where
  open B using (T)
  open N using (ℕ; zero; suc; _<_)
  open N/ using (_divMod_; result)
  open N∣ using (_∤_)
  open Np using (≤-trans)
  open F using (Fin; toℕ)
  -- open N′ renaming (Prime to is-prime)
  open P using (Σ; _×_; _,_; proj₁; proj₂)
  open U using (tt)

  is-prime″ : ℕ → Set
  is-prime″ p = (∀ n → (n<p : n < p) → (2 N.+ n) ∤ (2 N.+ p))

  Prime″ : Set
  Prime″ = Σ ℕ is-prime″

  f<p : ∀ {p} → (f : Fin p) → toℕ f < p
  f<p {zero} ()
  f<p {suc p} Fin.zero = N.s≤s N.z≤n
  f<p {suc p} (Fin.suc f) = N.s≤s (f<p f)

  toℕ′ : ∀ {p} → Fin p → Σ ℕ (N._< p)
  toℕ′ f = toℕ f , f<p f

  p<1+p : ∀ p → p < suc p
  p<1+p zero = N.s≤s N.z≤n
  p<1+p (suc p) = N.s≤s (p<1+p p)
  p≤1+p : ∀ p → p N.≤ suc p
  p≤1+p zero = N.z≤n
  p≤1+p (suc p) = N.s≤s (p≤1+p p)

  p-sn<p : ∀ {p n} → (n<p : suc n N.< p) → (p N.∸ (suc n) N.< p)
  p-sn<p {zero} {n} ()
  p-sn<p {suc p} {zero} (N.s≤s n<p) = p<1+p p
  p-sn<p {suc p} {suc n} (N.s≤s n<p) = ≤-trans (p-sn<p {p} {n} n<p) (p≤1+p p)

  -- TODO: make Ring
  record GFp (P : Prime″) : Set where
    constructor gfp
    private
      p = 2 N.+ proj₁ P
      p-is-prime = proj₂ P
      -- needed for _divMod_
      p≠0 : False (p N.≟ 0)
      p≠0 = tt

    𝔽 : Set
    𝔽 = Σ ℕ (N._< (2 N.+ proj₁ P)) -- N._< p

    to𝔽 = toℕ′ {p}

{-
    _==_ : 𝔽 → 𝔽 → Set
    _==_ (x , _) (y , _) = T ⌊ x N.≟ y ⌋
    -- _==_ = _≡_
    -- _≡_
    -- HeterogenousEquality

    ==-refl : ∀ x → x == x
    ==-refl (x , x<p) with x N.≟ x
    ==-refl (x , x<p) | yes x≡x = tt
    ==-refl (x , x<p) | no x≢x = x≢x refl

    ==-sym : ∀ x y → x == y → y == x
    ==-sym (x , _) (y , _) x==y with x N.≟ y
    ==-sym (x , _) (y , _) tt | yes x≡y = {!!}
    ==-sym (x , _) (y , _) x==y | no x≢y = {!x==y!}

    _≟_ : (x y : 𝔽) → Dec (x == y)
    (x , _) ≟ (y , _) with x N.≟ y
    (x , _) ≟ (y , _) | yes x≟y = yes tt
    (x , _) ≟ (y , _) | no ¬x≟y = no λ {prf → prf}
    -- (x , _) ≟ (y , _) | yes x≟y rewrite x≟y = yes {!!}
    -- (x , _) ≟ (y , _) | no ¬x≟y = no λ {prf → {!!}}
-}

{-
    _==_ : 𝔽 → 𝔽 → Set
    _==_ = _≡_

    private
      uip : ∀ {z} {t} → (p₁ p₂ : z N.< t) → p₁ ≡ p₂
      uip {zero} (N.s≤s N.z≤n) (N.s≤s N.z≤n) = refl
      uip {suc z} (N.s≤s p₁) (N.s≤s p₂) = cong N.s≤s (uip {z} p₁ p₂)

    _≟_ : (x y : 𝔽) → Dec (x == y)
    (x , px) ≟ (y , py) with x N.≟ y
    ((x , px) ≟ (y , py)) | yes x=y rewrite x=y | uip px py = yes refl
    ((x , px) ≟ (y , py)) | no x≠y = no (λ x=y → x≠y (cong proj₁ x=y))
-}
    _==_ : 𝔽 → 𝔽 → Set
    (x , _) == (y , _) = x ≡ y

    private
      uip : ∀ {z} {t} → (p₁ p₂ : z N.< t) → p₁ ≡ p₂
      uip {zero} (N.s≤s N.z≤n) (N.s≤s N.z≤n) = refl
      uip {suc z} (N.s≤s p₁) (N.s≤s p₂) = cong N.s≤s (uip {z} p₁ p₂)

    _≟_ : (x y : 𝔽) → Dec (x == y)
    (x , px) ≟ (y , py) with x N.≟ y
    ((x , px) ≟ (y , py)) | yes x=y rewrite x=y | uip px py = yes refl
    ((x , px) ≟ (y , py)) | no x≠y = no (λ x=y → x≠y x=y)

    ==-refl : ∀ {x} → x == x
    ==-refl = refl

    ==-sym : ∀ {x y} → x == y → y == x
    ==-sym = sym

    infixl 4 -_
    infixl 5 _+_ _-_
    infixl 6 _*_
    infixl 7 _² _³
    infixl 7 _^_
    infixl 7 _⁻¹

    _+_ : 𝔽 → 𝔽 → 𝔽
    (n , _) + (m , _) with ((n N.+ m) divMod p) {p≠0}
    ... | (result _ r _) = to𝔽 r

    _*_ : 𝔽 → 𝔽 → 𝔽
    (n , _) * (m , _) with ((n N.* m) divMod p) {p≠0}
    ... | (result _ r _) = to𝔽 r

    _² : 𝔽 → 𝔽
    x ² = x * x

    _³ : 𝔽 → 𝔽
    x ³ = x ² * x

    -_ : 𝔽 → 𝔽
    - (zero , prf) = (zero , prf)
    - (suc n , prf) = (p N.∸ (suc n) , p-sn<p prf)

    _-_ : 𝔽 → 𝔽 → 𝔽
    x - y = x + (- y)

    0# : 𝔽
    0# = 0 , N.s≤s N.z≤n

    1# : 𝔽
    1# = 1 , N.s≤s (N.s≤s N.z≤n)

    _^_ : 𝔽 → ℕ → 𝔽
    x ^ zero = 1#
    x ^ suc n = x * (x ^ n)

    _⁴ : 𝔽 → 𝔽
    x ⁴ = x ^ 4
    _⁶ : 𝔽 → 𝔽
    x ⁶ = x ^ 6

    _⁻¹ : 𝔽 → 𝔽
    x ⁻¹ = x ^ (p N.∸ 2)

    rawRing : RawRing _
    rawRing = record
      { Carrier = 𝔽
      ; _+_ = _+_
      ; _*_ = _*_
      ; -_ = -_
      ; 0# = 0#
      ; 1# = 1#
      }

    {-
    +-assoc : Associative _==_ _+_
    +-assoc (x , _) (y , _) (z , _) with ((x N.+ y) divMod p) {p≠0} | ((y N.+ z) divMod p) {p≠0}
    ... | result q₁ r₁ p₁ | result q₂ r₂ p₂ = {!!}
    -- x N.+ y N.+ z ≡ x N.+ toℕ r₂ N.+ q₂ N.* p
    -- x N.+ y N.+ z ≡ toℕ r₁ N.+ z N.+ q₁ N.* p

    *-assoc : Associative _==_ _*_
    *-assoc (x , _) (y , _) (z , _) with ((x N.* y) divMod p) {p≠0} | ((y N.* z) divMod p) {p≠0}
    ... | result q₁ r₁ p₁ | result q₂ r₂ p₂ = {!!}

    0-id : Identity _==_ 0# _+_
    0-id = (λ
      { x → {!!}}) , {!!}

    ring : Ring _ _
    ring = record
      { Carrier = 𝔽
      ; _≈_ = _==_ -- _≡_
      ; _+_ = _+_
      ; _*_ = _*_
      ; -_ = -_
      ; 0# = 0#
      ; 1# = 1#
      ; isRing = record
        { +-isAbelianGroup = record
          { isGroup = record
            { isMonoid = record
              { isSemigroup = record
                { isEquivalence = record
                  { refl = refl
                  ; sym = sym
                  ; trans = trans
                  }
                ; assoc = {!!}
                ; ∙-cong = {!!}
                }
              ; identity = 0-id
              }
            ; inverse = {!!}
            ; ⁻¹-cong = {!!}
            }
          ; comm = {!!}
          }
        ; *-isMonoid = {!!}
        ; distrib = {!!}
        }
      }
    -}

test : _
test = g where
  7-prime : _
  7-prime = λ
    { 0 n<p (N∣.divides 0 ())
    ; 0 _ (N∣.divides 1 ())
    ; 0 _ (N∣.divides 2 ())
    ; 0 _ (N∣.divides 3 ())
    ; 0 _ (N∣.divides (N.suc (N.suc (N.suc (N.suc q)))) ())
    ; 1 _ (N∣.divides 0 ())
    ; 1 _ (N∣.divides 1 ())
    ; 1 _ (N∣.divides 2 ())
    ; 1 _ (N∣.divides (N.suc (N.suc (N.suc q))) ())
    ; 2 _ (N∣.divides 0 ())
    ; 2 _ (N∣.divides 1 ())
    ; 2 _ (N∣.divides (N.suc (N.suc q)) ())
    ; 3 _ (N∣.divides 0 ())
    ; 3 _ (N∣.divides 1 ())
    ; 3 _ (N∣.divides (N.suc (N.suc q)) ())
    ; 4 _ (N∣.divides 0 ())
    ; 4 _ (N∣.divides 1 ())
    ; 4 _ (N∣.divides (N.suc (N.suc q)) ())
    ; (N.suc (N.suc (N.suc (N.suc (N.suc n)))))
      (N.s≤s (N.s≤s (N.s≤s (N.s≤s (N.s≤s ()))))) x
    }
  P : Prime″
  P = 5 P., 7-prime

  g : GFp P
  g = gfp
