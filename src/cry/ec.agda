module cry.ec where

import Data.Bool as B
import Data.Nat as N
import Data.Nat.DivMod as N/
import Data.Nat.Divisibility as N∣
-- import Data.Nat.Primality as N′
open import Data.Fin using (Fin; toℕ)
open import Data.Unit using (tt)
import Data.Product as P

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; True; ⌊_⌋)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Function using (case_of_)
open import Algebra
open import Algebra.Structures

open import cry.gfp hiding (test)

-- EC: group of points of elliptic curve (in jacobian coordinates, without conversion to affine)
module _ where
  open P using (Σ; _×_; _,_)

  record EC {P : Prime″} (gfp : GFp P) (a b : GFp.𝔽 gfp) : Set where
    constructor ec

    module F = GFp gfp
    open F renaming (_==_ to _=F_; _≟_ to _≟F_)

    xyz : Set
    xyz = 𝔽 × 𝔽 × 𝔽

    is-point : xyz → Set
    -- (y/z³) ² ≡ (x/z²) ³ + a * (x/z²) + b
    is-point (x , y , z) = y ² ≡ x ³ + a * x * z ⁴ + b * z ⁶

    Point : Set
    Point = Σ xyz is-point

    x_ y_ z_ : Point → 𝔽
    x ((v , _ , _) , _) = v
    y ((_ , v , _) , _) = v
    z ((_ , _ , v) , _) = v

    private
      norm2 : Point → Point → (𝔽 × 𝔽) × (𝔽 × 𝔽)
      norm2 ((x₁ , y₁ , z₁) , _) ((x₂ , y₂ , z₂) , _) = (x₁z₂² , x₂z₁²) , (y₁z₂³ , y₂z₁³) where
        z₂² = z₂ ²
        z₁² = z₁ ²
        x₁z₂² = x₁ * z₂²
        x₂z₁² = x₂ * z₁²
        z₂³ = z₂ * z₂²
        z₁³ = z₁ * z₁²
        y₁z₂³ = y₁ * z₂³
        y₂z₁³ = y₂ * z₁³

    _==_ : Point → Point → Set
    -- p₁ == p₂ with norm2 p₁ p₂
    -- ... | (x₁z₂² , x₂z₁²) , (y₁z₂³ , y₂z₁³)
    ((x₁ , y₁ , z₁) , _) == ((x₂ , y₂ , z₂) , _)
      = x₁z₂² =F x₂z₁² × y₁z₂³ =F y₂z₁³ where
        z₂² = z₂ ²
        z₁² = z₁ ²
        x₁z₂² = x₁ * z₂²
        x₂z₁² = x₂ * z₁²
        z₂³ = z₂ * z₂²
        z₁³ = z₁ * z₁²
        y₁z₂³ = y₁ * z₂³
        y₂z₁³ = y₂ * z₁³
      {-
      x₁/z₁² ≡ x₂/z₂²
      y₁/z₁³ ≡ y₂/z₂³
      -}

    eq : (p₁ p₂ : Point) → B.Bool
    eq ((x₁ , y₁ , z₁) , _) ((x₂ , y₂ , z₂) , _) = {!!} where
        z₂² = z₂ ²
        z₁² = z₁ ²
        x₁z₂² = x₁ * z₂²
        x₂z₁² = x₂ * z₁²
        z₂³ = z₂ * z₂²
        z₁³ = z₁ * z₁²
        y₁z₂³ = y₁ * z₂³
        y₂z₁³ = y₂ * z₁³

    _≟_ : (p₁ p₂ : Point) → Dec (p₁ == p₂)
    _≟_ ((x₁ , y₁ , z₁) , _) ((x₂ , y₂ , z₂) , _) = {!!}
    --   with z₂ ² | z₁ ²
    -- ... | z₂² | z₁² with x₁ * z₂² | x₂ * z₁²
    -- ... | x₁z₂² | x₂z₁² = {!!} where
      where
        z₂² = z₂ ²
        z₁² = z₁ ²
        x₁z₂² = x₁ * z₂²
        x₂z₁² = x₂ * z₁²
        z₂³ = z₂ * z₂²
        z₁³ = z₁ * z₁²
        y₁z₂³ = y₁ * z₂³
        y₂z₁³ = y₂ * z₁³

    -- data 𝕆 : (p : Point) → Set where
    --   ∞ :
    {-
    x₃ = λ² − x₁ − x₂
    y₃ = λ(x₁ − x₃) − y₁
    λ = (y₂ - y₁) / (x₂ - x₁), p₁ ≠ p₂
    λ = (3 x₁ ² + a) / (2 y₁), p₁ = p₂

    (x/z²)₃ = λ² − (x/z²)₁ − (x/z²)₂
    (y/z³)₃ = λ((x/z²)₁ − (x/z²)₃) − (y/z³)₁
    λ = ((y/z³)₂ - (y/z³)₁) / ((x/z²)₂ - (x/z²)₁), p₁ ≠ p₂
    λ = (3 (x/z²)₁ ² + a) / (2 (y/z³)₁), p₁ = p₂

    x₃/z₃² z₁² z₂² = λ² z₁² z₂² − x₁ z₂² − x₂ z₁²
    y₁/z₁³ + y₃/z₃³ = λ(x₁/z₁² − (x₃/z₃²))
    y₂/z₂³ + y₃/z₃³ = λ(x₂/z₂² − (x₃/z₃²))
    λ z₁ z₂ (x₂ z₁² - x₁ z₂²) = (y₂ z₁³ - y₁ z₂³), p₁ ≠ p₂
    λ = (3 (x/z²)₁ ² + a) / (2 (y/z³)₁), p₁ = p₂

    p₁ ≠ p₂:
    z₃ = z₁ z₂ (x₂ z₁² - x₁ z₂²)
    λ z₃ = (y₂ z₁³ - y₁ z₂³)
    x₃ = (y₂ z₁³ - y₁ z₂³)² − (x₁ z₂² + x₂ z₁²) (x₂ z₁² - x₁ z₂²)²
    y₃ z₁³ = (y₂ z₁³ - y₁ z₂³) (z₃² x₁ − x₃ z₁²) z₁ − y₁ z₃³

    (y₁ z₃³ + y₃ z₁³)/(y₂ z₁³ - y₁ z₂³) = (x₁ z₃² − x₃ z₁²) z₁
    (y₂ z₃³ + y₃ z₂³)/(y₂ z₁³ - y₁ z₂³) = (x₂ z₃² − x₃ z₂²) z₂

    x₁ z₃² − x₃ z₁² =
      x₁ (z₁ z₂ (x₂ z₁² - x₁ z₂²))² - 
      (y₂ z₁³ - y₁ z₂³)² z₁² + 
      ((x₂ z₁²)² - (x₁ z₂²)²) (x₂ z₁² - x₁ z₂²) z₁²
    = x₁ z₁² z₂² ((x₂ z₁²)² - 2 x₂ z₁² x₁ z₂² + (x₁ z₂²)²)
      + ((x₂ z₁²)³ - (x₂ z₁²)² x₁ z₂² - (x₁ z₂²)² x₂ z₁² + (x₁ z₂²)³) z₁²
      - (y₂ z₁³ - y₁ z₂³)² z₁²
    = (- (y₂ z₁³ - y₁ z₂³)²
      + 2 x₁³ z₂⁶ + x₂³ z₁⁶ + x₁² x₂ (-3 z₁² z₂⁴)) z₁²

    (y₁ z₃³ + y₃ z₁³) = (y₂ z₁³ - y₁ z₂³) (- (y₂ z₁³ - y₁ z₂³)²
      + 2 x₁³ z₂⁶ + x₂³ z₁⁶ + x₁² x₂ (-3 z₁² z₂⁴)) z₁³
    -}

    dbl : Point → Point
    dbl ((x₁ , y₁ , z₁) , p₁) = ((x₃ , y₃ , z₃) , {!!}) where
      {- p₁ = p₂
      x₃ = λ² − x₁ − x₁
      y₃ = λ(x₁ − x₃) − y₁
      λ = (3 x₁ ² + a) / (2 y₁)

      x₃ = λ² z₃² − 2 x₁/z₁² z₃²
      y₃/z₃³ = λ(x₁/z₁² − x₃/z₃²) − y₁/z₁³
      λ = (3 (x₁/z₁²) ² + a) / (2 y₁/z₁³)

      λ 2 y₁ z₁ = 3 x₁² + a z₁⁴
      z₃ = 2 y₁ z₁
      x₃ = (3 x₁² + a z₁⁴)² − 2 x₁ (2 y₁)²

      y₃ = (3 x₁² + a z₁⁴) (x₁ (2 y₁)² − x₃) − y₁ (2 y₁)³
      -}
      2y₁ = y₁ + y₁
      z₃ = 2y₁ * z₁

      x₁² = x₁ ²
      2x₁² = x₁² + x₁²
      3x₁² = 2x₁² + x₁²
      z₁² = z₁ ²
      z₁⁴ = z₁² ²
      az₁⁴ = a * z₁⁴
      3x₁²+az₁⁴ = 3x₁² + az₁⁴
      [3x₁²+az₁⁴]² = 3x₁²+az₁⁴ ²
      y₁² = y₁ ²
      2y₁² = y₁² + y₁²
      4y₁² = 2y₁² + 2y₁²
      x₁[2y₁]² = x₁ * 4y₁²
      2x₁[2y₁]² = x₁[2y₁]² + x₁[2y₁]²
      x₃ = [3x₁²+az₁⁴]² - 2x₁[2y₁]²

      4y₁⁴ = 2y₁² ²
      8y₁⁴ = 4y₁⁴ + 4y₁⁴
      x₁[2y₁]²-x₃ = x₁[2y₁]² - x₃
      [3x₁²+az₁⁴][x₁[2y₁]²-x₃] = 3x₁²+az₁⁴ * x₁[2y₁]²-x₃
      y₃ = [3x₁²+az₁⁴][x₁[2y₁]²-x₃] - 8y₁⁴

    add : Point → Point → Point
    add ((x₁ , y₁ , z₁) , p₁) ((x₂ , y₂ , z₂) , p₂) = (x₃ , y₃ , z₃) , {!!} where
      {- p₁ ≠ p₂
      x₃ = λ² − x₁ − x₂
      y₃ = λ(x₁ − x₃) − y₁
      λ = (y₂ - y₁) / (x₂ - x₁)

      (x/z²)₃ = λ² − (x/z²)₁ − (x/z²)₂
      (y/z³)₃ = λ((x/z²)₁ − (x/z²)₃) − (y/z³)₁
      λ = ((y/z³)₂ - (y/z³)₁) / ((x/z²)₂ - (x/z²)₁)

      λ z₁ z₂ (x₂ z₁² - x₁ z₂²) = (y₂ z₁³ - y₁ z₂³)
      x₃/z₃² z₁² z₂² + x₁ z₂² + x₂ z₁² = λ² z₁² z₂²
      y₃/z₃³ = λ(x₁/z₁² − x₃/z₃²) − y₁/z₁³

      z₃ = z₁ z₂ (x₂ z₁² - x₁ z₂²)
      x₃ = (y₂ z₁³ - y₁ z₂³)² - (x₁ z₂² + x₂ z₁²) (x₂ z₁² - x₁ z₂²)²
      y₃ = (y₂ z₁³ - y₁ z₂³) (x₁ z₂² (x₂ z₁² - x₁ z₂²)² − x₃) − y₁ z₂³ (x₂ z₁² - x₁ z₂²)³
      y₃ = (y₂ z₁³ - y₁ z₂³) ((x₁ z₂²+x₂ z₁²)/2 (x₂ z₁² - x₁ z₂²)² − x₃)
        − (x₂ z₁² - x₁ z₂²)³ (y₁ z₂³ + y₂ z₁³)/2
      -}

      z₁z₂ = z₁ * z₂
      z₁² = z₁ ²
      z₂² = z₂ ²
      x₁z₂² = x₁ * z₂²
      x₂z₁² = x₂ * z₁²
      z₂³ = z₂ * z₂²
      z₁³ = z₁ * z₁²
      y₁z₂³ = y₁ * z₂³
      y₂z₁³ = y₂ * z₁³
      x₂z₁²+x₁z₂² = x₂z₁² + x₁z₂²
      x₂z₁²-x₁z₂² = x₂z₁² - x₁z₂²
      y₂z₁³-y₁z₂³ = y₂z₁³ - y₁z₂³

      z₃ = z₁z₂ * x₂z₁²-x₁z₂²

      [x₂z₁²-x₁z₂²]² = x₂z₁²-x₁z₂² ²
      [y₂z₁³-y₁z₂³]² = y₂z₁³-y₁z₂³ ²
      [x₂z₁²+x₁z₂²][x₂z₁²-x₁z₂²]² = x₂z₁²+x₁z₂² * [x₂z₁²-x₁z₂²]²
      x₃ = [y₂z₁³-y₁z₂³]² - [x₂z₁²+x₁z₂²][x₂z₁²-x₁z₂²]²

      [x₂z₁²-x₁z₂²]³ = x₂z₁²-x₁z₂² * [x₂z₁²-x₁z₂²]²
      y₁z₂³[x₂z₁²-x₁z₂²]³ = y₁z₂³ * [x₂z₁²-x₁z₂²]³
      x₁z₂²[x₂z₁²-x₁z₂²]² = x₁z₂² * [x₂z₁²-x₁z₂²]²
      x₁z₂²[x₂z₁²-x₁z₂²]²-x₃ = x₁z₂²[x₂z₁²-x₁z₂²]² - x₃
      [y₂z₁³-y₁z₂³][x₁z₂²[x₂z₁²-x₁z₂²]²-x₃] = y₂z₁³-y₁z₂³ * x₁z₂²[x₂z₁²-x₁z₂²]²-x₃
      y₃ = [y₂z₁³-y₁z₂³][x₁z₂²[x₂z₁²-x₁z₂²]²-x₃] - y₁z₂³[x₂z₁²-x₁z₂²]³

test : {!!}
test = {!!} where
  g = cry.gfp.test

  open GFp g
  a b : GFp.𝔽 g
  a = 4 P., (N.s≤s (N.s≤s (N.s≤s (N.s≤s (N.s≤s N.z≤n)))))
  b = 1 P., (N.s≤s (N.s≤s N.z≤n))

  e : EC g a b
  e = ec
  open EC e
  


