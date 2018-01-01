module test where

open import Data.List using (List; []; _∷_; foldl)
open import Data.Char using (Char; toNat)
open import Data.String using (String; _++_; toList)
open import Data.Unit using (⊤)
open import Data.Nat as N using (ℕ; zero)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Nullary using (yes; no)
open import IO using (IO; run; putStrLn)
open import Coinduction using (♯_)
open import Function using (_∘_; _$_)

open import cry.ec using (module test)
open test

_>>=_ : ∀ {a} {A B : Set a} → IO A → (A → IO B) → IO B
m >>= f = ♯ m IO.>>= λ a → ♯ f a

_>>_ : ∀ {a} {A B : Set a} → IO A → IO B → IO B
m >> n = ♯ m IO.>> ♯ n

showElem : 𝔽 → String
showElem (n , _) = show n

read₁₀ : ℕ → List Char → ℕ × List Char
read₁₀ n [] = n , []
read₁₀ n (c ∷ cs) with toNat '0' N.≤? toNat c
... | no _ = n , cs
... | yes _ with toNat c N.≤? toNat '9'
... | no _ = n , cs
... | yes _ = read₁₀ (10 N.* n N.+ (toNat c N.∸ toNat '0')) cs

readsElem : List Char → 𝔽 × List Char
readsElem cs with read₁₀ 0 cs
... | n , cs′ = (n , prf) , cs′ where
  postulate prf : _

readElem : String → 𝔽
readElem = proj₁ ∘ readsElem ∘ toList

showPoint : Point → String
showPoint ((x , y , z) , _) = showElem x ++ ":" ++ showElem y ++ ":" ++ showElem z

readsPoint : List Char → Point × List Char
readsPoint s with readsElem s
... | x , s′ with readsElem s′
... | y , s″ with readsElem s″
... | z , s‴ = ((x , y , z) , prf) , s‴ where
  postulate prf : _

readPoint : String → Point
readPoint = proj₁ ∘ readsPoint ∘ toList

showPoint′ : Point → String
showPoint′ p = showPoint p ++ " = " ++ showPoint (aff p)

main′ : IO ⊤
main′ = do
  let
    p = readPoint "4,2,1"
    2p = dbl p
    3p = add 2p p
    3p′ = add p 2p
    4p = dbl 2p
    4p′ = add p 3p
    4p″ = add p 3p′
    5p = add 4p p
    5p′ = add 2p 3p
  putStrLn ("p = " ++ showPoint′ p)
  putStrLn ("2p = " ++ showPoint′ 2p)
  putStrLn ("3p = " ++ showPoint′ 3p)
  putStrLn ("3p′ = " ++ showPoint′ 3p′)
  putStrLn ("4p = " ++ showPoint′ 4p)
  putStrLn ("4p′ = " ++ showPoint′ 4p′)
  putStrLn ("4p″ = " ++ showPoint′ 4p″)
  putStrLn ("5p = " ++ showPoint′ 5p)
  putStrLn ("4p′ = " ++ showPoint′ 5p′)

main = run main′
