module Int2 where

-- import `plus` & `times` on Nats;
-- use these functions where appropriate below.
open import Nat

data Int : Set where
  -- (+ n) represents positive n.
  + : Nat → Int
  -- (- n) represents negative n.
  - : Nat → Int
  -- 0 can be represented as (+ zero) or (- zero).

-- given i, return i + 1.
isuc : Int → Int
isuc (+ n) = + (suc n)
isuc (- zero) = + (suc zero)
isuc (- (suc n)) = - n

-- given i, return i - 1.
ipred : Int → Int
ipred (- n) = - (suc n)
ipred (+ zero) = - (suc zero)
ipred (+ (suc n)) = + n

-- given i, return -i.
ineg : Int → Int
ineg (+ n)= - n
ineg (- zero) = + zero
ineg (- (suc n)) = + (suc n)

-- given i & j, return i + j.
iplus : Int → Int → Int
iplus (+ n) (+ m) = + (plus m n)
iplus (- n) (- m) = - (plus m n)
iplus (- zero) (+ m) = + m
iplus (- (suc n)) (+ m) = ipred (iplus (- n) (+ m))
iplus (+ zero) (- m) = - m
iplus (+ (suc n)) (- m) = isuc (iplus (+ n) (- m))


-- given i & j, return i - j.
iminus : Int → Int → Int

iminus (+ zero) (+ m) = - m 
iminus (+ (suc n)) (+ m) = isuc (iminus (+ n) (- m))
iminus (- zero) (- m) = + m
iminus (- (suc n)) (- m) = isuc (iminus (- n) (+ m))
iminus (- n) (+ m) = - (plus m n)
iminus (+ n) (- m) = + (plus m n)

-- given i & j, return i * j.
itimes : Int → Int → Int
itimes (+ n) (+ m) = + (times n m)
itimes (- n) (- m) = - (times n m)
itimes (- n) (+ m) = - (times n m)
itimes (+ n) (- m) = - (times n m)

