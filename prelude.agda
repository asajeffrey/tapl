data FALSE : Set where

CONTRADICTION : ∀ {A : Set} → FALSE → A
CONTRADICTION ()

record TRUE : Set where
{-# BUILTIN UNIT TRUE #-}

data Bool : Set where
  false true : Bool
{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

data Nat : Set where
  zero : Nat
  suc : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

_+_ : Nat → Nat → Nat
zero  + m = m
suc n + m = suc (n + m)
{-# BUILTIN NATPLUS _+_ #-}

_-_ : Nat → Nat → Nat
n     - zero  = n
zero  - suc m = zero
suc n - suc m = n - m
{-# BUILTIN NATMINUS _-_ #-}

_*_ : Nat → Nat → Nat
zero  * m = zero
suc n * m = (n * m) + m
{-# BUILTIN NATTIMES _*_ #-}

_==_ : Nat → Nat → Bool
zero  == zero  = true
suc n == suc m = n == m
_     == _     = false
{-# BUILTIN NATEQUALS _==_ #-}

_<_ : Nat → Nat → Bool
_     < zero  = false
zero  < suc _ = true
suc n < suc m = n < m
{-# BUILTIN NATLESS _<_ #-}

postulate String : Set
{-# BUILTIN STRING String #-}

primitive
  primStringAppend   : String → String → String
  primStringEquality : String → String → Bool

_+++_ = primStringAppend
_===_ = primStringEquality

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x
{-# BUILTIN EQUALITY _≡_  #-}

_≢_ :  ∀ {a} {A : Set a} → A → A → Set a
(x ≢ y) = (x ≡ y) → FALSE

data Dec(A : Set) : Set where
  yes : A → Dec(A)
  no : (A → FALSE) → Dec(A)

primitive
  primEraseEquality : ∀ {a} {A : Set a} {x y : A} → x ≡ y → x ≡ y

primTrustMe : ∀ {a} {A : Set a} {x y : A} → x ≡ y
primTrustMe {x = x} {y} = primEraseEquality unsafePrimTrustMe where
   postulate unsafePrimTrustMe : x ≡ y

_≟_ : (s t : String) → Dec(s ≡ t)
(s ≟ t) with primStringEquality s t
(s ≟ t) | true = yes primTrustMe
(s ≟ t) | false = no unsafeNo where
  postulate unsafeNo : s ≢ t
