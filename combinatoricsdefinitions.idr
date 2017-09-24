nCm : Nat -> Nat -> Nat
nCm n Z = 1
nCm Z (S m) = Z
nCm (S n) (S m) = (nCm n m) + (nCm n (S m))

Sum : Nat -> (Nat -> Nat) -> Nat
Sum Z f = (f Z)
Sum (S n) f = (f (S n)) + (Sum n f)

nDr : Nat -> Nat -> Nat
nDr Z r = S Z
nDr (S n) Z = S Z
nDr (S n) (S Z) = S Z
nDr (S n) (S r) = Sum (S n) f
	where f k = nDr k r

fibonacci : Nat -> Nat
fibonacci Z = 1
fibonacci (S Z) = 1
fibonacci (S (S n)) = (fibonacci n) + (fibonacci (S n))
