--Function that returns the result after one bubble goes up in the bubble sort process
bubble : (List Nat) -> (List Nat, Bool)
bubble Nil = (Nil, False)
bubble (x::Nil) = (x::Nil, False)
bubble (x::y::xs) = if x<=y then (x::(fst (bubble (y::xs))), snd (bubble (y::xs))) else (y::(fst (bubble (x::xs))), True)

--Give the element number i in a list
ith : Nat->(List Nat)->Nat
ith Z Nil = Z
ith Z (x::xs) = x
ith (S i) (x::xs) = ith i xs

--Concatenate two lists
concat : (List Nat) -> (List Nat) -> (List Nat)
concat Nil L = L
concat (x::xs) L = x::(concat xs L)

--Give a subset elements of which are less than or equal to a given number
smaller : Nat -> (List Nat) -> (List Nat)
smaller a Nil = Nil
smaller a (x::xs) = if x<=a then (x::(smaller a xs)) else (smaller a xs)

--Give the subset with elements that are greater than the given number
bigger : Nat -> (List Nat) -> (List Nat)
bigger a Nil = Nil
bigger a (x::xs) = if x>a then (x::(bigger a xs)) else (bigger a xs)

--Quick sort
quick : (List Nat) -> (List Nat)
quick Nil = Nil
quick (x::xs) = concat (quick (smaller x xs)) (concat (x::Nil) (quick (bigger x xs)))

--Tell whether a list is sorted
issorted : (List Nat) -> Bool
issorted Nil = True
issorted (x::Nil) = True
issorted (x::y::Nil) = if x<=y then (issorted (y::Nil)) else False

theorem :(L:(List Nat)) -> (issorted (quick L) = True)

theorem2 : (L:(List Nat))->(p:((snd (bubble(L)))=False))->(issorted(L)=True)