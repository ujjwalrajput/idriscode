data Direction = NE|NW|SE|SW

-- A function that gives new position after moving in the given diagonal direction. If the move is not possible, for example when going south-west from (0,0), then the answer is the original position.
move : (Nat,Nat) -> Direction -> (Nat,Nat)
move (a,b) NE = (S a,S b)
move (Z,b) NW = (Z,b)
move (S a, b) NW = (a,S b)
move (a,Z) SE = (a,Z)
move (a,S b) SE = (S a,b)
move (Z,b) SW = (Z,b)
move (a,Z) SW = (a,Z)
move (S a,S b) SW = (a,b)

-- A function for giving the final position after moving in the given directions, starting from the origin.
path : (List Direction)->(Nat,Nat)
path Nil = (Z,Z)
path (x::xs) = move (path xs) x

-- Some yet-unimplemented useful functions.
fun : (a:Type)->(False=True)->a
fe : (a:Type)->(b:Type)->(f:(a->b))->(x:a)->(y:a)->(x=y)->((f x)=(f y))


-- A function which, given a position, returns a bool indicating whether that position is accesible from origin or not along with, given the bool is True, a path and a proof that the path really leads to the specified position. What further needs to be done is to give proof of inaccesibility whenever the bool is False
accesible : (p:(Nat,Nat)) -> (a:(Bool,List Direction)**(((fst a)=True)->((path (snd a))=p)))
accesible (Z,Z) = ((True,Nil)**f)
	where f p = Refl
accesible (S Z,Z) = ((False,Nil)**(fun ((path Nil) = (S Z,Z))))
accesible (Z,S Z) = ((False,Nil)**(fun ((path Nil) = (Z,S Z))))
accesible (S (S a),b) = ((fst (fst(accesible (a,b))),SE::NE::(snd (fst(accesible (a,b)))))**f1)
	where
		f1 t = fe (Nat,Nat) (Nat,Nat) f (path (snd (fst(accesible (a,b))))) (a,b) ((snd (accesible(a,b))) t)
			where
				f : (Nat,Nat) -> (Nat,Nat)
				f x = move (move x NE) SE
accesible (a,S (S b)) = ((fst (fst(accesible (a,b))),NW::NE::(snd (fst(accesible (a,b)))))**f1)
	where
		f1 t = fe (Nat,Nat) (Nat,Nat) f (path (snd (fst(accesible (a,b))))) (a,b) ((snd (accesible(a,b))) t)
			where
				f : (Nat,Nat) -> (Nat,Nat)
				f x = move (move x NE) NW
