------------------------------------------------------------------------------
--	CI3661 Laboratorio de Lenguajes de Programación 						--
--	Abril - Julio 2016														--
--	Integrantes: 															--
--	Patricia Valencia 10-10916												--
--	Sahid Reyes 10-10603													--
------------------------------------------------------------------------------

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Term
( module Term
)where

import Control.Monad.Identity

-- Definición Tipos de Datos --

data Term = Var String
		| Or Term Term	
		| Neg Term 
		| And Term Term 
		| Ssi Term Term
		| Impl Term Term 
		| NotSsi Term Term
		| Const String
		deriving Eq

data Equation = Equal Term Term 

type Sust = (Term,Term)

-- Términos Válidos, Variables y Constantes ---

a :: Term
a = Var "a"

b :: Term
b = Var "b"

c :: Term
c = Var "c"

d :: Term
d = Var "d"

e :: Term
e = Var "e"

f :: Term
f = Var "f"

g :: Term
g = Var "g"

h :: Term
h = Var "h"

i :: Term
i = Var "i"

j :: Term
j = Var "j"

k :: Term
k = Var "k"

l :: Term
l = Var "l"

m :: Term
m = Var "m"

n :: Term
n = Var "n"

o :: Term
o = Var "o"

p :: Term
p = Var "p"

q :: Term
q = Var "q"

r :: Term
r = Var "r"

s :: Term
s = Var "s"

t :: Term
t = Var "t"

u :: Term
u = Var "u"

v :: Term
v = Var "v"

w :: Term
w = Var "w"

x :: Term
x = Var "x"

y :: Term
y = Var "y"

z :: Term
z = Var "z"

true :: Term
true = Const "true"

false :: Term
false = Const "false"

-- Operadores --

(\/) :: Term -> Term -> Term
(\/) t1 t2 = Or t1 t2

(/\) :: Term -> Term -> Term
(/\) t1 t2 = And t1 t2

(==>) :: Term -> Term -> Term
(==>) t1 t2 = Impl t1 t2

(<==>) :: Term -> Term -> Term
(<==>) t1 t2 = Ssi t1 t2

(!<==>) :: Term -> Term -> Term
(!<==>) t1 t2 = NotSsi t1 t2

(===) :: Term -> Term -> Equation
(===) t1 t2 = Equal t1 t2

neg :: Term -> Term
neg t1 = Neg t1

-- Precedencia de los Operadores --

infixl 9 `neg`
infixl 8 \/
infixl 8 /\
infixr 7 ==>
infixl 6 <==>
infixl 6 !<==>
infix  5 ===
infix  4 =:

-- Instancias de Show para los Términos --

showTerm :: Term -> String
showTerm (Const i) = i
showTerm (Var i)   = i

showTerm (Neg (Var i)) = "neg " ++ showTerm(Var i)
showTerm (Neg t)       = "neg " ++ "(" ++ showTerm t ++ ")"

showTerm (Or (Const i) (Const j)) = showTerm(Const i) ++ "\\/" ++ showTerm(Const j)
showTerm (Or (Var i) (Var j))     = showTerm(Var i) ++ "\\/" ++ showTerm(Var j)
showTerm (Or (Var i) (Const j))   = showTerm(Var i) ++ "\\/" ++ showTerm(Const j)
showTerm (Or (Const i) (Var j))   = showTerm(Const i) ++ "\\/" ++ showTerm(Var j)
showTerm (Or (Const i) t)         = showTerm(Const i) ++ " \\/ (" ++ showTerm(t) ++ ")"
showTerm (Or t (Const i))         = "(" ++ showTerm(t) ++ ")" ++ " \\/ " ++ showTerm(Const i)
showTerm (Or (Var i) t)           = showTerm(Var i) ++ " \\/ (" ++ showTerm(t) ++ ")"
showTerm (Or t (Var i))           = "(" ++ showTerm(t) ++ ")" ++ " \\/ " ++ showTerm(Var i)
showTerm (Or t1 t2)               = "(" ++ showTerm t1 ++ ") \\/ (" ++ showTerm t2 ++ ")"

showTerm (And (Const i) (Const j)) = showTerm(Const i) ++ "/\\" ++ showTerm(Const j)
showTerm (And (Var i) (Var j))     = showTerm(Var i) ++ "/\\" ++ showTerm(Var j)
showTerm (And (Var i) (Const j))   = showTerm(Var i) ++ "/\\" ++ showTerm(Const j)
showTerm (And (Const i) (Var j))   = showTerm(Const i) ++ "/\\" ++ showTerm(Var j)
showTerm (And (Const i) t)         = showTerm(Const i) ++ " /\\ (" ++ showTerm(t) ++ ")"
showTerm (And t (Const i))         = "(" ++ showTerm(t) ++ ")" ++ " /\\ " ++ showTerm(Const i)
showTerm (And (Var i) t)           = showTerm(Var i) ++ " /\\ (" ++ showTerm(t) ++ ")"
showTerm (And t (Var i))           = "(" ++ showTerm(t) ++ ")" ++ " /\\ " ++ showTerm(Var i)
showTerm (And t1 t2)               = "(" ++ showTerm t1 ++ ") /\\ (" ++ showTerm t2 ++ ")"

showTerm (NotSsi (Const i) (Const j)) = showTerm(Const i) ++ "!<==>" ++ showTerm(Const j)
showTerm (NotSsi (Var i) (Var j))     = showTerm(Var i) ++ "!<==>" ++ showTerm(Var j)
showTerm (NotSsi (Var i) (Const j))   = showTerm(Var i) ++ "!<==>" ++ showTerm(Const j)
showTerm (NotSsi (Const i) (Var j))   = showTerm(Const i) ++ "!<==>" ++ showTerm(Var j)
showTerm (NotSsi (Const i) t)         = showTerm(Const i) ++ " !<==> (" ++ showTerm(t) ++ ")"
showTerm (NotSsi t (Const i))         = "(" ++ showTerm(t) ++ ")" ++ " !<==> " ++ showTerm(Const i)
showTerm (NotSsi (Var i) t)           = showTerm(Var i) ++ " !<==> (" ++ showTerm(t) ++ ")"
showTerm (NotSsi t (Var i))           = "(" ++ showTerm(t) ++ ")" ++ " !<==> " ++ showTerm(Var i)
showTerm (NotSsi t1 t2)               = "(" ++ showTerm t1 ++ ") !<==> (" ++ showTerm t2 ++ ")"

showTerm (Impl (Const i) (Const j)) = showTerm(Const i) ++ "==>" ++ showTerm(Const j)
showTerm (Impl (Var i) (Var j))     = showTerm(Var i) ++ "==>" ++ showTerm(Var j)
showTerm (Impl (Var i) (Const j))   = showTerm(Var i) ++ "==>" ++ showTerm(Const j)
showTerm (Impl (Const i) (Var j))   = showTerm(Const i) ++ "==>" ++ showTerm(Var j)
showTerm (Impl (Const i) t)         = showTerm(Const i) ++ " ==> (" ++ showTerm(t) ++ ")"
showTerm (Impl t (Const i))         = "(" ++ showTerm(t) ++ ")" ++ " ==> " ++ showTerm(Const i)
showTerm (Impl (Var i) t)           = showTerm(Var i) ++ " ==> (" ++ showTerm(t) ++ ")"
showTerm (Impl t (Var i))           = "(" ++ showTerm(t) ++ ")" ++ " ==> " ++ showTerm(Var i)
showTerm (Impl t1 t2)               = "(" ++ (showTerm (t1)) ++ ") ==> (" ++ (showTerm (t2)) ++ ")"

showTerm (Ssi (Const i) (Const j)) = showTerm(Const i) ++ "<==>" ++ showTerm(Const j)
showTerm (Ssi (Var i) (Var j))     = showTerm(Var i) ++ "<==>" ++ showTerm(Var j)
showTerm (Ssi (Var i) (Const j))   = showTerm(Var i) ++ "<==>" ++ showTerm(Const j)
showTerm (Ssi (Const i) (Var j))   = showTerm(Const i) ++ "<==>" ++ showTerm(Var j)
showTerm (Ssi (Const i) t)         = showTerm(Const i) ++ " <==> (" ++ showTerm(t) ++ ")"
showTerm (Ssi t (Const i))         = "(" ++ showTerm(t) ++ ")" ++ " <==> " ++ showTerm(Const i)
showTerm (Ssi (Var i) t)           = showTerm(Var i) ++ " <==> (" ++ showTerm(t) ++ ")"
showTerm (Ssi t (Var i))           = "(" ++ showTerm(t) ++ ")" ++ " <==> " ++ showTerm(Var i)
showTerm (Ssi t1 t2)               = "(" ++ showTerm t1 ++ ") <==> (" ++ showTerm t2 ++ ")"

instance Show Term where show = showTerm

showEquation :: Equation -> String

showEquation (Equal (Const i) (Const j)) = showTerm(Const i) ++ "===" ++ showTerm(Const j)
showEquation (Equal (Var i) (Var j))     = showTerm(Var i)   ++ "===" ++ showTerm(Var j)
showEquation (Equal (Var i) (Const j))   = showTerm(Var i)   ++ "===" ++ showTerm(Const j)
showEquation (Equal (Const i) (Var j))   = showTerm(Const i) ++ " === " ++ showTerm(Var j)
showEquation (Equal (Const i) t)         = showTerm(Const i) ++ " === (" ++ showTerm(t) ++ ")"
showEquation (Equal t (Const i))         = "(" ++ showTerm(t) ++ ")" ++ " === " ++ showTerm(Const i)
showEquation (Equal (Var i) t)           = showTerm(Var i) ++ " === (" ++ showTerm(t) ++ ")"
showEquation (Equal t (Var i))           = "(" ++ showTerm(t) ++ ")" ++ " === " ++ showTerm(Var i)
showEquation (Equal t1 t2)               = "(" ++ showTerm t1 ++ ") === (" ++ showTerm t2 ++ ")"

instance Show Equation where show = showEquation
 
showSust :: Sust -> String
showSust (t,(Var i))          =  "(" ++ showTerm(t) ++ "=:" ++ showTerm(Var i) ++ ")"
instance Show Sust where show = showSust

showSust' :: (Term,Sust,Term) -> String
showSust' (t1,(t2,(Var i)),(Var j))       = "("++showTerm(t1)++","++showTerm(t2)++ "=:" ++showTerm(Var i)++","++showTerm(Var j)++")"
instance Show (Term,Sust,Term) where show = showSust'

showSust'' :: (Term,Term,Sust,Term,Term) -> String
showSust'' (t1,t2,(t3,(Var i)),(Var j),(Var k))     = "("++showTerm(t1)++","++showTerm(t2)++","++showTerm(t3)++"=:"++showTerm(Var i)++","++showTerm(Var j)++","++showTerm(Var k)++")"
instance Show (Term,Term,Sust,Term,Term) where show = showSust''


class Asign t p where
	(=:) :: t -> p -> Sust

instance Asign Term Term where
	(=:) t p = (t,p)

