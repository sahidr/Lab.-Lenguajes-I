------------------------------------------------------------------------------
--	CI3661 Laboratorio de Lenguajes de Programación 						--
--	Abril - Julio 2016														--
--	Integrantes: 															--
--	Patricia Valencia 10-10916												--
--	Sahid Reyes 10-10603													--
------------------------------------------------------------------------------

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Propositions(
	module Propositions
,	module Theorems
)where

import Theorems

class Sustitution t where
	sust :: Term -> t -> Term

instance Sustitution Sust where
	sust (Var i) (t,p)        =  if ((Var i) == p) then t else (Var i)
	sust (Const i) (t,p)      = Const i
	sust (Neg t1) (t,p)       = Neg (sust t1 (t,p))
	sust (Or t1 t2) (t,p)     = (Or (sust t1 (t,p)) (sust t2 (t,p)))
	sust (And t1 t2) (t,p)    = (And (sust t1 (t,p)) (sust t2 (t,p)))
	sust (Impl t1 t2) (t,p)   = (Impl (sust t1 (t,p)) (sust t2 (t,p)))
	sust (Ssi t1 t2) (t,p)    = (Ssi (sust t1 (t,p)) (sust t2 (t,p)))
	sust (NotSsi t1 t2) (t,p) = (NotSsi (sust t1 (t,p)) (sust t2 (t,p)))

instance Sustitution (Term,Sust,Term) where
	sust (Var i) (t1,(t2,p),q)        = if ((Var i) == p) then t1 else if ((Var i) == q) then t2 else (Var i)
	sust (Const i) (t2,(t3,p),q)      = Const i
	sust (Neg t0) (t2,(t3,p),q)       = Neg (sust t0 (t2,(t3,p),q))
	sust (Or t0 t1) (t2,(t3,p),q)     = (Or (sust t0 (t2,(t3,p),q)) (sust t1 (t2,(t3,p),q)))
	sust (And t0 t1) (t2,(t3,p),q)    = (And (sust t0 (t2,(t3,p),q)) (sust t1 (t2,(t3,p),q)))
	sust (Impl t0 t1) (t2,(t3,p),q)   = (Impl (sust t0 (t2,(t3,p),q)) (sust t1 (t2,(t3,p),q)))
	sust (Ssi t0 t1) (t2,(t3,p),q)    = (Ssi (sust t0 (t2,(t3,p),q)) (sust t1 (t2,(t3,p),q)))
	sust (NotSsi t0 t1) (t2,(t3,p),q) = (NotSsi (sust t0 (t2,(t3,p),q)) (sust t1 (t2,(t3,p),q)))

instance Sustitution (Term,Term,Sust,Term,Term) where
	sust (Var i) (t1,t2,(t3,p),q,r)        =  if ((Var i) == p) then t1 else if ((Var i) == q) then t2 else if ((Var i) == r) then t3 else (Var i)
	sust (Const i) (t2,t3,(t4,p),q,r)      = Const i
	sust (Neg t0) (t2,t3,(t4,p),q,r)       = Neg (sust t0 (t2,t3,(t4,p),q,r))
	sust (Or t0 t1) (t2,t3,(t4,p),q,r)     = (Or (sust t0 (t2,t3,(t4,p),q,r)) (sust t1 (t2,t3,(t4,p),q,r)))
 	sust (And t0 t1) (t2,t3,(t4,p),q,r)    = (And (sust t0 (t2,t3,(t4,p),q,r)) (sust t1 (t2,t3,(t4,p),q,r)))
	sust (Impl t0 t1) (t2,t3,(t4,p),q,r)   = (Impl (sust t0 (t2,t3,(t4,p),q,r)) (sust t1 (t2,t3,(t4,p),q,r)))
	sust (Ssi t0 t1) (t2,t3,(t4,p),q,r)    = (Ssi (sust t0 (t2,t3,(t4,p),q,r)) (sust t1 (t2,t3,(t4,p),q,r)))
	sust (NotSsi t0 t1) (t2,t3,(t4,p),q,r) = (NotSsi (sust t0 (t2,t3,(t4,p),q,r)) (sust t1 (t2,t3,(t4,p),q,r)))

--Instanciacion --

class Instantiation i where
	instantiate :: Equation -> i -> Equation

instance Instantiation Sust where
	instantiate (Equal t1 t2) (t,p) = Equal (sust t1 (t,p)) (sust t2 (t,p))

instance Instantiation (Term,Sust,Term) where
	instantiate (Equal t1 t2) (t3,(t4,p),q) = Equal (sust t1 (t3,(t4,p),q)) (sust t2 (t3,(t4,p),q))

instance Instantiation (Term,Term,Sust,Term,Term) where
	instantiate (Equal t1 t2) (t3,t4,(t5,p),q,r) = Equal (sust t1 (t3,t4,(t5,p),q,r)) (sust t2 (t3,t4,(t5,p),q,r))

-- Leibniz --

leibniz :: Equation -> Term -> Term -> Equation
leibniz (Equal t1 t2) e (Var k) = (Equal (sust e (t1,(Var k))) (sust e (t2,(Var k))))

-- Inferencia --

class Inference s where
	infer :: Float -> s -> Term -> Term -> Equation

instance Inference Sust where
	infer n s e (Var i) = leibniz (instantiate (prop n) s) e (Var i)

instance Inference (Term,Sust,Term) where
	infer n s e (Var i) = leibniz (instantiate (prop n) s) e (Var i)

instance Inference (Term,Term,Sust,Term,Term) where
	infer n s e (Var i) = leibniz (instantiate (prop n) s) e (Var i)

-- Deducción de un Paso --

extraer :: Equation -> Term-> Term 
extraer (Equal a b) t = if (a == t) then b else if (b == t) then a else error "invalid inference rule\n"


class OneStep s where
	step :: Term -> Float -> s -> Term -> Term -> Term

instance OneStep Sust where
	step termino1 n s e (Var j) =  extraer (infer n s e (Var j)) termino1

instance OneStep (Term,Sust,Term) where
	step termino1 n s e (Var j) =  extraer (infer n s e (Var j)) termino1

instance OneStep (Term,Term,Sust,Term,Term) where
	step termino1 n s e (Var j) =  extraer (infer n s e (Var j)) termino1

with::()
with = ()

using :: ()
using = ()

lambda :: ()
lambda = ()


class Statement s where
	statement :: Float -> () -> s -> () -> () -> Term -> Term -> Term -> IO Term

instance Statement Sust where
	statement n _ s _ _ v e termino1 = do
								let term = (step termino1 n s e v)
								putStrLn("===<statement "++show n++ " with " 
									++ showSust s ++ " using lambda " 
									++ showTerm(v) ++" ("++showTerm(e)++")"
									++">\n"++showTerm(term))
								return(term)

instance Statement (Term,Sust,Term) where
	statement n _ s _ _ v e termino1 = do
								let term = (step termino1 n s e v)
								putStrLn("===<statement "++show n++ " with " 
									++ showSust' s ++ " using lambda " 
									++ showTerm(v) ++" ("++showTerm(e)++")"
									++">\n"++showTerm(term))
								return(term)

instance Statement (Term,Term,Sust,Term,Term) where
	statement n _ s _ _ v e termino1 = do
								let term = (step termino1 n s e v)
								putStrLn("===<statement "++ show n++ " with " 
									++ showSust'' s ++ " using lambda " 
									++ showTerm(v) ++" ("++showTerm(e)++")"
									++">\n"++showTerm(term))
								return(term)

proof :: Equation -> IO Term
proof (Equal t1 t2) = do 
					putStrLn("\nprooving "++showEquation(Equal t1 t2)++"\n\n"
						++showTerm(t1))
					return (t1)
					
done :: Equation -> Term -> IO ()
done (Equal t1 t2) t3 = do
						if (t3 == t2) then putStrLn "\nproof successful\n" 
						else putStrLn "\nproof unsuccessful\n"