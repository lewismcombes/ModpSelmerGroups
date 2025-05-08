 

AttachSpec("ModPGalRep/spec");



_<x>:=PolynomialRing(Rationals());






K:=NumberField(x^2-x+1);
ZK:=MaximalOrder(K);

f:=PolynomialRing(K)![-6*K.1 - 4, 18, -9, -12, 15, -6, 1];

L:=ext<K|f>;
ZL:=MaximalOrder(L);


rho:=ModPGaloisRepresentation(L,2,2);


P:=Factorization(Discriminant(ZL))[1,1];
PP:=Factorization(Parent(1*ZL)!P)[1,1];

P1:=Factorization(3*ZK)[1,1];


[<Norm(P),Trace(rho`representation(FrobeniusElement(L,P)))> : P in PrimesUpTo(50,K) | not IsRamified(P,ZL)];
