
// Example 6.3 in the paper "Computing Selmer groups associated to mod p Galois representations"
// Note: exact choices of matrix will vary, depending on which basis Magma happens to decide on

AttachSpec("ModPGalRep/spec");
AttachSpec("ModPSelmer/spec");
import "ModPSelmer/SelmerUtility.m" : AllLineCombinations;

SetClassGroupBounds("GRH");

_<x> := PolynomialRing(Rationals());

K := QNF();
ZK := MaximalOrder(K);
f := PolynomialRing(K)![ 349029, 1330128, 1980000, 1452888, 468096, -91452, -131078, -25832, 8835, 1508, -1258, -60, 110, -16, -6, 4, 1 ];

q := 3;
n := 2;

L := ext<K|f>;
a := L.1;
ZL := MaximalOrder(L);

rho := ModPGaloisRepresentation(L,q,n);

E := EllipticCurve([0,1,0,-9,55]);
traces := [<p,TraceOfFrobenius(E,p) mod 3> : p in PrimesUpTo(50) | not p in [2,3,7]];

for i in [1..#rho`possible_irreds] do 
	tt := [<Norm(v), Trace(rho`possible_irreds[i](rho`frobenius_elements[v]))> : v in PrimesUpTo(50,K) | GCD(v,Discriminant(ZL)) eq 1*ZK];
	if tt eq traces then 
		ChangeRepresentation(rho,i);
	end if;
end for;


_ := IsNearlyOrdinary(rho);

GalLK := [g : g in rho`domain];
SD16 := Group< a, b | a^2, b^8, a^-1*b*a*b^-3>;
SD16_perm, m1 := PermutationGroup(SD16);

_, m2:=IsIsomorphic(SD16_perm,rho`domain);


a := m2(m1(SD16.1));
b := m2(m1(SD16.2));

fac := Factorization(3*ZL);
P := fac[1,1];

D := DecompositionGroup(P);

sel := SelmerData(rho);

ll := AllLineCombinations(rho);






