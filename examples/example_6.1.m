
// Example 6.1 in the paper "Computing Selmer groups associated to mod p Galois representations"
// Note: exact choices of matrix will vary, depending on which basis Magma happens to decide on

AttachSpec("ModPGalRep/spec");
AttachSpec("ModPSelmer/spec");
import "ModPSelmer/SelmerUtility.m" : AllLineCombinations;

SetClassGroupBounds("GRH");

_<x> := PolynomialRing(Rationals());

K := QNF();
ZK:=MaximalOrder(K);
f := PolynomialRing(K)! [4, -14, 21, -15, 10, -3, 1];

q := 2;
n := 2;

L := ext<K|f>;
a := L.1;
ZL := MaximalOrder(L);

rho := ModPGaloisRepresentation(L,q,n);
_ := IsNearlyOrdinary(rho);

GalLK := [g : g in rho`domain];


sigma_a := L![-6, 19, -13, 10, -3, 1]/2;
tau_a := L![8, -19, 13, -10, 3, -1]/2;

sigma := GalLK[Index([rho`field_autom_rep(g)(a) : g in GalLK],sigma_a)];
tau := GalLK[Index([rho`field_autom_rep(g)(a) : g in GalLK],tau_a)];

P1 := ideal< ZL | 2, 2 + a^3>;
P2 := ideal< ZL | 2, 1 + a + a^2>;
P3 := ideal< ZL | 2, 3 + a + a^2 + a^3 >;

sel := SelmerData(rho);

// these are the actions of sigma and tau
print "The action of sigma on Gal(A/L) is via \n" cat Sprint(sel`action_on_maximal_extension[Index(GalLK,sigma)]);
print "";
print "The action of tau on Gal(A/L) is via \n" cat Sprint(sel`action_on_maximal_extension[Index(GalLK,tau)]);
print "";


beta1 := L![0, -3, 1, -1, 0, 0];
beta2 := L![2, -1, 1, 0, 0, 0];
beta3 := L![0, 1, -4, 2, -1, 0]/2;
beta4 := L![0, 3, -4, 2, -1, 0]/2;

_<y>:=PolynomialRing(L);

M1 := RelativeField(L, ext< L | [y^2 - beta1, y^2 - beta2] >);
M2 := RelativeField(L, ext< L | [y^2 - beta3, y^2 - beta4] >);
M3 := RelativeField(L, ext< L | [y^2 - beta1*beta3, y^2 - beta2*beta4] >);
M4 := RelativeField(L, ext< L | [y^2 - 2, y^2 + 1] >);


D := DecompositionGroup(P1);

ZM1 := MaximalOrder(M1);

PP1 := ideal<ZM1|[ZM1!u : u in Generators(P1)]>;
fac := Factorization(PP1);




