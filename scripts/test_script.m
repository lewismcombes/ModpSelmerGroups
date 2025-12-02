

AttachSpec("../ModPGalRep/spec");
AttachSpec("../ModPSelmer/spec");
import "../ModPSelmer/SelmerUtility.m" : AllLineCombinations;

SetClassGroupBounds("GRH");


_<x> := PolynomialRing(Rationals());

//K := NumberField(x^2-x+2);
K := QNF();
ZK := MaximalOrder(K);
//f:=PolynomialRing(K)![ [ 32, -48 ], [ -48, 24 ], [ -54, 40 ], [ -10, -4 ], [ -1, 0 ], [ 2, -4 ], [ 1, 0 ] ];
//f := PolynomialRing(K)! [ [ 23, -1 ], [ 0, 0 ], [ 35, 2 ], [ 0, 0 ], [ 5, -1 ], [ 0, 0 ], [ 1, 0 ] ];

f := PolynomialRing(K)![ 41643837, 117933768, 169385310, 168420924, 116575978, 
        48162244, 7064422, -2597052, -1305921, -180364, 2550, 4060, 948, 96, 16,
        8, 1 ];

L := ext<K|f>;
ZL := MaximalOrder(L);


rho := ModPGaloisRepresentation(L,3,2);
ChangeRepresentation(rho,2);

sel := SelmerData(rho);
_ := IsNearlyOrdinary(rho);
ll := AllLineCombinations(rho);
no_ranks := [ NearlyOrdinaryRank(sel,l) : l in ll ];

printf "Relaxed rank is %o", RelaxedRank(sel);
printf "Nearly orindary ranks are %o" [ NearlyOrdinaryRank(sel,l) : l in ll ];
printf "Unramified rank is %o" UnramifiedRank(sel);

