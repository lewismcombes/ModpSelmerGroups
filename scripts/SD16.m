
AttachSpec("../ModPGalRep/spec");
AttachSpec("../ModPSelmer/spec");

SetClassGroupBounds("GRH");

import "../ModPSelmer/SelmerUtility.m" : AllLineCombinations;

_<x> := PolynomialRing(Rationals());


K := QNF();
ZK := MaximalOrder(K);

_<x> := PolynomialRing(K);

f:=x^16 + 4*x^15 - 6*x^14 - 16*x^13 + 110*x^12 - 60*x^11 - 1258*x^10 + 1508*x^9 + 
    8835*x^8 - 25832*x^7 - 131078*x^6 - 91452*x^5 + 468096*x^4 + 1452888*x^3 + 
    1980000*x^2 + 1330128*x + 349029;

L := ext<K|f>;
ZL := MaximalOrder(L);


rho := ModPGaloisRepresentation(L,3,2);

ranks := [];

for i in [1..#rho`possible_irreds] do 

    ChangeRepresentation(rho,i);
    sel := SelmerData(rho);
    _ := IsNearlyOrdinary(rho);
    ll := AllLineCombinations(rho);

    RelaxedRank(sel);
    [NearlyOrdinaryRank(sel,u) : u in ll];
    UnramifiedRank(sel);
    IsFaithful(rho);
    IsUnramifiedOnQuotient(rho);
    "";

end for;






