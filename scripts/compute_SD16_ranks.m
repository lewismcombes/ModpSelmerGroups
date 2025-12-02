

SD16s := recformat< polynomial, traces, LMFDBLabels, EC_ranks, relaxed_rank, nearly_ordinary_ranks, nearly_ordinary_ramifications, unramified_rank >;

load "SD16NO";


AttachSpec("ModPGalRep/spec");
AttachSpec("ModPSelmer/spec");

import "ModPGalRep/invariants.m": TracesAreEqual;
import "ModPSelmer/SelmerUtility.m" : AllLineCombinations;

SetClassGroupBounds("GRH");

K := QNF();
ZK := MaximalOrder(K);

time for i in [1..#nearly_ordinary] do

	u:=nearly_ordinary[i]; 

	L := ext<K | PolynomialRing(K)!u`polynomial>;
	rho := ModPGaloisRepresentation(L,3,2);

	// we pick out the representation matching our frobenius traces 
	for i in [1..#rho`possible_irreds] do 
		ChangeRepresentation(rho,i);
		traces := [<Norm(p),Trace(rho(rho`frobenius_elements[p]))> : p in PrimesUpTo(100,K) | GCD(p,rho`discriminant) eq 1*ZK];
		if TracesAreEqual(traces,u`traces) then 
			break i;
		end if;
	end for;

    sel:=SelmerData(rho);
    _:=IsNearlyOrdinary(rho);
    ll := AllLineCombinations(rho);

    u`nearly_ordinary_ramifications := IsUnramifiedOnQuotient(rho);
    u`relaxed_rank := RelaxedRank(sel);
    u`nearly_ordinary_ranks := [ NearlyOrdinaryRank(sel,l) : l in ll ];
    u`unramified_rank := UnramifiedRank(sel);
    nearly_ordinary[i] := u;

    print nearly_ordinary[i];
end for;


Write("SD16_done",nearly_ordinary,"Magma");


