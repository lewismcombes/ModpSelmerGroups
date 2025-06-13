

AttachSpec("ModPGalRep/spec");
AttachSpec("ModPSelmer/spec");

import "ModPSelmer/SelmerUtility.m": SelmerModulus;
SetClassGroupBounds("GRH");


_<x>:=PolynomialRing(Rationals());

/*
K:=NumberField(x^2-x+1);
ZK:=MaximalOrder(K);
f:=PolynomialRing(K)![ [ 8, 0 ], [ -8, -8 ], [ 12, 18 ], [ -12, -18 ], [ 6, 9 ], [ -2, -2 ], [ 1, 0 ]];
*/

K := NumberField(x^2-x+2);
ZK:=MaximalOrder(K);
f:=PolynomialRing(K)![ [ 32, -48 ], [ -48, 24 ], [ -54, 40 ], [ -10, -4 ], [ -1, 0 ], [ 2, -4 ], [ 1, 0 ] ];



L:=ext<K|f>;
ZL:=MaximalOrder(L);


rho:=ModPGaloisRepresentation(L,2,2);




time sel:=SelmerData(rho);



IsNearlyOrdinary(rho);
lines:=[u[1].1 : u in rho`fixed_by_decomp];
time NearlyOrdinaryRank(sel,lines);









//




// testing multiple representations from the same field 

AttachSpec("ModPGalRep/spec");
AttachSpec("ModPSelmer/spec");

_<x>:=PolynomialRing(Rationals());


K:=QNF();
ZK:=MaximalOrder(K);

_<x>:=PolynomialRing(K);

f:=x^16 + 4*x^15 - 6*x^14 - 16*x^13 + 110*x^12 - 60*x^11 - 1258*x^10 
    + 1508*x^9 + 8835*x^8 - 25832*x^7 - 131078*x^6 - 91452*x^5 + 
    468096*x^4 + 1452888*x^3 + 1980000*x^2 + 1330128*x + 349029;

L:=ext<K|f>;
ZL:=MaximalOrder(L);


rho:=ModPGaloisRepresentation(L,3,2);


I:=RamificationGroup(rho`primes_over_char_image[1][1],0);

for u in rho`possible_irreds do 
	rho`representation := Representation(u);
	if true then 
		IsNearlyOrdinary(rho);
		rho`fixed_by_decomp[1];
		QQ,down:=quo<RSpace(GF(3),2) | rho`fixed_by_decomp[1][2]>;
		[down(Inverse(down)(QQ.1) * rho(g)) : g in I]; 
	end if;
end for;            




SetClassGroupBounds("GRH");
for u in rho`possible_irreds do 
	rho`representation := Representation(u);
	sel:=SelmerData(rho);
	_:=IsNearlyOrdinary(rho);
	RelaxedRank(sel), NearlyOrdinaryRank(sel,[rho`fixed_by_decomp[1].1]), UnramifiedRank(sel);
end for;            






IsNearlyOrdinary(rho);
rho`fixed_by_decomp[1];
QQ,down:=quo<RSpace(GF(3),2) | s>;
[down(Inverse(down)(QQ.1) * rho(g)) : g in I];   
[rho(g) : g in I];   










// 




AttachSpec("ModPGalRep/spec");
AttachSpec("ModPSelmer/spec");

import "ModPSelmer/SelmerUtility.m": OneDimensionalSubspaces;

rel:=[];
no:=[];
unr:=[];


SetClassGroupBounds("GRH");


_<x>:=PolynomialRing(Rationals());


//K:=NumberField(x^2-x+1);
//K:=NumberField(x^2+1);
K:=NumberField(x^2-x+2);
//K:=NumberField(x^2+2);
//K:=NumberField(x^2-x+3);
ZK:=MaximalOrder(K);


time for f in pols do 
	LL:=NumberField(f);
	_ := IsSubfield(K,LL);
	L:=RelativeField(K,LL);
	ZL:=MaximalOrder(L);

	rho:=ModPGaloisRepresentation(L,2,2);
	sel:=SelmerData(rho);

	_:=IsNearlyOrdinary(rho);

	all_line_combos:=AllLineCombinations(rho`fixed_by_decomp);

	Append(~rel,RelaxedRank(sel));
	Append(~no,[NearlyOrdinaryRank(sel,[v.1 : v in u]) : u in all_line_combos]);
	Append(~unr,UnramifiedRank(sel));
	print no[#no];

end for;





for i in [1..#pols] do
	Write("rel",rel[i]);
	Write("no",no[i]);
	Write("unr",unr[i]);
end for;
	






///




















//

// let's do some interesting examples, eh? 

AttachSpec("ModPGalRep/spec");
AttachSpec("ModPSelmer/spec");

// this number field is the 2-torsion field of an elliptic curve with fairly big rank. but I can't remember which 
// it seems that the class field computation really chugs, though :( 
// it does finish! but then Magma won't let me compute with the ray class group 
K:=QNF();
f:=PolynomialRing(K)![ -4298722717504, 0, 1516089969, 0, -77874, 0, 1 ];

L:=NumberField(f);


SetClassGroupBounds("GRH");
rho:=ModPGaloisRepresentation(L,2,2);
sel:=SelmerData(rho);
IsNearlyOrdinary(rho);




//



AttachSpec("ModPGalRep/spec");
AttachSpec("ModPSelmer/spec");

_<x>:=PolynomialRing(Rationals());

f:=x^3 - x^2 - 2*x + 1;
K:=NumberField(f);
a:=K.1;

E := EllipticCurve([K![-2,1,1],K![-2,1,1],K![-1,1,1],K![-2,1,1],K![1,0,0]]);


LL:=SplittingField(DivisionPolynomial(E,2));
_:=IsSubfield(K,LL);

L:=RelativeField(K,LL);
L;

rho:=ModPGaloisRepresentation(L,2,2);
IsNearlyOrdinary(rho);

sel:=SelmerData(rho);
UnramifiedRank(sel);








