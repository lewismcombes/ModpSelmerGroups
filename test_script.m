

AttachSpec("ModPGalRep/spec");
AttachSpec("ModPSelmer/spec");

_<x>:=PolynomialRing(Rationals());


K:=NumberField(x^2-x+1);
ZK:=MaximalOrder(K);

// entry 1
//f:=PolynomialRing(K)![-6*K.1 - 4, 18, -9, -12, 15, -6, 1];

// entry 2
//f:=PolynomialRing(K)![ [-2,0], [-10,8], [-13,19], [-4,14], [0,5], [2,2], [1,0] ];

// entry 3, wrong NO rank
//f:=PolynomialRing(K)![ [ -6, -2 ], [ 2, 6 ], [ -4, 5 ], [ 8, -2 ], [ -5, -5 ], [ 0, 2 ], [ 1, 0 ] ];

// entry 6. it's all so fucked rn 
//f:=PolynomialRing(K)![ [ 1, 0 ], [ 0, 0 ], [ 0, 0 ], [ 12, -6 ], [ 0, 0 ], [ 0, 0 ], [ 1, 0 ] ];



// entry 22, wrong number of lines 
//f:=PolynomialRing(K)![ [ 28, -17 ], [ 0, 0 ], [ 13, 9 ], [ 0, 0 ], [ -9, -1 ], [ 0, 0 ], [ 1, 0 ] ];


// entry 27 
//f:=PolynomialRing(K)![ [ -19, 18 ], [ 0, 0 ], [ 0, 0 ], [ 12, -6 ], [ 0, 0 ], [ 0, 0 ], [ 1, 0 ] ];


// entry 28
f:=PolynomialRing(K)![ [ 11, 9 ], [ 0, 0 ], [ 6, -5 ], [ 0, 0 ], [ -6, 1 ], [ 0, 0 ], [ 1, 0 ] ];


// entry 62 (non-trivial unramified group)
//f:=PolynomialRing(K)![ [-32,8], [76, 12], [-79,-59], [24,60], [8,-21], [-6,2], [1,0] ];

// entry 101, three fixed lines 
//f:=PolynomialRing(K)![ [ 2, 0 ], [ 5, 5 ], [ 0, 14 ], [ -3, 6 ], [ 5, -5 ], [ 4, -2 ], [ 1, 0 ] ];



/*
K:=NumberField(x^2-x+2);
ZK:=MaximalOrder(K);

f:=PolynomialRing(K)![ [-2,11], [-8,-12], [8,-2], [4,8], [-5,-1], [0,-2], [1,0]];

*/


L:=ext<K|f>;
ZL:=MaximalOrder(L);


rho:=ModPGaloisRepresentation(L,2,2);

sel:=SelmerData(rho);

IsNearlyOrdinary(rho);

lines:=[u.1 : u in rho`fixed_by_decomp];



NearlyOrdinaryRank(sel,lines);




[[ideal<rho`image_order_abs | [rho`image_order_abs!u : u in Generators(v)]> : v in rho`primes_over_char_image[j]] : j in [1..#rho`primes_over_char]];





A1:=[rho`field_autom_rep(g) : g in rho`domain];
A2:=[sel`normal_subfields_transfer(g) : g in sel`aut];








foo:=function(pol)
	LL:=NumberField(pol);
	_:=IsSubfield(K,LL);
	L:=RelativeField(K,LL);
	f:=DefiningPolynomial(L);
	return [Sprint(Eltseq(u)) : u in Coefficients(f)];
end function;






LL:=AbsoluteField(L);

_<y>:=PolynomialRing(LL);

f1:=y^2 + 1/18*(2*LL.1^11 + 2*LL.1^10 - 
    2*LL.1^9 + 38*LL.1^8 + 35*LL.1^7 - 36*LL.1^6 + 254*LL.1^5 + 200*LL.1^4 - 218*LL.1^3
    + 236*LL.1^2 - 73*LL.1 + 18); 
f2:=y^2 + 1/6*(-2*LL.1^10 - LL.1^9 - 36*LL.1^7 - 
    18*LL.1^6 - 220*LL.1^4 - 109*LL.1^3 + 2*LL.1^2 - 36*LL.1 - 2);





















// 




AttachSpec("ModPGalRep/spec");
AttachSpec("ModPSelmer/spec");

import "ModPSelmer/SelmerUtility.m": OneDimensionalSubspaces;

rel:=[];
no:=[];
unr:=[];


_<x>:=PolynomialRing(Rationals());


K:=NumberField(x^2-x+1);
ZK:=MaximalOrder(K);


for f in pols do 
	LL:=NumberField(f);
	_ := IsSubfield(K,LL);
	L:=RelativeField(K,LL);
	ZL:=MaximalOrder(L);

	rho:=ModPGaloisRepresentation(L,2,2);
	sel:=SelmerData(rho);

	_:=IsNearlyOrdinary(rho);

	all_lines:=OneDimensionalSubspaces(rho`fixed_by_decomp[1]);

	Append(~rel,RelaxedRank(sel));
	Append(~no,[NearlyOrdinaryRank(sel,[u.1]) : u in all_lines]);
	Append(~unr,UnramifiedRank(sel));
	print no[#no];

end for;


