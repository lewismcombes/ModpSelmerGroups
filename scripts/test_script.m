

AttachSpec("ModPGalRep/spec");
AttachSpec("ModPSelmer/spec");
import "ModPSelmer/SelmerUtility.m" : AllLineCombinations;

SetClassGroupBounds("GRH");


_<x>:=PolynomialRing(Rationals());

//K := NumberField(x^2-x+2);
K:=QNF();
ZK:=MaximalOrder(K);
//f:=PolynomialRing(K)![ [ 32, -48 ], [ -48, 24 ], [ -54, 40 ], [ -10, -4 ], [ -1, 0 ], [ 2, -4 ], [ 1, 0 ] ];
//f := PolynomialRing(K)! [ [ 23, -1 ], [ 0, 0 ], [ 35, 2 ], [ 0, 0 ], [ 5, -1 ], [ 0, 0 ], [ 1, 0 ] ];

f:=PolynomialRing(K)![ 41643837, 117933768, 169385310, 168420924, 116575978, 
        48162244, 7064422, -2597052, -1305921, -180364, 2550, 4060, 948, 96, 16,
        8, 1 ];



L:=ext<K|f>;
ZL:=MaximalOrder(L);


rho:=ModPGaloisRepresentation(L,3,2);
ChangeRepresentation(rho,2);

frob_data := [<p, Trace(rho(rho`frobenius_elements[p*ZK])), Determinant(rho(rho`frobenius_elements[p*ZK]))> : p in PrimesUpTo(100) | IsDefined(rho`frobenius_elements,p*ZK)];

RepChar(rho,frob_data,Conductor(rho),3);









ChangeRepresentation(rho,2);
_:=IsNearlyOrdinary(rho);



time sel:=SelmerData(rho);

ll:=AllLineCombinations(rho);

for l in ll do 
	NearlyOrdinaryRank(sel,l);
end for;








// 




AttachSpec("ModPGalRep/spec");
AttachSpec("ModPSelmer/spec");

import "ModPSelmer/SelmerUtility.m": AllLineCombinations;

rel:=[];
no:=[];
unr:=[];


SetClassGroupBounds("GRH");


_<x>:=PolynomialRing(Rationals());


//K:=NumberField(x^2-x+1);
//K:=NumberField(x^2+1);
//K:=NumberField(x^2-x+2);
//K:=NumberField(x^2+2);
K:=NumberField(x^2-x+3);
ZK:=MaximalOrder(K);


time for f in pols do 
	LL:=NumberField(f);
	_ := IsSubfield(K,LL);
	L:=RelativeField(K,LL);
	ZL:=MaximalOrder(L);

	rho:=ModPGaloisRepresentation(L,2,2);
	sel:=SelmerData(rho);

	_:=IsNearlyOrdinary(rho);

	all_line_combos := AllLineCombinations(rho);

	Append(~rel,RelaxedRank(sel));
	Append(~no,[NearlyOrdinaryRank(sel,[v.1 : v in u]) : u in all_line_combos]);
	Append(~unr,UnramifiedRank(sel));
	print #no, no[#no];

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
import "ModPSelmer/SelmerUtility.m" : AllLineCombinations;

SetClassGroupBounds("GRH");


_<x>:=PolynomialRing(Rationals());

K := QNF();
ZK:=MaximalOrder(K);
f := PolynomialRing(K)! (x^18 + 5*x^16 + 12*x^14 + 29*x^12 + 55*x^10 + 57*x^8 + 39*x^6 + 22*x^4 + 8*x^2 + 1);




L:=ext<K|f>;
ZL:=MaximalOrder(L);


rho:=ModPGaloisRepresentation(L,4,2);
ChangeRepresentation(rho,2);

_:=IsNearlyOrdinary(rho);



time sel:=SelmerData(rho);

ll:=AllLineCombinations(rho);

for l in ll do 
	NearlyOrdinaryRank(sel,l);
end for;


IsConjugateToAction := function(rho,act)
	G:=GL(rho`dim,#rho`finite_field);

	for g in G do 
		if [g^-1*rho`representation(h)*g : h in rho`domain] eq act then 
			return true, g;
		end if;
	end for;

	return false, Id(G);
end function;



//


F:=GF(4);
t:=F.1;

Eltseq(t);

m:=Matrix(F,2,2,[t,0,0,t]);

MultiplicationMatrix := function(elt)
	F:=Parent(elt);
	B:=Basis(F);
	return Matrix([Eltseq(b*elt) : b in B]);
end function;

FqMatrixToFpMatrix := function(mat)
	return BlockMatrix([[MultiplicationMatrix(mat[j,i]) : i in [1..2]] : j in [1..2]]);
end function;



Elts:=[u : u in F];
MultMats:=[MultiplicationMatrix(u) : u in elts];




IsFqMatrix := function(mat)
	submats:=[ [Submatrix(mat,1+2*j,1+2*i,2,2) : i in [0..1]] : j in [0..1]];
	elts:=[];
	for u in submats do
		new_row:=[]; 
		for v in u do
			if v in MultMats then 
				Append(~new_row,Elts[Index(MultMats,v)]);
			end if;
		end for;

		Append(~elts,new_row);
	end for;

	if &and [#u eq 2: u in elts ] then 
		return true, Matrix(elts);
	else 
		return false,0;
	end if;
end function;

Fqify := function(list)
	new_mats := [];

	for u in list do 
		_,m := IsFqMatrix(u);
		Append(~new_mats,m);
	end for;
	return new_mats;
end function;



aa:=[FqMatrixToFpMatrix(rho(g)) : g in rho`domain];




