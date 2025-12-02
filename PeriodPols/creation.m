
import "Utility.m" : SparsePermutationMatrix, MatPerm, IdIndex;

declare type PerPolsGL2Q;

declare attributes PerPolsGL2Q:
	space, level, dim, char, chi, PL, field, r, HeckeOperators, HeckeComputed, id_index;


intrinsic Print(P::PerPolsGL2Q)
	{}
	printf "Space of extended period polynomials of level Gamma0(%o) and weight 2 in characteristic %o of dimension %o", P`level, P`char, P`dim;
end intrinsic;


intrinsic PeriodPolynomials(chi::GrpDrchElt, p::RngIntElt) -> PerPolsGL2Q
	{Return the space of extended period polynomials for character chi in characteristic p}

	require IsPrime(p): "Characteristic must be prime";

	N := Modulus(chi);

	P := New(PerPolsGL2Q);
	P`level := N;
	P`char := p;
	P`chi := chi;

	Z := Integers();
	PL, r := ProjectiveLine(quo< Z | N*Z >);
	P`PL := PL;
	P`r := r;

	F := GF(p);
	P`field := F;

	T := Matrix(Z,2,2,[1,1,0,1]);
	S := Matrix(Z,2,2,[0,-1,1,0]);
	U := T*S;
	J := Matrix(Z,2,2,[-1,0,0,1]);

	/*
	MS, scalS := MatPerm(PL, r, S);
	MU, scalU := MatPerm(PL, r, U);
	MJ, scalJ := MatPerm(PL, r, J);

	PS:=SparsePermutationMatrix(F, MS, scalS, chi);
	PU:=SparsePermutationMatrix(F, MU, scalU, chi);
	PJ:=SparsePermutationMatrix(F, MJ, scalJ, chi);
	ID:=PS^0;
	*/

	// we use this simplication to compute only one kernel instead of two 
	// see 
	/*
	Zagier, D., From quadratic functions to modular functions in Number Theory in Progress.
	Vol 2, Proceedings of Internat. Conference on Number Theory, Zakopane 1997, de
	Gruyter, Berlin (1999), 1147-1178.
	*/
	// although actually zagier leaves it as an exercise. but it's true, apparently. 

	M1 := U*S;
	M2 := U^2*S;

	MM1, scalM1 := MatPerm(PL, r, M1);
	MM2, scalM2 := MatPerm(PL, r, M2);
	MJ, scalJ := MatPerm(PL, r, J);

	PM1 := SparsePermutationMatrix(F, MM1, scalM1, chi);
	PM2 := SparsePermutationMatrix(F, MM2, scalM2, chi);
	PJ := SparsePermutationMatrix(F, MJ, scalJ, chi);
	ID:=PJ^0;

	K := Kernel(ID - PM1 - PM2) meet Kernel(ID-PJ);

	P`space := K;
	P`dim := Dimension(K);

	P`HeckeOperators := AssociativeArray(Z);
	P`HeckeComputed := [];

	P`id_index := IdIndex(PL, r);

	return P;
end intrinsic;


intrinsic PeriodPolynomials(N::RngIntElt,p::RngIntElt) -> PerPolsGL2Q
	{Return the space of extended period polynomials for Gamma0(N) in characteristic p}
	
	require N gt 0: "Level must be a positive integer";
	chi := DirichletGroup(N).0;	

	return PeriodPolynomials(chi,p);
end intrinsic;

