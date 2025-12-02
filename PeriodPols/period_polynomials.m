


PeriodPolynomials := function(N,p)

	Z := Integers();
	Q := quo<Z|N*Z>;

	F := GF(p);

	PL,r := ProjectiveLine(Q);

	T := Matrix(Z,2,2,[1,1,0,1]);
	S := Matrix(Z,2,2,[0,-1,1,0]);
	U := T*S;
	J := Matrix(Z,2,2,[-1,0,0,1]);

	MS := MatPerm(PL, r, S);
	MU := MatPerm(PL, r, U);
	MJ := MatPerm(PL, r, J);

	PS:=SparsePermutationMatrix(F,MS);
	PU:=SparsePermutationMatrix(F,MU);
	PJ:=SparsePermutationMatrix(F,MJ);
	ID:=PS^0;

	K:=Kernel(ID+PS) meet Kernel(ID+PU+PU^2) meet Kernel(ID-PJ);

	return K;

end function;


Z := Integers();
N := 3721;
char := 3;
F := GF(3);


HH:=AssociativeArray(Z);

for p in PrimesUpTo(50) do
	if N mod p ne 0 then 
		new_H:=[];
		if not IsDefined(HH,p) then 
			for u in HeilbronnCremona(p) do 
				MH,scalH:=MatPerm(Matrix(Z,2,2,[u[4],-u[2],-u[3],u[1]]));
				Append(~new_H,SparsePermutationMatrix(F,MH,scalH));
			end for;
			time HH[p]:=&+new_H;
		end if;
	end if;
end for;

eigs:=[
[5,0],
[7,0],
[11,0],
[13,0],
[17,1],
[19,0],
[23,0],
[29,2],
[37,0],
[41,0],
[43,0],
[47,1],
];


KK:=K;

for u in eigs do 
	KK:=KK meet Kernel(HH[u[1]] - u[2]*ID);
	Dimension(KK);
	if Dimension(KK) eq 1 then 
		break;
	end if;
end for;




