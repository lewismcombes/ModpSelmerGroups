
SparsePermutationMatrix:=function(R, g, scalars, chi)
	d := Degree(Parent(g));
	seq := [<i,i^g,1> : i in [1..d]];
	return SparseMatrix(R,d,d,seq);
end function;


MatPerm := function(PL,r,mat)
	Z := Integers();
	perm := [];
	scalars := [];
	for u in PL do 
		_, v, e := r(ChangeRing(u,Z)*mat,true,true);
		Append(~perm,Index(PL,v));
	end for;
	return Sym(#PL)!perm, scalars;
end function;

IdIndex := function(PL, r)
	_, v := r(Vector([0,1]),true,false);
	return Index(PL,v);
end function;
