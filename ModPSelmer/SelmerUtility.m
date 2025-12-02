
// from Cohen's Advanced Topics
SelmerModulusExponent := function(rho,P)
	r := Valuation(#rho`finite_field,rho`char) * rho`dim;
	p := rho`char;
	e := RamificationIndex(P,rho`char);
	return Floor((r*p*e)/(p-1))+1;
end function;


// write L for the image field of rho. this function returns the maximal abelian elementary 
// p-extension of L, unramified outside p = char(rho)
SelmerModulus := function(rho)
	return &*[ P^SelmerModulusExponent(rho,P) : P in &cat rho`primes_over_char_abs ];
end function;


// returns the map mm: R2 -> {ideals of ZL} that cuts out the p subextension of R.
// this map can be used with RayClassField to get the extension itself
MaximalPExtensionHom := function(R,m,p)

  h := hom< R-> R | [p*R.i : i in [1..Ngens(R)]]>;
  Q, mq := quo<R | Image(h) >;
  qm := Inverse(mq);
  mm := qm * m;

  return mm;
end function;


// essentially the function RepresentationMatrix, excpet for finite fields 
MultMat := function(elt)
	F2 := Parent(elt);
	F1 := BaseField(F2);
	return Matrix(F1,[Eltseq(elt*b) : b in Basis(F2)]);
end function;


// by treating F_q as F_p^n, this function turns a matrix in GL(k,F_q)
// into a matrix in GL(nk,F_p). 
FqMatToFp := function(mat)
	return BlockMatrix(Nrows(mat),Ncols(mat),[MultMat(u) : u in Eltseq(mat)]);
end function;


// same as the above, but for vectors 
FqVecToFp := function(vec)
	return FqMatToFp(vec)[1];
end function;


// returns whether rho is conjugate in GL(n,F_q) to the matrices given by act
IsConjugateToAction := function(rho,act)
	G:=GL(rho`dim,rho`finite_field);

	for g in G do 
		if [g^-1*rho(h)*g : h in rho`domain] eq act then 
			return true, g;
		end if;
	end for;

	return false, Id(G);
end function;


AllStabilisingMats:=function(G,m)
	if m eq Id(G) then
		return [g : g in G];
	else 
		return [g : g in G | g^-1*m*g eq m];
	end if;
end function;


IsConjugateToAction2 := function(rho,act)
	GG := GL(rho`dim * rho`finite_field_degree,rho`char);
	// since the Fp matrices don't ever change for a given rho, we should store and re-use them 
	rhoFp := [FqMatToFp(rho(g)) : g in rho`domain];
	rhoFp_stabs := [AllStabilisingMats(GG,GG!u) : u in rhoFp];

	conjs:=[];
	for i in [1..#rhoFp] do 
		t,g:=IsConjugate(GG,GG!rhoFp[i],GG!act[i]);
		if t then 
			Append(~conjs,g);
		end if;
	end for;

	if #conjs ne #rhoFp then 
		return false, [];
	else 
		sets:=[Set([rhoFp_stabs[i][j]*conjs[i] : j in [1..#rhoFp_stabs[i]]]) : i in [1..#rhoFp]];
		return true, SetToSequence(&meet sets);
	end if;
end function;



// returns the fixed field of inertia in the FldAb M for the primes over the characteristic of the 
// base representation of sel 
FixedFieldOfInertia:=function(M,P)
	_, m, minf := NormGroup(M);
	Mur := RayClassField(m/P^Valuation(m,P), minf);
	return Mur meet M;
end function;


// returns all the fixed fields of inertia of the normal subfields of sel 
AllFixedFieldsOfInertia := function(sel)
	rho := sel`base_rep;

	inertia_fixed := [];
	for M in sel`normal_subfields do 
		M_inertia_fixed := [];
		for PP in rho`primes_over_char_abs do 
			Append(~M_inertia_fixed, FixedFieldOfInertia(M,PP[1]));
		end for;
		Append(~inertia_fixed, M_inertia_fixed);
	end for;

	return inertia_fixed;
end function;


// Takes a vector representating a line in V, and returns the
// subfield of M corresponding to M^V, i.e. the elements fixed by V
// currently only doing this for 2 diml F_p reps, i.e. V = F_p + F_p
VectorToSubfield := function(M,vec)
  GM := Domain(NormGroup(M)); // Gal(M/L)
  Z := Integers();
  return AbelianSubfield(M,sub< GM | Z!(vec[1])*GM.1 + Z!(vec[2])*GM.2 >);
end function;


// returns whether the subfield of M fixed by the line is inside the fixed field of inertia
// i.e. tells us whether the inertia subgroup is in the line 
// alas, I tried to do it in fewer variables, but I couldn't make it work
InertiaInFixedLine := function(M, M_inertia_fixed, line)
	return VectorToSubfield(M,line) subset M_inertia_fixed;
end function;


// for V a vector space over a finite field F, return the 
// one-dimensional subspaces. a very straightforward and 
// ignorant algorithm. just check every single one! 
OneDimensionalSubspaces := function(V)
	spaces := [];

	for v in V do 
		VV:=sub<V | v>;
		if Dimension(VV) eq 1 then 
			if not VV in spaces then 
				Append(~spaces,VV);
			end if;
		end if;
	end for;

	return spaces;
end function;


// given list, the value of rho`fixed_by_decomp, returns all the fixed lines 
// over each prime. this accounts for situations where subspaces are fixed that 
// have dimension larger than 1. 
AllFixedLines := function(list)

	fixed_lines := [];

	for l in list do 
		lines_over_prime := [];
		// each fixed space u in l has some lines inside it 
		for u in l do 
			lines := OneDimensionalSubspaces(u);
			for v in lines do 
				// we only keep the lines we don't already have 
				if not v in lines_over_prime then 
					Append(~lines_over_prime,v);
				end if;
			end for;
		end for;
		Append(~fixed_lines,lines_over_prime);
	end for;

	return fixed_lines;
end function;


// a little combinatorial utility function, gives all of the possible 
// pairs of fixed lines (which each give their own selmer group)
AllLineCombinations := function(rho)
	all_fixed_lines := AllFixedLines(rho`fixed_by_decomp);
	all_combos:=[ [] ];

	for u in all_fixed_lines do 
		all_combos := &cat [[ w cat [v] : w in all_combos] : v in u];
	end for;

	return all_combos;
end function;
