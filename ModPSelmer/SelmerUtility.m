
// from Cohen's Advanced Topics
SelmerModulusExponent := function(rho,P)
	r := rho`dim;
	p := rho`char;
	e := RamificationIndex(P,rho`char);
	return Ceiling((r*p*e)/(p-1))+1;
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


// returns whether rho is conjugate in GL(n,F_q) to the matrices given by act
IsConjugateToAction := function(rho,act)
	G:=GL(rho`dim,rho`finite_field_order);

	for g in G do 
		if [g^-1*rho`representation(h)*g : h in rho`domain] eq act then 
			return true, g;
		end if;
	end for;

	return false, Id(G);
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








