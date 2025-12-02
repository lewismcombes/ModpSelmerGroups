

intrinsic IsFaithful(rho::ModPGalRep) -> BoolElt 
	{Returns whether the mod p Galois representation rho is faithful}
	return not &or [rho`representation(g) eq 1 : g in rho`domain | g ne Id(rho`domain)];
end intrinsic;


intrinsic IsUnramifiedOnQuotient(rho::ModPGalRep) -> BoolElt 
	{Returns whether a nearly-ordinary rho with fixed line l is unramified at p on the quotient rho/l}

	require IsNearlyOrdinary(rho): "Representation must be nearly-ordinary";

	if not assigned rho`inertias_over_char then 
		rho`inertias_over_char := [ RamificationGroup(P[1],0) : P in rho`primes_over_char_image ];
	end if;

	V := RSpace(rho`finite_field,rho`dim);

	is_unram := [];
	for i in [1..#rho`primes_over_char] do 

		lines_unram := [];

		for u in rho`fixed_by_decomp[i] do 
			Q,down := quo<V | u>;
			up := Inverse(down);
			Append(~lines_unram,&and [down(up(Q.1) * rho(g)) eq Q.1 : g in rho`inertias_over_char[i]]);
		end for;

		Append(~is_unram,lines_unram);

	end for;

	rho`unramified_on_quotient := is_unram;
	return is_unram;

end intrinsic;


// returns all the one-dimensional subspaces of V
OneDimensionalSubspaces := function(V)
	all := [];
	for v in V do 
		S := sub<V|v>;
		if not S in all and v ne 0 then 
			Append(~all,S);
		end if;
	end for;
	return all;
end function;


intrinsic IsNearlyOrdinary(rho::ModPGalRep) -> BoolElt
	{Decides whether rho restricted to decomposition fixes a 1-dimensional subspace. Can only be applied to 2-dimensional representations.}

	require rho`dim eq 2: "Only defined for 2-dimensional representations";

	if assigned rho`is_nearly_ordinary then 
		return &and rho`is_nearly_ordinary;
	end if;

	decomps := [];
	fixed_by_decomp := [];
	is_NO := [];

	V := RSpace(rho`finite_field,rho`dim);

	for PP in rho`primes_over_char_image do 

		fixed_lines := [];
		decomp := DecompositionGroup(PP[1]);
		Append(~decomps,decomp);

		subs := OneDimensionalSubspaces(V);

		for u in subs do 
			if &and [u*rho`representation(g) eq u : g in decomp] then
				Append(~fixed_lines, u);
			end if;
		end for;

		Append(~is_NO, #fixed_lines gt 0);
		Append(~fixed_by_decomp, fixed_lines);

	end for;

	rho`decomps_over_char := decomps;
	rho`fixed_by_decomp := fixed_by_decomp;
	rho`is_nearly_ordinary := is_NO;

	return &and is_NO;

end intrinsic;


OneDimensionalSubspacesRho:=function(rho)

	if not assigned rho`fixed_by_decomp then 
		is_NO := IsNearlyOrdinary(rho);
	end if;

	if not rho`is_nearly_ordinary then 
		return [];
	end if;

	// I feel like there should be a cleverer way of getting hold of all of these.	
	one_dim_subs := [];
	fixed := rho`fixed_by_decomp;
	for v in fixed do 
		S := sub<fixed | v>;
		if Dimension(S) eq 1 then 
			if not S in one_dim_subs then 
				Append(~one_dim_subs,S);
			end if;
		end if;
	end for;

	return one_dim_subs;

end function;


