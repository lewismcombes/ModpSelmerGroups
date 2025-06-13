

intrinsic Filtration(rho::ModPGalRep,H::GrpPerm) -> SeqEnum 
	{Attempts to find filtrations on rho with respect to the group H}

	// what should go here? :s

end intrinsic;


intrinsic IsFaithful(rho::ModPGalRep) -> BoolElt 
	{Returns whether the mod p Galois representation rho is faithful}
	return not &or [rho`representation(g) eq 1 : g in rho`domain | g ne Id(rho`domain)];
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

	decomps:=[];
	fixed_by_decomp:=[];
	is_NO:=[];

	V := RSpace(GF(rho`finite_field_order),rho`dim);

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
		is_NO:=IsNearlyOrdinary(rho);
	end if;

	if not rho`is_nearly_ordinary then 
		return [];
	end if;

	// I feel like there should be a cleverer way of getting hold of all of these.	
	one_dim_subs:=[];
	fixed:=rho`fixed_by_decomp;
	for v in fixed do 
		S:=sub<fixed | v>;
		if Dimension(S) eq 1 then 
			if not S in one_dim_subs then 
				Append(~one_dim_subs,S);
			end if;
		end if;
	end for;

	return one_dim_subs;

end function;







