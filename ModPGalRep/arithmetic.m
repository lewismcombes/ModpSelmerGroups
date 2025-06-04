

intrinsic Filtration(rho::ModPGalRep,H::GrpPerm) -> SeqEnum 
	{Attempts to find filtrations on rho with respect to the group H}

	// what should go here? :s

end intrinsic;



intrinsic IsNearlyOrdinary(rho::ModPGalRep) -> BoolElt
	{Decides whether rho restricted to decomposition fixes a 1-dimensional subspace. Can only be applied to 2-dimensional representations.}

	require rho`dim eq 2: "Only defined for 2-dimensional representations";


	decomps:=[];
	fixed_by_decomp:=[];
	is_NO:=[];

	for PP in rho`primes_over_char_image do 

		decomp := DecompositionGroup(PP[1]);
		Append(~decomps,decomp);

		kernels := [Kernel(rho(g) - 1) : g in decomp];
		fixed := &meet kernels;
		
		Append(~fixed_by_decomp, fixed);
		Append(~is_NO, Dimension(fixed) ge 1);

	end for;

	rho`decomps_over_char := decomps;
	rho`fixed_by_decomp := fixed_by_decomp;
	rho`is_nearly_ordinary := is_NO;

	return &and is_NO;

end intrinsic;





OneDimensionalSubspaces:=function(rho)

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







