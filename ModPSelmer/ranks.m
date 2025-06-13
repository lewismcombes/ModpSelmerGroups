
import "SelmerUtility.m": AllFixedFieldsOfInertia, InertiaInFixedLine;


intrinsic RankFromNumberOfLines(num::RngIntElt,q::RngIntElt) -> RngIntElt 
	{Returns the rank of the F_q vector space with num different lines in it}

	require IsPrimePower(q) : "q must be a prime power";

	F := GF(q);
	p := Characteristic(F);

	qr := 1 + num*(q-1);
	n := Valuation(q,p);

	v := Integers()!(Valuation(qr, p)/n);
	require q^v eq qr: "There is no F_q vector space with this many lines";

	return v;

end intrinsic;



intrinsic RelaxedRank(sel::ModPSelData) -> RngIntElt 
	{Returns the rank of the relaxed Selmer group associated to the Selmer data sel}
	return RankFromNumberOfLines(#sel`normal_subfields, sel`base_rep`finite_field_order);
end intrinsic;



intrinsic NearlyOrdinaryRank(sel::ModPSelData,lines::SeqEnum) -> RngIntElt
	{Returns the rank of the nearly-ordinary Selmer group associated to the Selmer data sel}

	rho:=sel`base_rep;

	require IsNearlyOrdinary(rho): "Representation is not nearly-ordinary";

	require #lines eq #rho`primes_over_char: "Exactly one fixed line per prime over the characteristic is required.";
	// if the lines are given as vector spaces rather than vectors, we convert 
	if Type(lines[1]) eq ModTupFld then 
		require &and [Dimension(u) eq 1 : u in lines]: "Dimension of fixed space must be 1";
		lines := [u.1 : u in lines];
	end if;
	require &and [lines[i] in &join rho`fixed_by_decomp[i] : i in [1..#lines] ] : "Lines must in a space fixed by the decomposition group at each prime.";

	// to do: some requirements on the lines 
	// also the rep should be nearly-ordinary 


	// if we haven't already got the fixed fields of inertia for each extension, we gather them now 
	// this makes things quicker in situations such as, e.g., we have already computed the unramified rank 
	if not assigned sel`normal_subfields_inertia_fixed then 
		sel`normal_subfields_inertia_fixed := AllFixedFieldsOfInertia(sel);
	end if;

	lines_in_NO := 0;

	for i in [1..#sel`normal_subfields] do 
		extension_contributes:=true;
		M := sel`normal_subfields[i];
		
		// we check that the nearly-ordinary Selmer condition is satisfied for each prime over the characteristic 
		for j in [1..#lines] do 
			M_inertia := sel`normal_subfields_inertia_fixed[i][j];
			line := lines[j] * sel`normal_subfields_conjugators[i];
			tt := InertiaInFixedLine(M, M_inertia, line);
			if not tt then 
				// the break here means we sometimes save time
				extension_contributes := false;
				break j;
			end if;
		end for;

		if extension_contributes then 
			lines_in_NO +:= 1;
		end if;
	end for;

	return RankFromNumberOfLines(lines_in_NO, rho`finite_field_order);
end intrinsic;




intrinsic UnramifiedRank(sel::ModPSelData) -> RngIntElt
	{Returns the rank of the unramified Selmer group associated to the Selmer data sel}

	// if we haven't already got the fixed fields of inertia for each extension, we gather them now 
	if not assigned sel`normal_subfields_inertia_fixed then 
		sel`normal_subfields_inertia_fixed := AllFixedFieldsOfInertia(sel);
	end if;

	// Gal(M/L) is the same as the vector space F_q^n that Gal(L/K) acts upon 
	SizeOfGalM := (sel`base_rep`finite_field_order)^(sel`base_rep`dim);
	lines_in_unram := [v: v in sel`normal_subfields_inertia_fixed | &and[Degree(u) eq SizeOfGalM : u in v] ];

	return RankFromNumberOfLines(#lines_in_unram,sel`base_rep`finite_field_order);
end intrinsic;








