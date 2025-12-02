
intrinsic DecompositionGroup(P::RngOrdIdl) -> GrpPerm 
	{The decomposition group of the ideal P}

	L := NumberField(Order(P));
	ZL := MaximalOrder(L);
	A, _, GrpToNFAut := AutomorphismGroup(L);


	// applies the automorphism aut to the ideal id 
	AutIdeal := function(aut,id)
		return ideal<Order(id)|[aut(u) : u in Generators(id)]>;
	end function;

	// tells us if g fixes the ideal P 
	FixesIdeal := function(g)
		return P eq AutIdeal(GrpToNFAut(g),P);
	end function;

	return sub<A | [g : g in A | FixesIdeal(g)]>;

end intrinsic;


intrinsic RamificationGroup(P::RngOrdIdl,n::RngIntElt) -> GrpPerm 
	{Computes the n-th ramification group of P (lower index)}

	// this function goes wrong when given an ideal over an absolute field.
	// TODO: do something about that!

	require IsPrime(P): "Ideal must be prime";
	require n ge -1: "Index too low";

	if n eq -1 then 
		return DecompositionGroup(P);
	end if;

	L := NumberField(Order(P));
	ZL := MaximalOrder(L);
	A, _, GrpToNFAut := AutomorphismGroup(L);

	// we need to use the ZK-generators of the module ZL, since L is a relative extension.
	// this is not always given by Basis(ZL), we need the pseudo-basis.
	gens := [ZL!Eltseq(u) : u in Generators(Module(ZL))];

	// for phi an automorphism of L, returns whether phi also acts on the quotient ZL/P^(n+1)
	ActsOnQuotient := function(phi)
		for b in gens do 
			if not (phi(b) - b) in P^(n+1) then 
				return false;
			end if;
		end for;
		return true;
	end function;

	ram_group_gens := [g : g in A | ActsOnQuotient(GrpToNFAut(g))];

	return sub<A|ram_group_gens>;
end intrinsic;


intrinsic SerreExponent(rho::ModPGalRep,P::RngOrdIdl) -> RngIntElt
	{Returns the exponent of P in the Serre conductor of rho}

	require P in Parent(1*rho`base_order): "Prime ideal must be in the base field of the representation rho";

	// we pick a prime in the image field over P. it doens't matter which one, we only need the orders of the ramification groups, which are all conjugate 
	PP := Factorization(Parent(1*MaximalOrder(rho`image_field))!P)[1,1];
	ram_groups := [RamificationGroup(PP,0)];
	i := 1;
	while #ram_groups[#ram_groups] ne 1 do 
		Append(~ram_groups,RamificationGroup(PP,i));
		i +:= 1;
	end while;

	exp := 0;
	id_mat := rho`representation(ram_groups[1].1)^0;
	for G in ram_groups do 
		kernels := [];
		for g in G do 
			m := rho`representation(g);
			K := Kernel(m - id_mat);
			Append(~kernels,K);
		end for;
		d := Dimension(&meet kernels);
		exp +:= #G/#ram_groups[1] * (rho`dim - d);
	end for;

	return Integers()!exp;
end intrinsic;


intrinsic SerreConductor(rho::ModPGalRep) -> RngOrdIdl
	{Returns the Serre conductor of the representation rho}

	if assigned rho`conductor then 
		cond := rho`conductor;
	else 
		ZK := MaximalOrder(rho`base_field);
		disc := Discriminant(MaximalOrder(rho`image_field));

		// the conductor is P^e for all P dividing the discriminant of L, not including those over the characteristic,
		// where e is the Serre exponent
		cond := &*[P[1]^SerreExponent(rho,P[1]) : P in Factorization(disc) | &and [Valuation(P[1],u) eq 0 : u in rho`primes_over_char] ];

		rho`conductor := cond;
	end if;

	return cond;

end intrinsic;


intrinsic Conductor(rho::ModPGalRep) -> RngOrdIdl 
	{Returns the Serre conductor of the representation rho}
	return SerreConductor(rho);
end intrinsic;



// given two lists of the form [ <prime, trace(Frob_p)> ], compares the traces
// where the two lists overlap, and tells you whether they match.
TracesAreEqual := function(traces1, traces2)
	are_equal := true;
	defined_primes_1 := [u[1] : u in traces1];
	defined_primes_2 := [u[1] : u in traces2];
	for p in PrimesUpTo(100) do 
		if p in defined_primes_1 and p in defined_primes_2 then 
			are_equal := traces1[Index(defined_primes_1,p)] eq traces2[Index(defined_primes_2,p)];
			if not are_equal then 
				return false;
			end if;
		end if;
	end for;

	return are_equal;
end function;


// stretch goals: implement BDJ weights, and the Dirichlet character coming from the determinant
