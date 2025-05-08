

intrinsic RamificationGroup(P::RngOrdIdl,n::RngIntElt) -> GrpPerm 
	{Computes the i-th ramification group of P (lower index)}

	ram_group_gens:=[];

	L:=NumberField(Order(P));
	ZL:=MaximalOrder(L);
	A,_,m:=AutomorphismGroup(L);

	// we need to use the ZK-generators of the module ZL, since L is a relative extension
	gens:=[ZL!Eltseq(u) : u in Generators(Module(ZL))];

	for g in A do 
		keep:=true;
		for b in gens do 
			if not (m(g)(b) - b) in P^(n+1) then 
				keep:=false;
				break b;
			end if;
		end for;
		if keep then 
			Append(~ram_group_gens,g);
		end if;
	end for;

	return sub<A|ram_group_gens>;
end intrinsic;



intrinsic SerreExponent(rho::ModPGalRep,P::RngOrdIdl) -> RngIntElt
	{Returns the exponent of P in the Serre conductor of rho}

	require P in Parent(1*MaximalOrder(rho`base_field)): "Prime ideal must be in the base field of the representation rho";

	// we pick a prime in the image field over P. it doens't matter which one, we only need the orders of the ramification groups, which are all conjugate 
	PP:=Factorization(Parent(1*MaximalOrder(rho`image_field))!P)[1,1];
	ram_groups:=[RamificationGroup(PP,0)];
	i:=1;
	while #ram_groups[#ram_groups] ne 1 do 
		Append(~ram_groups,RamificationGroup(PP,i));
		i+:=1;
	end while;

	ind:=0;
	for G in ram_groups do 
		kernels:=[];
		for g in G do 
			m:=rho`representation(g);
			K:=Kernel(m-m^0);
			Append(~kernels,K);
		end for;
		d:=Dimension(&meet kernels);
		ind+:=#G/#ram_groups[1] * (rho`dim - d);
	end for;

	return Integers()!ind;
end intrinsic;





intrinsic SerreConductor(rho::ModPGalRep) -> RngOrdIdl
	{Returns the Serre conductor of the representation rho}

	if assigned rho`conductor then 
		return rho`conductor;
	else 

		ZK:=MaximalOrder(rho`base_field);
		primes_over_char:=[u[1] : u in Factorization(rho`char*ZK)];
		disc:=Discriminant(MaximalOrder(rho`image_field));

		cond:=1*ZK;

		for P in Factorization(disc) do
			// this excludes primes over the characteristic 
			if &and [Valuation(P[1],u) eq 0 : u in primes_over_char] then
				cond*:=P[1]^SerreExponent(rho,P[1]);
			end if;
		end for;

		rho`conductor:=cond;
		return cond;
	end if;

end intrinsic;

