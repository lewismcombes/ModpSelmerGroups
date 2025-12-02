
load "all_SD16_data.m";

AttachSpec("ModPGalRep/spec");
AttachSpec("PeriodPols/spec");

K := QNF();
ZK := MaximalOrder(K);
P<x>:=PolynomialRing(K);

inds := [ 1, 70, 71, 72, 73, 74, 77, 80, 85, 86, 90, 93, 94, 96, 98, 99, 102, 106, 110, 115, 116, 118, 119, 121, 122, 123, 125, 128, 129, 130, 133, 136, 140, 142, 143, 144, 147, 151, 154, 155, 157, 162, 165, 167, 168, 175, 176, 177, 178, 184 ];

for j in inds do 

	dd := data[j];
	f := P!dd`polynomial;
	L := ext< K | f >;
	rho := ModPGaloisRepresentation(L,3,2);
	disc := Discriminant(rho`field_order);

	// pick out the irreducible module coming from L associated to our representation
	PP := [u[1]*ZK : u in dd`traces];
	for i in [1..#rho`possible_irreds] do
		repp := rho`possible_irreds[i];
		irred_traces := [<Norm(v), Trace(repp(rho`frobenius_elements[v]))> : v in PP | GCD(v,disc) eq 1*ZK];
		if irred_traces eq dd`traces then 
			ChangeRepresentation(rho,i);
			break i;
		end if;
	end for;

	// obtain the conductor of rho, so we can find its associated cohomology class 
	cond := Conductor(rho);
	_, N := IsPrincipal(cond);
	N := Integers()!N;

	Pols := PeriodPolynomials(N, 3);

	// we pick out the eigenspace of Pols corresponding to rho 
	eigenspace := Pols`space;
	n := 1;

	while Dimension(eigenspace) gt 1 and n le 100 do 
		p := NthPrime(n);
		// we only check those primes not dividing the conductor and characteristic,
		// where the representation and the cohomology class might differ 
		if GCD(p*ZK, 3*cond) eq 1*ZK then 
			Tp := HeckeOperator(Pols,p);
			I := Tp^0;
			tr := Trace(rho(FrobeniusElement(L,p*ZK)));

			// no need to do this if we have the whole space. and there's no way to avoid 
			// at least the first hecke kernel being a beefy calculation 
			if eigenspace ne P`space then 
				// now we compute the action of T on space (this should save time as space gets smaller)
				TT := Matrix([Solution(Matrix(Basis(eigenspace)), eigenspace.i * T ) : i in [1..Dimension(eigenspace)]]);
				KK := Kernel(TT - tr*TT^0);
				new_basis := [ &+[Eltseq(KK.j)[i] * eigenspace.i : i in [1..Degree(KK)]] : j in [1..Dimension(KK)] ];

				eigenspace := sub<eigenspace | new_basis>;
			else
				eigenspace := eigenspace meet Kernel(Tp - tr*I);
			end if;

			print Dimension(eigenspace);

			// we keep the hecke operators that we compute for sensible reasons 
			// but actually in this instance it does more harm than good, eating up 
			// memory on something we're not going to reuse 
			Remove(~Pols`HeckeOperators,p);

		end if;
		
		n := n+1;
	end while;

	if Dimension(eigenspace) eq 1 then 
		pol := eigenspace.1;
		period := pol[Pols`id_index];
		print j, ",", period;
	else 
		print j, ",", "could not find period in 100 primes";
	end if;

end for;





