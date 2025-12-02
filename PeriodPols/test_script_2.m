
AttachSpec("spec");

//N := 3721;
//E := EllipticCurve([1, 0, 0, -515436, 129970135]);
//E := EllipticCurve([1, 0, 1, -139, 561]);

//N := 30752;
//E := EllipticCurve([0, -1, 0, -20416765, -35501824363]);

N := 61504;
E := EllipticCurve([0, -1, 0, -5311, 150761]);


//N := 10502;
//E := EllipticCurve([1, 1, 0, -59, 4189]);


P := PeriodPolynomials(N,3);

space := P`space; 

for p in PrimesUpTo(50) do 
	time if GCD(3*Conductor(E),p) eq 1 then 
		T := HeckeOperator(P,p);
		I := T^0;
		tr := TraceOfFrobenius(E,p);

		// no need to do this if we have the whole space. and there's no way to avoid 
		// at least the first hecke kernel being a beefy calculation 
		if space ne P`space then 
			// now we compute the action of T on space (this should save time as space gets smaller)
			TT := Matrix([Solution(Matrix(Basis(space)), space.i * T ) : i in [1..Dimension(space)]]);
			KK := Kernel(TT - tr*TT^0);
			new_basis := [ &+[Eltseq(KK.j)[i] * space.i : i in [1..Degree(KK)]] : j in [1..Dimension(KK)] ];

			space := sub<space | new_basis>;
		else
			space := space meet Kernel(T - tr*I);
		end if;

		print Dimension(space);
		if Dimension(space) eq 1 then 
			break p;
		end if;
	end if;
end for;

(space.1)[P`id_index];
