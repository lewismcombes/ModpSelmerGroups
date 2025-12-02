
AttachSpec("spec");

//N := 3721;
//E := EllipticCurve([1, 0, 0, -515436, 129970135]);
//E := EllipticCurve([1, 0, 1, -139, 561]);

N := 30752;
E := EllipticCurve([0, -1, 0, -20416765, -35501824363]);

//N := 61504;
//E := EllipticCurve([0, -1, 0, -5311, 150761]);

//N := 10502;
//E := EllipticCurve([1, 1, 0, -59, 4189]);



P := PeriodPolynomials(N,3);

space := P`space; 

for p in PrimesUpTo(50) do 
	time if GCD(3*Conductor(E),p) eq 1 then 
		T := HeckeOperator(P,p);
		I := T^0;
		tr := TraceOfFrobenius(E,p);

		space := space meet Kernel(T - tr*I);
		print Dimension(space);
		if Dimension(space) eq 1 then 
			break p;
		end if;
	end if;
end for;

(space.1)[P`id_index];
