

intrinsic FrobeniusElement(L::FldNum,P::RngOrdIdl) -> GrpPermElt 
	{Returns a Frobenius element in Gal(L) of the prime P. If P is a prime of the base field of L, Frobenius is only determined up to a choice of ideal in L over P!}

	require IsPrime(P): "Ideal must be prime";

	ZL:=MaximalOrder(L);
	ZK:=MaximalOrder(BaseField(L));

	// this was behaving weirdly but we do need it! why aren't number fields equal?
	//require NumberField(Order(P)) eq L or NumberField(Order(P)) eq BaseField(L): "Ideal must be of L or its base field";

	// in this case, the Frobenius is determined exactly by the ideal 
	if P in Parent(1*MaximalOrder(L)) then 
		PP:=P;
		pow:=Norm(Norm(P));
		require not IsRamified(P): "Field cannot be ramified at prime";
	// in this case, the Frobenius is determined up to a choice of prime in L over P
	else 
		PP:=Factorization(Parent(1*ZL)!P)[1,1];
		pow:=Norm(P);
		require not IsRamified(P,ZL): "Field cannot be ramified at prime"; 
	end if;



	F,down:=ResidueClassField(PP);

	// a generating set for ZL as a ZK-module
	gens:=[ZL!Eltseq(u) : u in Generators(Module(ZL))];

	A,_,m:=AutomorphismGroup(L);

	// a little utility function for checking if we have a Frobenius
	IsFrob:=function(g)
		for b in gens do 
			if not down(m(g)(b)) eq down(b)^pow then 
				return false;
			end if;
		end for;
		return true;
	end function;

	for g in A do 
		if IsFrob(g) then 
			return g;
		end if;
	end for;

end intrinsic;






















