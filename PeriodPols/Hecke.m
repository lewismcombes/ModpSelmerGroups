
import "Utility.m" : SparsePermutationMatrix, MatPerm;

intrinsic HeckeOperator(P::PerPolsGL2Q,p::RngIntElt) -> MtrxSprs
	{Return the Hecke operator T_p acting on a space of period polynomials}

	require IsPrime(p): "Hecke operator only defined for prime index";
	require GCD(P`level,p) eq 1: "Hecke operator index must not divide level";
	require p ne P`char: "Hecke operator index must not be characteristic";

	if IsDefined(P`HeckeOperators,p) then 
		return P`HeckeOperators[p];
	else 
		new_H := [];
		for u in HeilbronnCremona(p) do 
			MH, scalMH := MatPerm(P`PL, P`r, Matrix(Integers(),2,2,[u[4],-u[2],-u[3],u[1]]));
			Append(~new_H, SparsePermutationMatrix(P`field, MH, scalMH, P`chi ));
		end for;
		Tp := &+new_H;
		P`HeckeOperators[p] := Tp;
		Append(~P`HeckeComputed,p);
		return Tp;
	end if;
end intrinsic;


