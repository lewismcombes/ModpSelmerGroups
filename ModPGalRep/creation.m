

declare type ModPGalRep;


declare attributes ModPGalRep:
	base_field, image_field, dim, char, field_order, frobenius_elements, domain, field_autom_rep, 
	module_field, representation, ramification, conductor;






intrinsic Print(rho::ModPGalRep)
	{}
	str:="Mod " cat Sprint(rho`char) cat " Galois representation of dimension " cat Sprint(rho`dim) cat " over " cat Sprint(rho`base_field);

	if assigned rho`conductor then 
		str cat:="\nwith conductor of norm " cat Sprint(Norm(rho`conductor));
	end if;

	printf str;
end intrinsic;





intrinsic ModPGaloisRepresentation(L::FldNum,q::RngIntElt,n::RngIntElt) -> ModPGalRep
	{Returns a dimension n Galois representation over F_q with image Gal(L)}

	require IsNormal(L): "Field must be Galois";
	require #PrimeFactors(q) eq 1: "Field order must be a prime power";
	require n ge 1: "Dimension must be at least 1";


	rho:=New(ModPGalRep);
	rho`char:=PrimeFactors(q)[1];
	rho`field_order:=q;
	rho`dim:=n;
	rho`base_field:=BaseField(L);
	rho`image_field:=L;
	rho`module_field:=GF(q);



	A,S,m:=AutomorphismGroup(L,rho`base_field);
	rho`domain:=A;
	rho`field_autom_rep:=m;



	ZK:=MaximalOrder(rho`base_field);
	rho`frobenius_elements:=AssociativeArray(Parent(1*ZK));


	irreds:=[u : u in IrreducibleModules(rho`domain,rho`module_field) | Dimension(u) eq rho`dim];
	require #irreds ge 1: "No such module found";
	// we'll need to do something with frobenius stuff to make sure we get the right representation 
	// for now we'll just pick the first one 
	rho`representation:=Representation(irreds[1]);



	

	return rho;

end intrinsic;














