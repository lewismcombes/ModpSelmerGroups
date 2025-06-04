

// TODO:
// assign ramification in ModPGalRep
// choose module using frobenius data 
// can we specify ramification ahead of time? 



declare type ModPGalRep;


declare attributes ModPGalRep:
	base_field, image_field, image_order, image_field_abs, image_order_abs, dim, char, finite_field_order, finite_field_degree, field_order, field_order_gens, frobenius_elements, domain, field_autom_rep, module_field, 
	representation, traces, ramification, conductor, primes_over_char, primes_over_char_image, primes_over_char_abs, decomps_over_char, fixed_by_decomp, is_nearly_ordinary;






intrinsic Print(rho::ModPGalRep)
	{}
	str := Sprintf("Mod %o Galois representation of dimension %o over %o",
	rho`char, rho`dim, rho`base_field);

	if assigned rho`conductor then 
		str cat:= Sprintf("\nwith conductor of norm %o", rho`conductor);
    end if;

	printf "%o", str;
end intrinsic;





intrinsic ModPGaloisRepresentation(L::FldNum,q::RngIntElt,n::RngIntElt) -> ModPGalRep
	{Returns a dimension n Galois representation over F_q with image Gal(L)}

	require IsNormal(L): "Field must be Galois";
	require IsPrimePower(q): "Field order must be a prime power";
	require n ge 1: "Dimension must be at least 1";

	rho := New(ModPGalRep);
	F := GF(q);
	p := Characteristic(F);
	rho`finite_field_order := q;
	rho`finite_field_degree := Valuation(q,p);
	rho`dim := n;
	rho`base_field := BaseField(L);
	rho`image_field := L;
	rho`module_field := F;
	rho`char := p;

	A, S, m := AutomorphismGroup(L,rho`base_field);
	rho`domain := A;
	rho`field_autom_rep := m;

	// we check there is at least one irreducible module before we do lengthier computations like the maximal order
	irreds := [u : u in IrreducibleModules(rho`domain,rho`module_field) | Dimension(u) eq rho`dim];
	require #irreds ge 1: "No such module found";
	
	ZL := MaximalOrder(L);
	rho`field_order := ZL;
	rho`field_order_gens := [ZL!Eltseq(u) : u in Generators(Module(ZL))];

	L_abs := AbsoluteField(L);
	rho`image_field_abs := L_abs;
	ZL_abs := MaximalOrder(L_abs);
	rho`image_order_abs := MaximalOrder(L_abs);

	ZK := MaximalOrder(rho`base_field);
	rho`frobenius_elements := AssociativeArray(Parent(1*ZK));
	primes_over_char := [u[1] : u in Factorization(p*ZK)];
	rho`primes_over_char := primes_over_char;
	rho`primes_over_char_image := [ [u[1] : u in Factorization(Parent(1*ZL)!P)] : P in primes_over_char ];
	//rho`primes_over_char_abs := [ [u[1] : u in Factorization(Parent(1*Z_Labs)!P)] : P in primes_over_char ];
	rho`primes_over_char_abs := [[ideal<ZL_abs | [ZL_abs!u : u in Generators(v)]> : v in rho`primes_over_char_image[j]] : j in [1..#rho`primes_over_char]];


	// we'll need to do something with frobenius stuff to make sure we get the right representation 
	// for now we'll just pick the first one 
	rho`representation := Representation(irreds[1]);
	rho`traces := [Trace((rho`representation)(g)) : g in A];

	return rho;

end intrinsic;







intrinsic '@'(g::GrpPermElt,rho::ModPGalRep) -> AlgMatElt 
	{Evaluates rho at the group element g}

	require g in rho`domain: "g is not in the domain of rho";
	return rho`representation(g);

end intrinsic;





