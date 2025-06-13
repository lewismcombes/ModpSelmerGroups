

import "SelmerUtility.m" : SelmerModulus, MaximalPExtensionHom, IsConjugateToAction;
import "NormalSubfields_K.m": NormalSubfields_K, GetAction;




declare type ModPSelData;

declare attributes ModPSelData:
	base_rep, modulus, real_inf, maximal_p_extension, NSF, act, aut, normal_subfields, normal_subfields_actions, normal_subfields_domain, 
	normal_subfields_transfer, normal_subfields_conjugators, normal_subfields_inertia_fixed;



intrinsic Print(S::ModPSelData)
	{}

	str := "Selmer data associated to " cat Sprint(S`base_rep);
	printf str;

end intrinsic;



intrinsic SelmerData(rho::ModPGalRep) -> ModPSelData
	{The Selmer data associated to a representation rho}

	sel := New(ModPSelData);
	sel`base_rep := rho;

	modulus := SelmerModulus(rho);
	sel`modulus := modulus;

	real_inf := [1..#RealPlaces(rho`image_field_abs)];
	sel`real_inf := real_inf;
	R, m := RayClassGroup(modulus,real_inf);
	mm := MaximalPExtensionHom(R, m, rho`char);
	AA := RayClassField(mm);

	// we try to bring the modulus down, to save time on future calculations inside the ray class field 
	cond := Conductor(AA);
	R, m := RayClassGroup(cond, real_inf);
	A := RayClassField(MaximalPExtensionHom(R, m, rho`char));

	sel`maximal_p_extension := A;
	NSF, act, aut, transfer := NormalSubfields_K(A, [rho`char : i in [1..rho`finite_field_degree * rho`dim]], rho`base_field);

	assert aut eq rho`domain;

	// we want to compare information from rho`domain and aut, but since they're not always 
	// literally the same group, we need an isomorphism between them 
	_, isom := IsIsomorphic(rho`domain,aut);
	aut_elts := [g : g in aut];
	perm := [Index(aut_elts,isom(h)) : h in rho`domain];
	
	// we want to keep only those extensions upon which Gal(L/K) acts via rho 
	NSF_keep := [];
	act_keep := [];
	NSF_conj := [];
	for i in [1..#NSF] do 
		aa:=[act[i][perm[j]] : j in [1..#perm]];
		tt, g := IsConjugateToAction(rho,aa);
		if tt then 
			Append(~NSF_keep, NSF[i]);
			Append(~act_keep, aa);
			Append(~NSF_conj, g);
		end if;
	end for;


	sel`normal_subfields := NSF_keep;
	sel`normal_subfields_actions := act_keep;
	sel`normal_subfields_domain := aut;
	sel`normal_subfields_transfer := transfer;
	sel`normal_subfields_conjugators := NSF_conj;

	// FIX 
	sel`NSF := NSF;
	sel`act := act;
	sel`aut := aut;

	return sel;
end intrinsic;

