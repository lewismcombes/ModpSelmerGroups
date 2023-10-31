
SEL:= recformat <
  NSF               : SeqEnum,
  ACT               : SeqEnum,
  AUT               : GrpPerm,
  transfer          : Map,
  group_list        : SeqEnum,
  p                 : RngIntElt,
  L                 : FldNum,
  K                 : FldNum,
  A                 : FldAb,
  mm                : Map,
  rad               : SeqEnum,
  traces            : SeqEnum,
  rep               : Tup
  >;

ChangeDirectory("/mnt/data/smp19lmc_code/galois_reps/selmer_utility");
load "NormalSubfields_K.m";
load "CFT_utility.m";
load "nearly_ordinary.m";
load "NO_selmer_lines.m";
load "get_rep.m";



// for polynomial f over Q defining a number field L, with L/K the image of a
// mod p Galois representation, returns the ranks of the relaxed,
// nearly-ordinary & unramified Selmer groups

// Ramification allows one to supply the ramifying primes of rho ahead of time, which can speed
// up MaximalOrder computations.
// SelVerbose makes the Selmer computation print more to the terminal about what it's doing.
// SelRamQuo makes the Selmer computation also supply the images of the inertia group in F_p*
// under the quotient rho*: G_K \to V/l. The order of the lists matches the order of the lines,
// allowing one to identify which nearly-ordinary Selmer groups correspond to unramified quotients.
// USeGRH allows one to specify whether to use class group bounds predicted by the general Riemann hypothesis,
// which often speeds up the computation.
SelRanks:=function(f,p,K : Ramification:=[], SelVerbose:=false, SelRamQuo:=false, UseGRH:=true)

  _<x>:=PolynomialRing(Integers());

  ZK:=MaximalOrder(K);

  L:=NumberField(f);

  assert IsSubfield(K,L);
  // L is the field such that Gal(L/K) = Im(rho)
  if #Ramification eq 0 then
    ZL:=MaximalOrder(L);
  else
    ZL:=MaximalOrder(L : Ramification:=Ramification cat PrimeFactors(Discriminant(K)));
  end if;


  // the next few blocks compute the right modulus for our ray class computation
  D:=Decomposition(ZL,p);

  // this should be the structure of V as an abelain group
  G:=AbelianGroup(ElementaryAbelianGroup(GrpGPC,p,2));

  // we also need the primes in L over individual primes in K
  // that lie over p. when K = Q this should be a list with one
  // sub-list, etc
  facK:=Factorization(p*ZK);
  radL:=[[PP[1] : PP in ff] : ff in [Factorization(Parent(1*ZL)!u[1]) : u in facK]];

  n:=#G;
  v := Valuation(n,p);

  ee:=Max([u[2] : u in Factorization(p*ZL)]);
  // this is the exponent we will need
  max_exp:=Ceiling(ee*v + ee/(p-1)+1);
  I:=(&*[&*u : u in radL])^max_exp;

  if UseGRH then
    SetClassGroupBounds("GRH");
  end if;


  // when max_exp is big this can take a long time.
  time R, m :=RayClassGroup(I,[1..#RealPlaces(L)]);

  // here is our maximal (Z/p)^n field, which contains all the elements of our Selmer group
  mm:=MaxlPExt(R,m,p);
  A:=AbelianExtension(mm);


  time NSF,ACT,AUT,transfer:=NormalSubfields_K(A,Invariants(G),K);
  print #NSF, "subfields to check";

  // tells us what action each element of NSF encodes
  group_stats,group_list:=ProfileNSF(ACT,p);
  if SelVerbose then
    group_stats;
  end if;


  // we need to choose a particular instance of the representation
  // so that we can spot it in extensions
  reps:=galreps(RelativeField(K,L),K,p);
  ranks:=[];
  rams:=[];
  for rho in reps do
    tt,ff:=IsIsomorphic(AUT,Domain(rho[1]));
    // we precompose rho here for compatibility reasons---sometimes rho itself will not
    // recognise AUT as its domain, but a group isomorphic to it.
    rep:=<ff*rho[1],ff*rho[2],rho[3],rho[4]>;
    traces:=[Trace(rep[1](Domain(rep[1]).i)) : i in [1..Ngens(AUT)]];

    // packages all of the info into one easy-to-use source
    // we will be messing around with the condition over p, so
    // SelNoP is literally "Selmer with no condition on p"
    SelNoP:=rec<SEL | NSF:=NSF,
                      ACT:=ACT,
                      AUT:=AUT,
                      transfer:=transfer,
                      group_list:=group_list,
                      p:=p,
                      L:=L,
                      K:=K,
                      A:=A,
                      mm:=mm,
                      rad:=radL,
                      traces:=traces,
                      rep:=rep
                >;

    if SelRamQuo then
      RR,ram:=REL_NO_UR(SelNoP : Verbose:=SelVerbose, Fast:=true, RamQuo:=SelRamQuo);
      Append(~rams,ram);
    else
      RR:=REL_NO_UR(SelNoP : Verbose:=SelVerbose, Fast:=true, RamQuo:=SelRamQuo);
    end if;
    Append(~ranks,RR);
    frob_traces:=ComputeFrob(ZL,K,rho, 50);
    print "Ranks:";
    print RR;
    print "Traces of Frobenius:";
    print frob_traces;
  end for;

  return RR,rams;
end function;












//
