
// acts on an ideal by an automorphism
AutIdeal:=function(aut,ideal)
  gens:=Generators(ideal);
  R:=Ring(Parent(ideal));
  return ideal<R | [aut(g) : g in gens]>;
end function;


// computes decomp group
DecompGroup:=function(rep,P)
  G:=Domain(rep[1]);
  decomp:=[];
  gens:=SetToSequence(Generators(G));
  for g in gens do
    if AutIdeal(rep[2](g),P) eq P then
      Append(~decomp,g);
    end if;
  end for;
  return sub<G|decomp>;
end function;


// creates the projective line over F_p^2, which is maybe projective space?
// returns lines (a,b) with a,b in GF(p) covering all such possible lines in projective
// space, and a function r that recognises a line (c,d) in its "canonical" form
ProjLineFp:=function(p)
  F:=GF(p);
  line:=[];
  for i in [0..p-1] do
    Append(~line,Vector([F!1,F!i]));
  end for;
  Append(~line,Vector([F!0,F!1]));

  r:=function(v)
    if v[1] eq 0 then
      return Vector([F!0,F!1]),1/F!v[2];
    else
      return Vector([1,v[2]/F!v[1]]),1/F!v[1];
    end if;
  end function;

  return line,r;
end function;


// computes the action of a matrix on the projective line PL
ProjActionV:=function(mat,PL,r)
  p:=Characteristic(CoefficientRing(mat));
  M:=ZeroMatrix(GF(p),p+1);
  for i in [1..p+1] do
    ind:=Index(PL,r(PL[i]*mat));
    M[i,ind]:=1;
  end for;
  return M;
end function;

// for rep a rep, D the decomposition group under consideration, PL and r coming
// from ProjActionV, computes the lines in F_p^2 fixed by all elements of D
FixedLines:=function(rep,D,PL,r)

  spaces:=[Kernel(ProjActionV(rep[1](D.i),PL,r)-1) : i in [0..Ngens(D)]];

  S:=&meet spaces;
  lines:=[];

  F:=CoefficientRing(PL[1]);
  p:=Characteristic(F);

  vz:=Vector([F!0 : i in [1..p+1]]);
  for i in [1..p+1] do
    v:=vz;
    v[i]:=1;
    if v in S then
      Append(~lines,PL[i]);
    end if;
  end for;
  return lines;
end function;



// ZL ring of integers of extension, P a prime ideal of ZL
// tells you if rho|D_P fixes any 1 dim'l spaces, and what the spaces are if it does
IsNearlyOrdinaryP:=function(rep,P)

  D:=DecompGroup(rep,P);
  p:=Characteristic(Codomain(rep[1]));
  PL,r:=ProjLineFp(p);
  lines:=FixedLines(rep,D,PL,r);
  if #lines ne 0 then
    return true,lines;
  else
    return false,[];
  end if;
end function;


// tells you if the mod p rep is nearly ordinary at all places over p
// does a bunch of redundant stuff, we only need to check one prime per
// ideal of K over p, since Galois action shuffles the fixed lines around
// also returns the fixed lines
IsNearlyOrdinary:=function(ZL,rep)
  p:=Characteristic(Codomain(rep[1]));
  fac:=[f[1] : f in Factorization(p*ZL)];
  nearly_ord:=true;
  ss:=0;
  for P in fac do
    t,ss:=IsNearlyOrdinaryP(rep,P);
    if not t then
      nearly_ord:=false;
      break P;
    end if;
  end for;
  return nearly_ord,ss;
end function;





//
