

// given a list of numbers [a_1,a_2,...,a_n], returns the list of all
// [u_1,u_2,...,u_n] such that 1 =< u_i =< a_i
LineCombos:=function(list)

  if #list eq 1 then
    return [[i] : i in [1..list[1]]];
  else
    combos:=[];
    prev:=$$(list[2..#list]);
    for u in prev do

      for i in [1..list[1]] do
        Append(~combos,[i] cat u);
      end for;
    end for;
    return combos;
  end if;
end function;


//
// takes the number N of lines, and the degree q of F_q
// and returns the rank
//
NumToRank:=function(N,q)
  qr:=(q-1)*N+1;
  b:=Floor(Log(q,qr));
  B:=Ceiling(Log(q,qr));
  if (q^b-1)/(q-1) eq N then
    return b;
  elif (q^B-1)/(q-1) eq N then
    return B;
  else
    print "bad number of lines " cat Sprint(N);
    return -N;
  end if;
end function;


// Takes a vector representating a line in V, and returns the
// subfield of M corresponding to M^V, i.e. the elements fixed by V
// currently only doing this for F_p reps, i.e. V = F_p + F_p
VecToSubfield:=function(M,vec)
  GM:=Domain(NormGroup(M)); // Gal(M/L)
  Z:=Integers();
  return AbelianSubfield(M,sub<GM|Z!(vec[1])*GM.1 + Z!(vec[2])*GM.2>);
end function;


// given two ideals I and J, returns the automorphisms that send
// I to J
IdentifyAutFromIdeals:=function(I,J,rep)
  auts:=[];
  G:=Domain(rep[1]);
  for i in [1..Ngens(G)] do
    if AutIdeal(rep[2](G.i),I) eq J then
      Append(~auts,G.i);
    end if;
  end for;
  return auts;
end function;



PrimeTranslate:=function(P,Q,rep)
  G:=Domain(rep[1]);
  gs:=[];
  for i in [1..Ngens(G)] do
    if AutIdeal(rep[2](G.i),P) eq Q then
      Append(~gs,G.i);
    end if;
  end for;
  return gs;
end function;


// given a line L fixed by a prime P, and another prime Q, finds an element g of
// the galois group such that the line g*L is fixed by Q. this is all wrt the action
// of rep. the line L is represented by its canonical generator from the nearly_ordinary
// code package. returns g and the vector v representing L in canonical form
LineTranslate:=function(L,P,Q,rep)

  G:=Domain(rep[1]);
  p:=Minimum(P);
  PL,r:=ProjLineFp(p);

  g:=-1;
  v:=-1;

  for i in [1..Ngens(G)] do
    if AutIdeal(rep[2](G.i),P) eq Q then
      g:=G.i;
      v:=r(L*rep[1](G.i));
      break i;
    end if;
  end for;
  return g,v;
end function;


// given one of our galois rep objects and the primes over its characteristic in L,
// returns the equivalence classes of its lines under the action of Gal(L/K).
// the order of the lines matches the order of the primes in the list given
// so if you pass rad (the radical) it should all line up nicely
FixedLineOrbits:=function(rep,rad)

  t,VP:=IsNearlyOrdinaryP(rep,rad[1]);
  orbits:=[];

  if t then
    for L in VP do
      new_orbit:=[];
      for Q in rad do
        g,v:=LineTranslate(L,rad[1],Q,rep);
        Append(~new_orbit,v);
      end for;
      Append(~orbits,new_orbit);
    end for;
  end if;

  return orbits;
end function;


// if rep1 and rep2 are conjugate and have the same domain, returns the
// element of G by which they are conjugate. if they aren't, returns "bad"
// this should never happen when used in REL_NO_UR.
ConjReps:=function(rep1,rep2)

  G:=Domain(rep1[1]);
  p:=Characteristic(Codomain(rep1[1]));

  act1:=[rep1[1](G.i) : i in [1..Ngens(G)]];
  act2:=[rep2[1](G.i) : i in [1..Ngens(G)]];

  V:=GL(2,p);

  for h in V do
    if [h^-1*u*h : u in act1] eq act2 then
      return h;
    end if;
  end for;

  print "something went wrong with conjugation";
  return "bad";
end function;



// returns the ranks of the relaxed, nearly-ordinary and unramified Selmer groups
REL_NO_UR:=function(S : Verbose:=false, Fast:=true, RamQuo:=false)

  PL,r:=ProjLineFp(S`p);

  // we collect the fixed lines over each prime over p
  fixed_lines:=[];
  for r in S`rad do
    tt,ll:=IsNearlyOrdinaryP(S`rep,r[1]);
    Append(~fixed_lines,ll);
  end for;

  unr_lines:=0;

  // this big list collates all the information about which inertia groups lie
  // in which lines, which we then pass to a function that checks all the combos
  AllFields_AllLines:=[];

  for i in [1..#S`NSF] do

    tr:=[Trace(u) : u in S`ACT[i]];
    M:=S`NSF[i];

    // we only keep the extensions with the right traces
    // this means the representation of Gal(L/K) on Gal(M/L)
    // is conjugate to S`rep
    if S`traces eq tr then

      M_Inertia:=[];

      // collects all the fixed fields of inertia for comparison
      for r in S`rad do
        PP:=r[1];
        N, m, minf := NormGroup(S`A);
        Mur := RayClassField(m/PP^Valuation(m,PP), minf);
        MI:=Mur meet M;
        Append(~M_Inertia,MI);
      end for;

      // while we have the inertia groups, we do the checks for the unramified
      // Selmer group too
      is_unr:=true;
      for u in M_Inertia do
        if not Degree(u) eq Degree(M) then
          is_unr:=false;
          break u;
        end if;
      end for;

      if is_unr then
        unr_lines+:=1;
      end if;

      // we need to see how a given fixed line behaves inside Gal(M/L) \simeq V
      // so we figure out this isomorphism and translate the line accordingly
      repM:=<Representation(GModule(S`AUT,S`ACT[i])),S`rep[2]>;
      h:=ConjReps(S`rep,repM);

      LineForP:=[];

      for j in [1..#S`rad] do

        ll_conj:=[r(u*h) : u in fixed_lines[j]];

        LineInInertia:=[];

        // if the subfield of M fixed by the line u is inside the fixed field of inertia,
        // the inertia group is in the line
        for u in ll_conj do
          Append(~LineInInertia,VecToSubfield(M,u) subset M_Inertia[j]);
        end for;
        Append(~LineForP,LineInInertia);
      end for;
      Append(~AllFields_AllLines,LineForP);
    end if;

  end for;

  // finally we go over AllFields_AllLines and collect the Selmer stats
  // we check all possible combination of fixed lines over each prime
  LineNums:=LineCombos([#u : u in AllFields_AllLines[1]]);

  if Verbose then
    print "Number of fixed line combinations to check:", #LineNums;
  end if;

  NO_lines:=[];

  for u in LineNums do
    lines:=0;

    for R in AllFields_AllLines do
      contained:=[];
      for i in [1..#u] do
        Append(~contained,R[i][u[i]]);
      end for;
      if &and contained then
        lines+:=1;
      end if;
    end for;
    Append(~NO_lines,lines);
  end for;

  if Verbose then
    print "Fixed line inclusions for each " cat Sprint(GroupName(S`AUT)) cat " field:";
    AllFields_AllLines;
    "";
  end if;

  if RamQuo then
    // we compute the image of the inertia group of L/K at p
    // in the quotient V / l, where l is a fixed line
    chars:=[];
    for j in [1..#fixed_lines] do
      II:=InertiaGroup(S`rad[j][1]);
      new_list:=[];
      R:=RSpace(GF(S`p),2);
      for l in fixed_lines[j] do
        QQ,d:=quo<R|l>;
        Append(~new_list,[d(Inverse(d)(QQ.1)*S`rep[1](u))[1] : u in II]);
      end for;
      Append(~chars,new_list);
    end for;
    return [*NumToRank(#AllFields_AllLines,S`p),[NumToRank(u,S`p) : u in NO_lines],NumToRank(unr_lines,S`p)*],chars;
  else
    return [*NumToRank(#AllFields_AllLines,S`p),[NumToRank(u,S`p) : u in NO_lines],NumToRank(unr_lines,S`p)*];
  end if;

end function;




//
