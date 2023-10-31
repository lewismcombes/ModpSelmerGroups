
//turns a vector to a group element, pretty straightforward
// in particular it is compatible with the rest of the functions here
VecToGroup:=function(vec,grp)
  elt:=Id(grp);
  for i in [1..Ncols(vec)] do
    elt+:=Integers()!vec[i]*grp.i;
  end for;
  return elt;
end function;



CreateHom := function(G, GG, mp)
  // h := hom<G -> GG | mp>;  // does not work ...
  // mp is a list of pairs. We want to constuct the map
  // that sends mp[i][1] -> mp[i][2].

  m1 := Matrix(Integers(), [Eltseq(x[1]) : x in mp]);
  m1 := VerticalJoin(m1, DiagonalMatrix([ Order(G.x) : x in [1..Ngens(G)]]));
  _, t := EchelonForm(m1);
  m1 := Matrix(Integers(), [Eltseq(x[2]) : x in mp]);
  t := Matrix(Integers(), [ Eltseq(t[i])[1..#mp] : i in [1..Nrows(t)]]);
  m1 := t*m1;
  mp := [ GG!Eltseq(m1[i]) : i in [1..Ngens(G)]];
  h := hom<G -> GG | mp>;
  return h;
end function;



InducedMap_K:=function(r1,r2,h,Coprime)

  pp := NextPrime(100);
  li := [ ];
  lg := [ ];
  G := Domain(r1);
  H := Domain(r2);
  o := Ring(Codomain(r1));
  /*   // this goes here but I don't think we need it
       // since #G = #H always, for our purposes, I think
       // maybe should leave it in anyway? it can't hurt right??  -L
  if Gcd(#G, #H) eq 1 then
    return hom<G -> H | [ H.0 : i in [1..Ngens(G)]]>;
  end if;
  */

  HEval:=function(h,I) // a bodge function that apparently needs to exist  -L
    gens:=Generators(I);
    R:=Order(I);
    h_gens:=[h(g) : g in Generators(I)];
    h_ideal:=ideal<R | h_gens>;
    return h_ideal;
  end function;



    repeat
      repeat
        pp := NextPrime(pp);
      until Gcd(pp, Coprime) eq 1;
      lp := Decomposition(o, pp);
      for i in lp do
        if Degree(i[1]) gt 1 and Norm(i[1]) gt 1000 then
          continue;
        end if;
        Append(~lg, i[1] @@ r1);
        Append(~li, HEval(h,i[1]) @@ r2); //changed here  -L
      end for;
    until sub<G|lg> eq G;


  return CreateHom(G, H, [<lg[i], li[i]> : i in [1..#lg]]);
end function;








//CohomologyModule_K

function convert_K(elt, Mk, M, mo)
    X := Domain(M);
    Z := Domain(Mk);
    phi := Mk(elt);
    aut := InducedMap_K(M,M, phi, mo);
    return Matrix([Eltseq(aut(X.i)) : i in [1..Ngens(X)]]);
    // use InducedAut here!!! XXX and do it in C
end function;


// InducedAutomorphism(M,phi,mo)  = InducedMap(M,M,phi,mo)


CohomologyModule_K:=function(F,Sub,K)

k := BaseField(F);
g, _, p := AutomorphismGroup(k,K);

if Sub cmpne false then // not sure what this is doing but it came with the intrinsic so ¯\_(ツ)_/¯  -L
  g := Sub;
end if;


  A, mo := NormGroup(F);
  mo := AbsoluteNorm(mo);
  AA := InvariantRepresentation(Domain(A));
  mAA := Coercion(AA, Domain(A));

  inv := AbelianInvariants(AA);
  mats := [ convert_K(g.i, p, mAA*A, mo) : i in [1..Ngens(g)]];



    C := CohomologyModule(g, inv, mats);
    Zm := RSpace(Integers(), Ngens(AA));
    mp := map<Zm -> AA | x :-> AA!Eltseq(x), y:-> Zm!Eltseq(y)>;
    // p maps the automorphisms group of k onto automorphisms
    // mAA*AA maps between the ideal group of F and the same group
    //      in Smith form (as used in Cohomology module)
    // mp maps between the RSpace from C to the ideal group.


    return C, p, mAA*A, mp;
end function;



GalMatsQuo:=function(Q,S,GalMats) // given GalMats acting on Q and a subgroup S, find the action on the space Q/S

  Mats:=[];
  Q1,down:=quo<Q|S>;
  up:=Inverse(down);
  p:=Exponent(Q);

  for gg in GalMats do
    N:=Ngens(Q1);
    vecs:=[down(VecToGroup(ChangeRing(Vector(ElementToSequence(up(Q1.i))),GF(p))*gg,Q)) : i in [1..N]];
    Append(~Mats,Matrix(GF(p),N,N,[ElementToSequence(v) : v in vecs]));
  end for;

  return Mats;
end function;




NormalSubfields_K:=function(A,Quot,K)
  All:=true;
  Over:=false; //not sure about this! could be a problem. documentation doesn't say what these do  -L
  N := NormGroup(A);

  /*
  if Quot cmpeq false then
    l := Subgroups(Domain(N));
  else
    l := Subgroups(Domain(N):Quot := Quot);
  end if;
  */
  print "finding Aut(L/K)...";
  g, _, mg := AutomorphismGroup(BaseField(A),K); // this is Gal(L/K)
  /*
  if Over cmpne false then
    require not All : "All cannot be given together with Over";
    g := sub<g|[x @@ mg : x in Over]>;
    q1, q2, q3, q4 := CohomologyModule_K(A : Sub := g); // not sure here either! but maybe this is never seen due to All and Over  -L
  else
  */
  print "creating cohomology module (using class group data)...";
    q1, q2, q3, q4 := CohomologyModule_K(A,false,K);
  //end if;
  // we SHOULD be able to map (coerce) between Domain(N) and Domain(q3)
  // they should be the same group, but possibly differnt bases.
  // Point is, that q3 has the action already computed...


  // this part gives us the action of Gal(L/K) on the ray class group Q
  // this is stored in the GalMats list -L
  Q:=Domain(N);
  p:=Exponent(Q);
  G := Group(q1);
  a := [Q.i : i in [1..Ngens(Q)]];
  ChangeUniverse(~a, Domain(N));
  ChangeUniverse(~a, Domain(q3));
  b := [ChangeUniverse([ActionOnVector(q1, x@@q4, G.i)@q4 : x in a],Domain(N)) : i in [1..Ngens(G)]];
  GalMats:=[Matrix(GF(p),[ElementToSequence(e) : e in u]) : u in b];

  QInv:=Invariants(Q);
  print "finding submodules of chosen size...";
  GM:=GModule(g,MatrixAlgebra<GF(p),#QInv|GalMats>); // makes the Gal(L/K) module explicitly
  LL:=Submodules(GM);

  // we want all those submodules which leave Quot as the quotient
  // this particular method works for (Z/pZ)^n extensions
  // it will NOT work in general
  // but of course something similar could -L
  k:=#QInv - #Quot;

  keeps:=[];
  for u in LL do
    if Dimension(u) eq k then
      Append(~keeps,u);
    end if;
  end for;

  gens:=[];
  for u in keeps do
    Append(~gens,[VecToGroup(GM!u.i,Q) : i in [1..k]]);
  end for;

  subgroups:=[];
  for u in gens do
    Append(~subgroups,sub<Q|u>);
  end for;


  l := [AbelianSubfield(A, x:IsNormal, Over := Over) : x in subgroups];
  actions:=[GalMatsQuo(Q,s,GalMats) : s in subgroups];
  return l,actions,g,mg,gens;
end function;







/* this just fetches the action of G(L/K) on G(M/L). It returns
1) G(L/K) as a group of permutations
2) the action of these permutations on G(M/L) as matrices
3) and also as permutations
These latter permutations
*/

GetAction:=function(F,K)

k := BaseField(F);
g, _, p := AutomorphismGroup(k,K);


  A, mo := NormGroup(F);
  mo := AbsoluteNorm(mo);
  AA := InvariantRepresentation(Domain(A));
  mAA := Coercion(AA, Domain(A));

  Autos:=[];
  Mats:=[];

  for i in [1..#g] do
     Append(~Autos,InducedMap_K(mAA*A,mAA*A, p(g.i), mo));
     Append(~Mats,convert_K(g.i, p, mAA*A, mo));
  end for;

  return <g,Mats,Autos>;
end function;





//
