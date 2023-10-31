
// code originally written by Aurel Page, later adapted by Lewis Combes 

function isfaithful(rho)
  G := Domain(rho);
  MR := Codomain(rho);
  for g in G do
    if g ne G!1 and rho(g) eq MR!1 then
      return false;
    end if;
  end for;
  return true;
end function;



function ffss2dreps(G,q) //faithful semisimple
   F<w>:=GF(q);
  Lirr := IrreducibleModules(G,F);
  if IsAbelian(G) then
    Ldim1 := [M : M in Lirr | Dimension(M) eq 1];
    Ldim2 := [Representation(M) : M in Lirr | Dimension(M) eq 2];
    Lreps := [Representation(DirectSum(Ldim1[i],Ldim1[j])) : j in [i..#Ldim1], i in [1..#Ldim1]];
    Lreps cat:= Ldim2;
  else
    Lreps := [Representation(M) : M in Lirr | Dimension(M) eq 2];
  end if;
  Lreps := [rho : rho in Lreps | isfaithful(rho)];
  return Lreps;
end function;



function galreps(F,K,q)
  //print "computing automorphism group";
  G,_,f := AutomorphismGroup(F,K);
  if #G ne AbsoluteDegree(F) div AbsoluteDegree(K) then
    print "not Galois, early abort";
    return [];
  end if;
  //print "computing representations";
  L := ffss2dreps(G,q);
  //print "found", #L, "representations";
  return [<rho,f> : rho in L];
end function;



function isfrob(basisZL,aut,N,proj)
  for x in basisZL do
    if proj(x)^N ne proj(aut(x)) then
      return false;
    end if;
  end for;
  return true;
end function;



function frobenius(ZL,f,pr) // f: G -> Aut_K(L)
  G := Domain(f);
  a,b := TwoElement(pr);
  facto := Factorization(ideal<ZL|ZL!a,ZL!b>);
  PR := facto[1,1];
  if facto[1,2] ne 1 then
    return 0; //ramified!
  end if;
  N := Norm(pr);
  Q,proj := ResidueClassField(PR);
  basis:=Basis(ZL);
  for g in G do  //could be improved
    aut := f(g);
    if isfrob(basis,aut,N,proj) then
      return g;
    end if;
  end for;
  print "should not be reached!";
  return 0;
end function;



function frobmatrix(ZL,galrep,pr)
  rho := galrep[1];
  f := galrep[2];
  g := frobenius(ZL,f,pr);
  return rho(g);
end function;


detect_hnf:=function(J,M)
      N:=Norm(J);
      a:=M[1,1];  d:=M[1,2];
	  b:=M[2,1];  c:=M[2,2];
	  if (d eq 0) and (N eq a*c) and (b in [0..a-1]) then
	     return 1;
	  else
         return 0;
      end if;
end function;

HNF_basis:=function(J)
    N:=Norm(J);
    M:=BasisMatrix(J);
    if Ncols(M) eq 2 then
  	  Mt:=Matrix(Integers(),2,2,[M[1,2],M[1,1],M[2,2],M[2,1]]);
      HN:=HermiteForm(Mt);
  	  H:=Matrix(Integers(),2,2,[HN[2,2],HN[2,1],HN[1,2],HN[1,1]]);
        c:=H[2,2];  b:=H[2,1];   a:=H[1,1];
  	  if c lt 0 then
  	     c:=-c;   b:=-b;
  	  end if;

  	  b:=(b mod a);
  	  assert 1 eq detect_hnf(J,Matrix(Integers(),2,2,[a,0,b,c]));
  	  return [Norm(J), b,c];
    else
      return [M[1]];
    end if;
end function;


ComputeTraces:=function(ZL,K,rho, max)
    PP:=[J : J in IdealsUpTo(max,K) | IsPrime(J) and GCD(J,Discriminant(ZL)) eq 1*MaximalOrder(K)];
    HNF:=[HNF_basis(J): J in PP];
    ParallelSort(~HNF,~PP);
    traces:=[* *];
    for i in [1..#PP] do
       J:=PP[i];
       t,g:=IsPrincipal(J);
       M:=frobmatrix(ZL,rho,J);
       Append(~traces,<g, Order(M), Trace(M)>);
       //print "done ideal:",i;
   end for;
   return traces;
end function;
