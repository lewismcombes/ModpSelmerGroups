
// given a representation rep, returned by Aurel's galreps function,
// a prime P of ZLL (the ring of integers of L/K, entry 3 in rep), and an index i,
// returns the higher ramification group (lower numbered) of P of index i
HigherRamGroup:=function(rho,P,i)

  A:=Domain(rho[1]);

  ram_group:=[];
  B:=Basis(rho[3]);

  Q:=Factorization(Parent(1*rho[3])!P)[1,1];
  CC:=rho[4];

  for g in A do
    keep:=true;
    for j in [1..#B] do
      if not (rho[2](g)(B[j])-B[j])*CC[j] in Q^(i+1) then
        keep:=false;
        break j;
      end if;
    end for;
    if keep then
      Append(~ram_group,g);
    end if;
  end for;
  return sub<A|ram_group>;
end function;




// given a representation rho and a prime P of ZLL, returns the exponent of P in
// the Serre conductor of rho
SerreExponent:=function(rho,P)

  ram_groups:=[HigherRamGroup(rho,P,0)];
  i:=1;
  while #ram_groups[#ram_groups] ne 1 do
    Append(~ram_groups,HigherRamGroup(rho,P,i));
    i+:=1;
  end while;

  ind:=0;
  for R in ram_groups do
    Kers:=[];
    for r in R do
      m:=rho[1](r);
      S:=Kernel(m-m^0);
      Append(~Kers,S);
    end for;
    d:=Dimension(&meet Kers); // dimension of the space they all fix
    ind+:=#R/#ram_groups[1]*(2-d);
  end for;

  return Integers()!ind;
end function;



SerreConductor:=function(rho)

  K:=BaseField(NumberField(rho[3]));
  ZK:=MaximalOrder(K);
  p:=Characteristic(Codomain(rho[1]));
  primes_over_char:=[u[1] : u in Factorization(p*ZK)];

  ZLLdisc:=Discriminant(rho[3]);

  cond:=1*ZK;

  for P in Factorization(ZLLdisc) do
    if &and [Valuation(P[1],u) eq 0 : u in primes_over_char] then // excludes primes over the characteristic
      cond*:=P[1]^SerreExponent(rho,P[1]);
    end if;
  end for;

  return cond,Factorization(cond);
end function;



//
