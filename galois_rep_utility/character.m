
// assuming we already have the representation rho, the frobenius data
// from aurel's code, its conductor cond,
// and the characteristic p of the representation

RepChar:=function(rho,frob,cond,p)

  ZK:=Order(cond);

  DG1:=DirichletGroup(cond);
  DG2:=DirichletGroup(p*ZK);

  E1:=Elements(DG1);
  E2:=Elements(DG2);

  // we find the order of the determinant character
  // when the rep lives in some non-prime finite field
  frob_order:=1;
  frob_dets:=[u[3] : u in frob];
  frob_test:=[u^1 : u in frob_dets];
  while not &and [u eq 1 : u in frob_test] do
    frob_order+:=1;
    frob_test:=[u^frob_order : u in frob_test];
  end while;

  possible_chars:=[];
  // now we run over all the characters in both, looking
  // for d1 and d2 such that their product gives the determinant
  // character. then d1 is the character of the rep as predicted by Serre
  for d1 in E1 do
    for d2 in E2 do
      if LCM(Order(d1),Order(d2)) eq frob_order then
        test:=[d1(u[1])*d2(u[1]) : u in frob];
        kk:=Rationals();
        for u in test do
          par:=Parent(u);
          if Type(par) ne RngInt then
            kk:=Compositum(kk,Parent(u));
          end if;
        end for;
        Zkk:=MaximalOrder(kk);
        pp:=Factorization(p*Zkk)[1,1];
        ff,down:=ResidueClassField(pp);
        if [down(u) : u in test] eq frob_dets then
          Append(~possible_chars,<d1,Index(E1,d1)>);
        end if;

      end if;
    end for;
  end for;

  if #possible_chars eq 1 then
    return possible_chars[1][1], possible_chars[1][2];
  elif #possible_chars eq 0 then
    print "no character found";
    return -1;
  else
    print "multiple possible characters found";
    print "more determinants of frobenius needed to disambiguate";
    return possible_chars;
  end if;

end function;


//
