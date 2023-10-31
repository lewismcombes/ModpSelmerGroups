// QOL function, gives the version of Q(sqrt(-d)) such that the basis of
// K is a Z-basis of ZK
QuadFld:=function(d)

    _<x>:=PolynomialRing(Integers());
  if d in [1,2] then
    return NumberField(x^2+d);
  elif d in [3,7,11] then
    return NumberField(x^2-x-Integers()!((-d-1)/4));
  else
    return "d = " cat Sprint(d) cat " currently not supported";
  end if;
end function;



// returns the map mm: R2 -> {ideals of ZL} that cuts out the p subext
// of RayClassField(m). so RayClassField(mm) should give a group (Z/p)^n
MaxlPExt:=function(R,m,p)

  h:=hom< R-> R | [p*R.i : i in [1..Ngens(R)]]>;
  Q,mq:=quo<R | Image(h) >;

  qm:=Inverse(mq);
  mm:=qm * m;

  return mm;
end function;



// takes the a list of actions and returns the stats on what groups the
// actions encode on the vector space (Z/p)^2
ProfileNSF:=function(ACT,p)

  group_stats:=[];
  group_list:=[];
  for u in ACT do
    H:=MatrixGroup<2,GF(p)|u>;
    name:=GroupName(H);
    names:=[g[1] : g in group_stats];
    if not name in names then
      Append(~group_stats,[*name,1*]);
    else
      group_stats[Index(names,name)][2]+:=1;
    end if;
    Append(~group_list,name);
  end for;

  return group_stats,group_list;
end function;





//
