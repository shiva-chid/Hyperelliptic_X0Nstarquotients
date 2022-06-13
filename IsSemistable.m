function HasSemistableReduction(C, p)
  Cp := BaseChange(C, Bang(Rationals(), GF(p)));
  //return forall {pt : pt in SingularPoints(Cp) | IsDoublePoint(Cp, pt) and IsOrdinarySingularity(Cp, pt)};
  return forall {pt : pt in SingularPoints(Cp) | IsNode(Cp, pt)};
end function;

function IsRegularModel(C,f,p)
  Cp := BaseChange(C, Bang(Integers(), GF(p)));
  for ptFp in SingularPoints(Cp) do
    // does the constant term have p-adic valuation 1?
    if Valuation(Evaluate(f, [Integers()!ptFp[1], Integers()!ptFp[2]]), p) ne 1 then
      return false;
    end if;
  end for;
  return true;
end function;

for N in [133,177,205,213,221,287,299] do
  print N;

  X := SimplifiedModel(X0NQuotient(N, [p^Valuation(N,p) : p in PrimeDivisors(N)]));
  A2Q<x,y> := AffineSpace(Rationals(), 2);
  f, h := HyperellipticPolynomials(X);
  assert h eq 0;
  C := Curve(A2Q, y^2 - Evaluate(f, x));

  assert forall {p : p in PrimeDivisors(N) | HasSemistableReduction(C, p)};

  PxyZ<x,y> := PolynomialRing(Integers(), 2);
  A2Z<X,Y> := AffineSpace(PxyZ);
  f := y^2 - Evaluate(ChangeRing(f, Integers()), x);
  C := Scheme(A2Z, f);

  assert forall{p : p in PrimeDivisors(N) | IsRegularModel(C,f,p)};
end for;