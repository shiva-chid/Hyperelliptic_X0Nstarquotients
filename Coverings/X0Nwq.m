declare verbose ModularCurveModel, 3;

intrinsic XZeroN(N::RngIntElt) -> Sch, SeqEnum, SeqEnum
{ Computes the canonical model of X_0(N) if it is non-hyperelliptic and for each p^d || N the Atkin-Lehner involution w_(p^d).}
  S := CuspForms(N);
  g := Dimension(S);
  number_of_terms := 50;
  repeat
    number_of_terms := Round(number_of_terms * Sqrt(2));
    vprintf ModularCurveModel, 2: "Computing q-expansion basis of cusp forms of level %o of dimension %o with %o terms.\n", N, g, number_of_terms;
    bas := qExpansionBasis(S, number_of_terms); // #bas = g
    // determine equations for canonical model in P^{g-1}
    Pg1<[z]> := PolynomialRing(Rationals(), g); // z[i] = bas[i]
    // intersection of quadrics
    vprintf ModularCurveModel, 2: "Finding equation of model as intersection of quadrics.\n";
    mons2 := MonomialsOfDegree(Pg1, 2);
    mat := Matrix([[Coefficient(m, j) : j in [2..number_of_terms]] where m := Evaluate(mm, bas) : mm in mons2]);
    kermat := KernelMatrix(mat);
    vprintf ModularCurveModel, 3: "Kernel matrix has %o rows and %o columns.\n", Nrows(kermat), Ncols(kermat);
    equations := [&+[kermat[i,j]*mons2[j] : j in [1..#mons2]] : i in [1..Nrows(kermat)]];
    Pws<q> := Universe(bas);
    X0N_Scheme := Scheme(ProjectiveSpace(Pg1), equations);
  until Dimension(X0N_Scheme) eq 1;
  vprintf ModularCurveModel, 1: "Found model of X_0(%o).\n", N;
  X0N := Curve(X0N_Scheme);

  wqs := [];
  wqsmat := [];
  for p in PrimeDivisors(N) do
    q := p^Valuation(N,p);
  //for q in Divisors(N) do
  //  if Gcd(q, N div q) ne 1 or q in {1,N} then continue; end if;
    vprintf ModularCurveModel, 2: "Computing w_%o.\n", q;

    wq := AtkinLehnerOperator(S, q);
    Append(~wqsmat, wq);
    //wqinv := wq^-1;
    //assert wq eq wqinv; // remove this, wq is an involution
    assert {Nrows(wq), Ncols(wq)} eq {g};
    //wq_aut := iso<X0N -> X0N | [&+[wq[i][j] * z[j] : j in [1..g]] : i in [1..g]],
    //                           [&+[wq[i][j] * z[j] : j in [1..g]] : i in [1..g]] >; // wq is self-inverse
    //Append(~wqs, wq_aut);
  end for;
  vprintf ModularCurveModel, 1: "Computed all wq's.\n";
  //assert Genus(X0N) eq g;
  //return X0N, wqs, wqsmat;
  return X0N, wqsmat, bas;
end intrinsic;

intrinsic HyperellipticModularCurve(bas::SeqEnum, g::RngIntElt) -> CrvHyp
{ Compute a model of the modular curve X_0(N) over Q.}
  number_of_terms := #Eltseq(bas[1]) - 2;
  // compute x, y in terms of f_1, f_2
  xq := bas[2]/bas[1]; // x(q) = f_2(q)/f_1(q)
  xq := Universe(bas)!xq;
  yq := Parent(xq)!(Parent(xq).1*Derivative(xq)/bas[1]); // y(q) = q x'(q)/f_1(q)
  // find a hyperelliptic equation of degree 2g + 2
  mat := Matrix([[Coefficient(xn, j) : j in [0..number_of_terms]] where xn := xq^n : n in [0..2*g+2]]);
  P<x> := PolynomialRing(Rationals());
  f1 := P!Eltseq(Solution(mat, Vector([Coefficient(y2, j) : j in [0..number_of_terms]]) where y2 := yq^2));
  C := HyperellipticCurve(f1);
  assert Genus(C) eq g;
  return C, xq, yq;
end intrinsic;

/*
intrinsic HMCurve(bas::SeqEnum, g::RngIntElt) -> CrvHyp
{ Compute a model of the modular curve X_0(N) over Q.}
  number_of_terms := #Eltseq(bas[1]) - 2;
  // compute x, y in terms of f_1, f_2
  xq := bas[1]/bas[2]; // x(q) = f_1(q)/f_2(q)
  yq := Parent(xq)!(Parent(xq).1*Derivative(xq)/bas[2]); // y(q) = q x'(q)/f_2(q)
  // find a hyperelliptic equation of degree 2g + 2
  mat := Matrix([[Coefficient(xn, j) : j in [-(2*g+2)..number_of_terms-(2*g+2)]] where xn := xq^n : n in [0..2*g+2]]);
  P<x> := PolynomialRing(Rationals());
  f1 := P!Eltseq(Solution(mat, Vector([Coefficient(y2, j) : j in [-(2*g+2)..number_of_terms-(2*g+2)]]) where y2 := yq^2));
  C := HyperellipticCurve(f1);
  assert Genus(C) eq g;
  return C, xq, yq;
end intrinsic;
*/