_<x> := PolynomialRing(Rationals());
levelN := 136;
C := X0NQuotient(levelN, [p^Valuation(levelN,p) : p in PrimeDivisors(levelN)]);
J := Jacobian(C);
RankBounds(J); //0
#Points(ChangeRing(C,GF(3))); //4
#Points(SimplifiedModel(C) : Bound:=1000); //4

/////////////////////////////////////////

levelN := 207;
C := X0NQuotient(levelN, [p^Valuation(levelN,p) : p in PrimeDivisors(levelN)]);
C := SimplifiedModel(C); 
#Points(C : Bound:=1000); //4
F<x,y> := FunctionField(C);
//A[3](GenericPoint(C));
A := Automorphisms(C);
phi := iso<C ->C | [1/x,y/x^4,1],[1/x,y/x^4,1]>;
G:= AutomorphismGroup(C,[phi]);
E,m := CurveQuotient(G);
#TorsionSubgroup(Jacobian(E)); //2
RankBounds(Jacobian(E)); //0 0

////////////////////////////////////////////
levelN := 252;
C := X0NQuotient(levelN, [p^Valuation(levelN,p) : p in PrimeDivisors(levelN)]);
C := SimplifiedModel(C); 
#Points(C : Bound:=1000); //4
F<x,y> := FunctionField(C);
A := Automorphisms(C);
A[3](GenericPoint(C));
phi := iso<C ->C | [(x + 1)/(x - 1), 4*y/(x-1)^4,1],[(x + 1)/(x - 1), 4*y/(x-1)^4,1]>;
G:= AutomorphismGroup(C,[phi]);
E,m := CurveQuotient(G);
#TorsionSubgroup(Jacobian(E)); //4
RankBounds(Jacobian(E)); //0 0
assert #Points(E : Bound:=100) eq #TorsionSubgroup(Jacobian(E)); 

RatPoints := [];
for k in [1..#Points(E: Bound:=100)] do
    R := RationalPoints(Difference(Pullback(m,Points(E: Bound:=1000)[k]), BaseScheme(m)));
    S:=IndexedSetToSequence(R);
    RatPoints := RatPoints cat S;
end for;

#RatPoints; //4

////////////////////////////////////////////////////
levelN := 315;
C := X0NQuotient(levelN, [p^Valuation(levelN,p) : p in PrimeDivisors(levelN)]);
C := SimplifiedModel(C); 
#Points(C : Bound:=1000); //4
F<x,y> := FunctionField(C);
//A[3](GenericPoint(C));
A := Automorphisms(C);
phi := iso<C ->C | [1/x,y/x^4,1],[1/x,y/x^4,1]>;
G:= AutomorphismGroup(C,[phi]);
E,m := CurveQuotient(G);
RatPoints := [];
for k in [1..#Points(E: Bound:=100)] do
    R := RationalPoints(Difference(Pullback(m,Points(E: Bound:=1000)[k]), BaseScheme(m)));
    S:=IndexedSetToSequence(R);
    RatPoints := RatPoints cat S;
end for;

#RatPoints; //4

////////////////////////////////////////////////////
_<x> := PolynomialRing(Rationals());
levelN := 176;
C := X0NQuotient(levelN, [p^Valuation(levelN,p) : p in PrimeDivisors(levelN)]);
C := SimplifiedModel(C);
f,_:=HyperellipticPolynomials(C);
f1 := x*(x^3 - 2*x^2 + 2);
f2 := (x^3 - 4*x + 4)*(x^3 + 2*x^2 - 2);
assert f eq f1*f2;
Factorization(Integers()!Resultant(f1,f2)); //2^12
Y1 := HyperellipticCurve(f2);
Ym2 := HyperellipticCurve(-2*f2);

Ym1 := HyperellipticCurve(-f2);
Y2 := HyperellipticCurve(2*f2);

RankBound(Jacobian(Y1));  //1
RankBound(Jacobian(Ym2)); //1

J1 := Jacobian(Y1);
Jm2 := Jacobian(Ym2);

Chabauty(Points(J1 : Bound:=100)[2]); //{ (1 : 1 : 1), (-3 : 11 : 1), (1 : -1 : 0), (1 : 1 : 0), (1 : -1 : 1), (-3 : -11: 1) }
Chabauty(Points(Jm2 : Bound:=100)[2]);//{ (-2 : -4 : 1), (0 : 4 : 1), (2 : -44 : 3), (-2 : 4 : 1), (2 : 44 : 3), (0 : -4: 1) }

RankBound(Jacobian(Ym1)); //0 
RankBound(Jacobian(Y2)); //0

Chabauty0(Jacobian(Ym1)); //{@ @}
Chabauty0(Jacobian(Y2)); //{@ @}

//x in {1,-3,-2,0,2/3}
IsSquare(Evaluate(f,1));
IsSquare(Evaluate(f,-3));
IsSquare(Evaluate(f,-2));
IsSquare(Evaluate(f,0));
IsSquare(Evaluate(f,2/3));