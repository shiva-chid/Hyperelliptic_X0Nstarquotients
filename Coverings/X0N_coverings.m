SetDebugOnError(true);
Attach("X0Nwq.m");

SetVerbose("ModularCurveModel", 3);

N := 133;
X0N, wqsmat, bas := XZeroN(N);
number_of_terms := #Eltseq(bas[1]) - 2;
wqsmat := wqsmat;
printf "Computing the quotient X_0(N)/W(N) ...\n";
g := Dimension(AmbientSpace(X0N)) + 1;
printf "g = %o\n", g;
V := VectorSpace(Rationals(), g);
I := One(Parent(wqsmat[1])); // identity matrix
// compute basis of V such that all wqsmat are diagonal
wqsmatnew, A := Diagonalization(wqsmat);
//print wqsmatnew;
assert wqsmatnew[1] eq A * wqsmat[1] * A^-1;
// find fixed space
fixed_vectors := [i : i in [1..g] | forall{wq : wq in wqsmatnew | wq[i,i] eq 1}];
inverted_vectors := [i : i in [1..g] | exists{wq : wq in wqsmatnew | wq[i,i] eq -1}];
P<[x]> := AmbientSpace(X0N);
aut := map< X0N -> P | [&+[A[i,j] * x[j] : j in [1..g]] : i in [1..g]] >;
autinv := map< X0N -> P | [&+[B[i,j] * x[j] : j in [1..g]] : i in [1..g]] > where B := A^-1;
autP := map< P -> P | [&+[A[i,j] * x[j] : j in [1..g]] : i in [1..g]] >;
autPinv := map< P -> P | [&+[B[i,j] * x[j] : j in [1..g]] : i in [1..g]] > where B := A^-1;

// assume X_0(N)/W'(N) is hyperelliptic
basnew := [&+[A[i,j] * bas[j] : j in [1..g]] : i in [1..g]]; // new basis of S_2(Gamma_0(N)) such that the w_q are diagonal
basnew_fixed := [basnew[i] : i in fixed_vectors];
gquot := #fixed_vectors;
assert gquot eq 2;
X0N_WN, xq, yq := HyperellipticModularCurve(basnew_fixed, gquot);


Points(X0N_WN : Bound := 10^5);  
coords := [&+[A[i,j] * x[j] : j in [1..g]] : i in [1..g]];  
// transformed coordinates
coords_fixed := [coords[i] : i in fixed_vectors];  
// these are the two linear forms whose quotient gives the map to P¹
coords_fixed;  
S1 := Scheme(X0N, coords_fixed[1]); // x = oo
time Dimension(S1);  
time Degree(S1);  
time irrS1 := IrreducibleComponents(S1);  
#irrS1;  
[<Degree(c), Degree(ReducedSubscheme(c))> : c in irrS1];  
S2 := Scheme(X0N, coords_fixed[2]);
time Dimension(S2);  
time Degree(S2);  
time irrS2 := IrreducibleComponents(S2);  
[<Degree(c), Degree(ReducedSubscheme(c))> : c in irrS2];  
S0 := S1 meet S2; // the base scheme of the morphism
Degree(S0);  
S1a := Complement(S1, S0); // Difference is better !  
// Complement subtracts as often as possible, but here part of the
// fiber we want is contained in the base locus. See later.
Degree(S1a);  
S2a := Complement(S2, S0);
Degree(S2a);  
[<Degree(c), Degree(ReducedSubscheme(c))> : c in IrreducibleComponents(S1a)];
[<Degree(c), Degree(ReducedSubscheme(c))> : c in IrreducibleComponents(S2a)];
S3 := Scheme(X0N, coords_fixed[1]-coords_fixed[2]);
S0 subset S3;  
S3a := Complement(S3, S0);
Degree(S3a);  
[<Degree(c), Degree(ReducedSubscheme(c))> : c in IrreducibleComponents(S3a)];
S4 := Scheme(X0N, 5*coords_fixed[1]-3*coords_fixed[2]);   
S0 subset S4;   
S4a := Complement(S4, S0);   
Degree(S4a);   
[<Degree(c), Degree(ReducedSubscheme(c))> : c in IrreducibleComponents(S4a)];
[<Degree(c), Degree(ReducedSubscheme(c))> : c in IrreducibleComponents(S0)];
irrS1a := IrreducibleComponents(S1a);
MinimalBasis(irrS1a[1]);  
_<u> := PolynomialRing(Rationals());
Evaluate($1[#$1], [0,0,0,0,0,0,0,0,0,u,1]);  
Discriminant(Integers(NumberField($1)));  
K := NumberField(u^2+u+1);
Points(irrS1a[1], K);  
pt1 := $1[1];
Vector(Eltseq(pt1))*Transpose(ChangeRing(wqsmat[1],K));  
X0N(K)!Eltseq($1);  
Vector(Eltseq(pt1))*Transpose(ChangeRing(wqsmat[2],K));  
X0N(K)!Eltseq($1);  
Points(irrS1a[2], K);  
// get four distinct points.
// look at the other fiber:
S1aa := Difference(S1, S0); // Difference instead of Complement
Degree(S1aa);  
irrS1aa := IrreducibleComponents(S1aa);
[<Degree(c), Degree(ReducedSubscheme(c))> : c in irrS1aa];   
// the first component is new
MinimalBasis(ReducedSubscheme(irrS1aa[1]));  
Evaluate($1[#$1], [0,0,0,0,0,0,0,0,0,u,1]);  
Discriminant(Integers(NumberField($1)));  
K1 := NumberField(u^2 + 19);
Points(irrS1aa[1], K1);  
pt1a := $1[1];
Vector(Eltseq(pt1a))*Transpose(ChangeRing(wqsmat[1],K1));  
X0N(K1)!Eltseq($1);  
Vector(Eltseq(pt1a))*Transpose(ChangeRing(wqsmat[2],K1));  
X0N(K1)!Eltseq($1);  
$1 eq pt1a;  
// same point --> fixed under the second Atkin-Lehner op.
Points(S2a); // the rational points on X_0(N)  

//// METHOD 1

Pg<[y]> := PolynomialRing(Rationals(), g - #fixed_vectors);
mons2 := MonomialsOfDegree(Pg, 2);
// monomials mon2 invariant under all wq
mons2invariant := [mon2 : mon2 in mons2 | forall{wq : wq in wqsmatnew | 
                    Evaluate(mon2, [wq[i,i] * x[i] : i in inverted_vectors]) eq Evaluate(mon2, [x[i] : i in inverted_vectors])}];

Pnew<[z]> := ProjectiveSpace(Rationals(), [2 : i in [1..#mons2invariant]] cat [1 : i in [1..#fixed_vectors]]);
quot := map< P -> Pnew | [Evaluate(mon2, [x[i] : i in inverted_vectors]) : mon2 in mons2invariant] cat [x[i] : i in fixed_vectors] >;
X := Image(aut * quot);
printf "Computed X_0(N)/W'(N).\n";
printf "It has genus %o.\n", Genus(X);
flag, isom := IsIsomorphic(X, X0N_WN);
assert flag;
quot2 := quot * isom;

ptsX2 := RationalPoints(X0N_WN : Bound := 1000);
printf "Computing the preimages of the %o rational points ...\n", #ptsX2;
for P in ptsX2 do
    printf "Computing the preimage of %o: ", P;
    fiberP := ReducedSubscheme(P@@quot2);
    ptsfiberP := RationalPoints(fiberP);
    ptsfiberPinX0N := [autPinv(p) : p in ptsfiberP | autPinv(p) in X0N];
    printf "%o (# = %o)\n", ptsfiberPinX0N, #ptsfiberPinX0N;
end for;