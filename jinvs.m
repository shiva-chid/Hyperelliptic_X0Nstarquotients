// ####################################################
/*
The main function in this file jinvs() requires calling pari gp's polredbest(). We do this
using CHIMP, which can be installed from
https://github.com/edgarcosta/CHIMP

For level 330, jinvs(330) involves calling polredbest() for a deg 16 polynomial with very
big coefficients, which results in a "Pari stack overflows !" error.
To avoid this, modify line 19 in CHIMP/endomorphisms/endomorphisms/magma/polredabs.m
from
s := Pipe("gp -q -D timer=0", cmd);
to
s := Pipe("gp -q -D timer=0 parisizemax=1G", cmd);
*/
// ####################################################

SetLogFile("jinvs.log" : Overwrite := true);
// SetLogFile("jinvs.log");

function fs(as,x,y);
/*
functions f3, f4, f5 on hyperelliptic curve y^2 = x^6 + a5*x^5 + a4*x^4 + a3*x^3 + a2*x^2 + a1*x + a0
such that div(fi) + i*P_0 >= 0, where P_0 is the point at +infty. Further if P1 is the point at -infty,
then fi(P1) = 0 for each i.
Thus, the Riemann-Roch spaces with no poles outside P_0 are:
L(P_0) = L(2*P_0) = 1
L(3*P_0) = <1,f3>
L(4*P_0) = <1,f3,f4>
L(5*P_0) = <1,f3,f4,f5>
L(6*P_0) = <1,f3,f4,f5,f3^2>
L(7*P_0) = <1,f3,f4,f5,f3^2,f3*f4>
L(8*P_0) = <1,f3,f4,f5,f2^2,f3*f4,f3*f5>
and so on.
*/
    a0 := as[1];
    a1 := as[2];
    a2 := as[3];
    a3 := as[4];
    a4 := as[5];
    a5 := as[6];
    f3 := (8*a3-4*a4*a5+a5^3)/32 + (4*a4-a5^2)/16*x + a5/4*x^2 + x^3/2 + y/2;
    f4 := (64*a2-16*a4^2-32*a3*a5+24*a4*a5^2-5*a5^4)/256 + x*f3;
    f5 := (128*a1-64*a3*a4-64*a2*a5+48*a4^2*a5+48*a3*a5^2-40*a4*a5^3+7*a5^5)/512 + x*f4;
    return [f3,f4,f5];
end function;

function express(Ji,fs);
/*
Write the function Ji as a rational linear combination of products of the functions
f3, f4, f5, where fs = [f3, f4, f5]
To be precise, we express Ji with respect to the basis
1, f3, f4, f5, f3^2, f3*f4, f3*f5, f3^3, ...
of the Riemann-Roch space L(d*P_0) where
d is the order of the pole of the function Ji at the point at +infty P_0.
*/
    f3 := fs[1];
    f4 := fs[2];
    f5 := fs[3];
    coefsJi, n, d := Coefficients(Ji);
    m := -n div 3;
    i := -n mod 3;
    listofcoefs := [coefsJi];
    for j := 0 to m-1 do
	if j eq 0 then
	    Append(~listofcoefs, [0 : k in [n..-1]] cat [1] cat [0 : k in [1..100]]);
	else
	    f3tothej, nn, dd := Coefficients(f3^j);
	    Append(~listofcoefs, [0 : k in [n..nn-1]] cat f3tothej);
	end if;
	f3tothejf4, nn, dd := Coefficients(f3^j*f4);
	Append(~listofcoefs, [0 : k in [n..nn-1]] cat f3tothejf4);
	f3tothejf5, nn, dd := Coefficients(f3^j*f5);
	Append(~listofcoefs, [0 : k in [n..nn-1]] cat f3tothejf5);
    end for;
    if i ge 0 then
	f3tothem, nn, dd := Coefficients(f3^m);
	Append(~listofcoefs, [0 : k in [n..nn-1]] cat f3tothem);
    end if;
    if i ge 1 then
	f3tothemf4, nn, dd := Coefficients(f3^m*f4);
	Append(~listofcoefs, [0 : k in [n..nn-1]] cat f3tothemf4);
    end if;
    if i ge 2 then
	f3tothemf5, nn, dd := Coefficients(f3^m*f5);
	Append(~listofcoefs, [0 : k in [n..nn-1]] cat f3tothemf5);
    end if;
//    print #listofcoefs, -n+10;
    M := Matrix(Rationals(),#listofcoefs,-n+10,[coefs[1..(-n+10)] : coefs in listofcoefs]);
    VM := Kernel(M);
//    print VM;
//    print Dimension(VM) eq 1;
    normalized_rel := Eltseq((VM.1)/(VM.1)[1]);
    return [-normalized_rel[i] : i in [2..#normalized_rel]];
end function;

function jinvs(N);
/*
For each rational point on X_0(N)^* of height <= 1000
1. Finds the (minimal polynomials of the) j-invariants of the collection of associated Q-curves.
2. Describes the multi-quadratic extension Q(j) explicitly by finding small a_1, a_2,...,a_{omega(N)}
such that Q(j) = Q(\sqrt{a_i} : 1 <= i <= omega(N)). Note omega(N) denotes the number of distinct
prime factors of N.
3. Determines if the Q-curves have CM, and computes the discriminant of the CM orders if they do.
*/
    assert IsSquarefree(N);
    primefacsN := PrimeFactors(N);
    omegaN := #primefacsN;
    facsN := Divisors(N);
    sigma1N := &+facsN;
    prec := 3*sigma1N div 2;
    
    L<q> := LaurentSeriesRing(Rationals(),prec);
    j := jInvariant(q);
    jscales := [Evaluate(j,q^M) : M in facsN];
    P2 := PolynomialRing(Rationals(),#facsN);
    Js := [Evaluate(ElementarySymmetricPolynomial(P2,k),jscales) : k in [1..#facsN]];
    
    S := CuspForms(N,2);
    Tps := [AtkinLehnerOperator(S,p) : p in primefacsN];
    fixed_vecs := &meet[Kernel(Tp - Identity(Parent(Tp))) : Tp in Tps];
    assert Dimension(fixed_vecs) eq 2;
    assert Eltseq(fixed_vecs.1)[1..2] eq [1,0];
    assert Eltseq(fixed_vecs.2)[1..2] eq [0,1];
    h1 := &+[(fixed_vecs.1)[i]*S.i : i in [1..Dimension(S)]];
    assert qExpansion(h1,3) eq q + O(q^3);
    h1 := qExpansion(h1,prec);
    h2 := &+[(fixed_vecs.2)[i]*S.i : i in [1..Dimension(S)]];
    assert qExpansion(h2,3) eq q^2 + O(q^3);
    h2 := qExpansion(h2,prec);
    x := h1/h2;
    y := -q*Derivative(x)/h2;
/*
    as := find_eqn(x,y);
*/
    X, m := X0NQuotient(N,primefacsN);
    Y := Domain(m);
    smallratpts_Y := Points(Y : Bound := 1000);
    smallratpts_affineY := [<pt[1]/pt[3],pt[2]/pt[3]^3> : pt in smallratpts_Y | pt[3] ne 0];
    f, h := HyperellipticPolynomials(Y);
    assert h eq 0;
    as := Coefficients(f);
    assert #as eq 7 and as[7] eq 1;
    as := as[1..6];
    
    ffs := fs(as,x,y);
    Js_intermsof_ffs := [express(Ji,ffs) : Ji in Js];
    
    P<t> := PolynomialRing(Rationals());
    polsofjinvs := [];
    // -infty point (1:-1:0)
    p := t^#facsN + &+[(-1)^i*Js_intermsof_ffs[i,1]*t^(#facsN-i) : i in [1..#facsN]];
    Append(~polsofjinvs,p);
    
    // affine rational points
    for affpt in smallratpts_affineY do
        ffs_at_affpt := fs(as,affpt[1],affpt[2]);
        Js_at_affpt := [&+[Ji[k]*(ffs_at_affpt[1])^((k-1) div 3)*((k mod 3 eq 1) select 1 else (k mod 3 eq 2) select ffs_at_affpt[2] else ffs_at_affpt[3]): k in [1..#Ji]] : Ji in Js_intermsof_ffs];
        p := t^#facsN + &+[(-1)^i*Js_at_affpt[i]*t^(#facsN-i) : i in [1..#facsN]];
        Append(~polsofjinvs,p);
    end for;
    
    factorized_polsofjinvs := [];
    jfields := [];
    hascm := [];
    for p in polsofjinvs do
        Facsp := Factorisation(p);
        Append(~factorized_polsofjinvs,Facsp);
        jfields_sub := [];
        hascm_sub := [];
        for pp in Facsp do
            if Degree(pp[1]) gt 1 then
		pp_optimized := Polredabs(pp[1] : Best := true);
		K := NumberField(pp_optimized);
		j1 := Roots(pp[1],K)[1,1];
//            	K<j1> := NumberField(pp[1]);
            else
            	K := RationalField();
            	j1 := Roots(pp[1])[1,1];
            end if;
            m := Valuation(Degree(pp[1]),2);
            if m eq 0 then
            	Append(~jfields_sub,[]);
            else
		dK := Discriminant(pp_optimized);
            	ramified_ps := SetToSequence(Set(PrimeFactors(Numerator(dK))) join Set(PrimeFactors(Denominator(dK))));
//		print ramified_ps;
            	gens := [];
            	allnewsquares := [1];
            	V := VectorSpace(GF(2),#ramified_ps);
            	for v in V do
            	    a := &*[(v[i] eq 1) select ramified_ps[i] else 1 : i in [1..Dimension(V)]];
            	    b := Squarefree(a);
            	    if not b in allnewsquares and IsSquare(K ! b) then
            	    	Append(~gens,b);
			if #gens eq m then
//			    print gens;
			    break;
			end if;
            	    	allnewsquares := allnewsquares cat [Squarefree(os*b) : os in allnewsquares];
            	    end if;
            	    if not -b in allnewsquares and IsSquare(K ! -b) then
            	    	Append(~gens,-b);
			if #gens eq m then
//			    print gens;
			    break;
			end if;
            	    	allnewsquares := allnewsquares cat [Squarefree(-os*b) : os in allnewsquares];
            	    end if;
            	end for;
                        
            	L := SplittingField([t^2-g : g in gens]);
		try
		    assert IsIsomorphic(K,L);
		    Append(~jfields_sub,gens);
		catch e
		    printf "Error: The minimal polynomial %o for the j-invariant of a Q-curve associated to the point %o does not define a multi-quadratic number field", pp[1], (Index(polsofjinvs,p) eq 1) select -Infinity() else smallratpts_affineY[Index(polsofjinvs,p)-1];
		end try;
            end if;
            E := EllipticCurveFromjInvariant(j1);
            bool, D := HasComplexMultiplication(E);
            Append(~hascm_sub,bool);
        end for;
        Append(~jfields,jfields_sub);
        Append(~hascm,hascm_sub);
    end for;

    cmdiscs := [];
    for i := 1 to #hascm do
        cmdiscs_sub := [];
        for j := 1 to #hascm[i] do
            if hascm[i,j] then
            	pp := factorized_polsofjinvs[i,j,1];
            	if Degree(pp) gt 1 then
            	    K<j1> := NumberField(pp);
            	else
            	    K := RationalField();
            	    j1 := Roots(pp)[1,1];
            	end if;
            	E := EllipticCurveFromjInvariant(j1);
            	bool, D := HasComplexMultiplication(E);
            	Append(~cmdiscs_sub,D);
            else
            	Append(~cmdiscs_sub,0);
            end if;
    	end for;
    	Append(~cmdiscs,cmdiscs_sub);
    end for;
    
    return [<0,-Infinity()>] cat smallratpts_affineY, polsofjinvs, factorized_polsofjinvs, jfields, hascm, cmdiscs;
end function;

// Ns := [133,134,146,166,177,205,206,213,221,255,266,287,299,330];
Ns := [133,134,146,166,177,205,206,213,221,255,266,287,299];
for N in Ns do
    pts, polsofjs, factorized_polsofjs, Qj, hascm, cmdiscs := jinvs(N);
    printf "The rational points on X_0(%o) besides the cusp at %o are:\n%o\n", N, <0,Infinity()>, pts;
    printf "Q(j) is a multi-quadratic extension obtained by taking square roots of \n%o \n", Qj;
    printf "The j-invariants are roots of: \n%o \n", factorized_polsofjs;
    printf "Do the Q-curves have CM or not? \n%o \nIf yes, the discriminant of the CM order (listed as 0 if no CM): \n%o \n", hascm, cmdiscs;
    printf "##############################################################\n";
end for;


