SetLogFile("jinvs.log" : Overwrite := true);
// SetLogFile("jinvs.log");

function find_eqn(x,y);
    listofcoeffs := [];
    coefs, n, d := Coefficients(y^2);
    Append(~listofcoeffs,coefs);
    n;
    for i := 6 to 1 by -1 do
    	coefs, nn, dd := Coefficients(-x^i);
    	Append(~listofcoeffs, [0 : j in [n..nn-1]] cat coefs);
    	nn;
    end for;
    minlen := Minimum([#x : x in listofcoeffs]);
    minlen;
    Append(~listofcoeffs, [0 : j in [n..-1]] cat [-1] cat [0 : j in [1..minlen]]);
    listofcoeffs;
    M := Matrix(Rationals(),#listofcoeffs,minlen,[coeffs[1..minlen] : coeffs in listofcoeffs]);
    kerM := Kernel(M);
    assert Dimension(kerM) eq 1;
    v := kerM.1;
    v := v/v[1];
    assert v[2] eq 1;
    return Eltseq(v)[3..#listofcoeffs];
end function;

function f3(as,x,y);
    a0 := as[1];
    a1 := as[2];
    a2 := as[3];
    a3 := as[4];
    a4 := as[5];
    a5 := as[6];
    return (8*a3-4*a4*a5+a5^3)/32 + (4*a4-a5^2)/16*x + a5/4*x^2 + x^3/2 + y/2;
end function;

function f4(as,x,y);
    a0 := as[1];
    a1 := as[2];
    a2 := as[3];
    a3 := as[4];
    a4 := as[5];
    a5 := as[6];
    return (64*a2-16*a4^2-32*a3*a5+24*a4*a5^2-5*a5^4)/256 + x*f3(as,x,y);
end function;

function f5(as,x,y);
    a0 := as[1];
    a1 := as[2];
    a2 := as[3];
    a3 := as[4];
    a4 := as[5];
    a5 := as[6];
    return (128*a1-64*a3*a4-64*a2*a5+48*a4^2*a5+48*a3*a5^2-40*a4*a5^3+7*a5^5)/512 + x*f4(as,x,y);
end function;

function express(Ji, f3, f4, f5);
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
//	print f3tothem, nn, dd;
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
    assert IsSquarefree(N);
    primefacsN := PrimeFactors(N);
    omegaN := #primefacsN;
    facsN := Divisors(N);
    sigma1N := &+facsN;
    prec := 3*sigma1N div 2;
    
    L<q> := LaurentSeriesRing(Rationals(),prec);
    j := jInvariant(q);
    jtranslates := [Evaluate(j,q^M) : M in facsN];
    Ptemp := PolynomialRing(Rationals(),#facsN);
    Js := [Evaluate(ElementarySymmetricPolynomial(Ptemp,k),jtranslates) : k in [1..#facsN]];
    
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
    
    ff3 := f3(as,x,y);
    ff4 := f4(as,x,y);
    ff5 := f5(as,x,y);
    Js_intermsof_ffs := [express(Ji,ff3,ff4,ff5) : Ji in Js];
    
    P<t> := PolynomialRing(Rationals());
    polsofjinvs := [];
    // -infty point
    p := t^#facsN + &+[(-1)^i*Js_intermsof_ffs[i,1]*t^(#facsN-i) : i in [1..#facsN]];
    Append(~polsofjinvs,p);
    
    // affine rational points
    for affpt in smallratpts_affineY do
        ff3_at_affpt := f3(as,affpt[1],affpt[2]);
        ff4_at_affpt := f4(as,affpt[1],affpt[2]);
        ff5_at_affpt := f5(as,affpt[1],affpt[2]);
        Js_at_affpt := [&+[Ji[k]*(ff3_at_affpt)^((k-1) div 3)*((k mod 3 eq 1) select 1 else (k mod 3 eq 2) select ff4_at_affpt else ff5_at_affpt): k in [1..#Ji]] : Ji in Js_intermsof_ffs];
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
		pp_optimized := Polredabs(pp[1]);
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
/*
		gens := [];
		allnewsquares := [1];
		if IsSquare(K ! -1) then
		    Append(~gens,-1);
		    Append(~allnewsquares,-1);
		end if;
		a := 2;
		while #gens lt m do
		    b := Squarefree(a);
		    if not b in allnewsquares then
			if IsSquare(K ! b) then
			    Append(~gens,b);
			    if #gens eq m then
//				print gens;
				break;
			    end if;
			    newsquares := [Squarefree(os*b) : os in allnewsquares];
			    allnewsquares := allnewsquares cat newsquares;
			end if;
		    end if;
		    if not -b in allnewsquares then
			if IsSquare(K ! -b) then
			    Append(~gens,-b);
			    if #gens eq m then
//				print gens;
				break;
			    end if;
			    newsquares := [Squarefree(-os*b) : os in allnewsquares];
			    allnewsquares := allnewsquares cat newsquares;
			end if;
		    end if;
		    a := a+1;
		end while;
*/
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
            	    	newsquares := [Squarefree(os*b) : os in allnewsquares];
            	    	allnewsquares := allnewsquares cat newsquares;
            	    end if;
            	    if not -b in allnewsquares and IsSquare(K ! -b) then
            	    	Append(~gens,-b);
			if #gens eq m then
//			    print gens;
			    break;
			end if;
            	    	newsquares := [Squarefree(-os*b) : os in allnewsquares];
            	    	allnewsquares := allnewsquares cat newsquares;
            	    end if;
            	end for;
                        
            	L := SplittingField([t^2-g : g in gens]);
            	/*
            	if not IsIsomorphic(K,L) then
            	    print Index(Facsp,pp), pp;
            	    print Index(polsofjinvs,p), p;
            	    break p;
            	end if;
            	*/
            	assert IsIsomorphic(K,L);
            	Append(~jfields_sub,gens);
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
// Ns := [255,266,287,299,330];
for N in Ns do
    pts, polsofjs, factorized_polsofjs, Qj, hascm, cmdiscs := jinvs(N);
    printf "The rational points on X_0(%o) besides the cusp at %o are:\n%o\n", N, <0,Infinity()>, pts;
    printf "Q(j) is a multi-quadratic extension obtained by taking square roots of \n%o \n", Qj;
    printf "The j-invariants are roots of: \n%o \n", factorized_polsofjs;
    printf "Do the Q-curves have CM or not? \n%o \nIf yes, the discriminant of the CM order (listed as 0 if no CM): \n%o \n", hascm, cmdiscs;
    printf "##############################################################\n";
end for;


