SetLogFile("table_main.log" : Overwrite := true);

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
    js := [];
    for p in polsofjinvs do


        Facsp := Factorisation(p);
        Append(~factorized_polsofjinvs,Facsp);
        jfields_sub := [];
        hascm_sub := [];
        js_sub := [];

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
//		        print ramified_ps;

            	gens := [];
            	allnewsquares := [1];
            	V := VectorSpace(GF(2),#ramified_ps);
            	for v in V do
            	    a := &*[(v[i] eq 1) select ramified_ps[i] else 1 : i in [1..Dimension(V)]];
            	    b := Squarefree(a);
            	    if not b in allnewsquares and IsSquare(K ! b) then
            	    	Append(~gens,b);
                        if #gens eq m then
//			                print gens;
                            break;
                        end if;
            	    	allnewsquares := allnewsquares cat [Squarefree(os*b) : os in allnewsquares];
            	    end if;
            	    if not -b in allnewsquares and IsSquare(K ! -b) then
            	    	Append(~gens,-b);
                        if #gens eq m then
//			                print gens;
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

            if m eq 0 then
                Append(~js_sub,[j1]);
            elif m eq 1 then
                sqrtg := Roots(t^2-gens[1],K)[1,1];
                M := Matrix(Rationals(),3,2,[Eltseq(j1),Eltseq(K ! -1),Eltseq(K ! -sqrtg)]);
                temp := Kernel(M);
                assert Dimension(temp) eq 1;
                Append(~js_sub, Eltseq((temp.1)/(temp.1)[1])[2..3]);
            else
                Append(~js_sub,[]);
            end if;
        end for;
        Append(~jfields,jfields_sub);
        Append(~hascm,hascm_sub);
        Append(~js,js_sub);
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
                    j1 := Roots(pp)[1,1];
                end if;
                E := EllipticCurveFromjInvariant(j1);
                bool, D := HasComplexMultiplication(E);
                assert bool;
                Append(~cmdiscs_sub,D);
            else
                Append(~cmdiscs_sub,0);
            end if;
    	end for;
    	Append(~cmdiscs,cmdiscs_sub);
    end for;
    
    return [<0,-Infinity()>] cat smallratpts_affineY, polsofjinvs, factorized_polsofjinvs, jfields, js, hascm, cmdiscs;
end function;


//////////////////////////////////////////////////////////////////////////////////////////////////////////////
//   Function to factor a quadratic j-invariant by extracting "maximal" cubic factors and write in Latex    //
//////////////////////////////////////////////////////////////////////////////////////////////////////////////

function tex_factor_quadj(g,eltseqj);
    if g lt 0 then
        return "";
    end if;
    j_gcdofnums := GCD(Numerator(eltseqj[1]),Numerator(eltseqj[2]));
    j_cubicgcdofnums := &*[dd[1]^(dd[2] div 3) : dd in Factorisation(j_gcdofnums)];
    j_rem := [eltseqj[1]/j_cubicgcdofnums^3, eltseqj[2]/j_cubicgcdofnums^3];

    K := QuadraticField(g);
    OK := RingOfIntegers(K);
    jinv := K ! j_rem;
    jinvs_idealfacs := Factorisation(jinv*OK);
    maxcubic_ideal_fac := &*[fac[1]^(fac[2] div 3) : fac in jinvs_idealfacs];
    remaining_fac := &*[fac[1]^(fac[2] mod 3) : fac in jinvs_idealfacs];

    bool, elt := IsPrincipal(maxcubic_ideal_fac);
    assert bool;
    cubic_part := elt;

    bool, elt := IsPrincipal(remaining_fac);
    assert bool;
    remaining_part := elt;
    
    unit := jinv/(cubic_part^3*remaining_part);
    assert Norm(unit)^2 eq 1;
//    print [<cubic_part,3>,<remaining_part,1>];
    eps := FundamentalUnit(OK);
    for k := 0 to 50 do
    	if unit eq eps^k then
    	    unitpart := <eps,k>;
    	    break;
    	end if;
    	if unit eq eps^(-k) then
    	    unitpart := <eps^(-1),k>;
    	    break;
    	end if;
    	if unit eq -eps^k then
    	    unitpart := <eps,k>;
    	    remaining_part := -remaining_part;
    	    break;
    	end if;
    	if unit eq -eps^(-k) then
    	    unitpart := <eps^(-1),k>;
    	    remaining_part := -remaining_part;
    	    break;
    	end if;
    end for;
    cubic_part := cubic_part*(unitpart[1]^(unitpart[2] div 3));
    remaining_part := remaining_part*(unitpart[1]^(unitpart[2] mod 3));
    assert jinv eq cubic_part^3*remaining_part;

    Z := Integers();

    j_factored := [Eltseq(K ! cubic_part), Eltseq(K ! remaining_part)];
    cubepart := j_factored[1];
    lcmofdens_cubicpart := LCM([Denominator(x) : x in cubepart]);
    cubepart := [Z ! (Numerator(x)*lcmofdens_cubicpart/Denominator(x)) : x in cubepart];
    gcdofnums_cubepart := GCD(cubepart);
    j_cubicgcdofnums := j_cubicgcdofnums*gcdofnums_cubepart;
    cubepart := [x/gcdofnums_cubepart : x in cubepart];
    cancelfac := GCD(j_cubicgcdofnums,lcmofdens_cubicpart);
    j_cubicgcdofnums := j_cubicgcdofnums/cancelfac;
    lcmofdens_cubicpart := lcmofdens_cubicpart/cancelfac;

    noncubepart := j_factored[2];
    lcmofdens_noncubepart := LCM([Denominator(x) : x in noncubepart]);
    noncubepart := [Z ! (Numerator(x)*lcmofdens_noncubepart/Denominator(x)) : x in noncubepart];
    gcdofnums_noncubepart := GCD(noncubepart);
    noncubepart := [x/gcdofnums_noncubepart : x in noncubepart];
    cancelfac := GCD(gcdofnums_noncubepart,lcmofdens_noncubepart);
    integernum_noncubepart := gcdofnums_noncubepart/cancelfac;
    denominator_noncubepart := lcmofdens_noncubepart/cancelfac;
    if noncubepart[1] lt 0 and noncubepart[2] le 0 then
        integernum_noncubepart := -integernum_noncubepart;
        noncubepart := [-x : x in noncubepart];
    end if;
    if integernum_noncubepart lt 0 then
        integernum_noncubepart := -integernum_noncubepart;
        cubepart[1] := -cubepart[1];
        cubepart[2] := -cubepart[2];
    end if;
    if cubepart[2] gt 0 then
        sgn_irrationalpart_cubepart := " + ";
    elif cubepart[2] lt 0 then
        sgn_irrationalpart_cubepart := " - ";
        cubepart[2] := -cubepart[2];
    end if;

    if noncubepart[2] eq 0 then
        assert noncubepart eq [1,0];
        if denominator_noncubepart ne 1 then
            if lcmofdens_cubicpart ne 1 then
                output_string := Sprint(integernum_noncubepart) cat "(" cat Sprint(j_cubicgcdofnums) cat "(" cat Sprint(cubepart[1]) cat sgn_irrationalpart_cubepart cat Sprint(cubepart[2]) cat "\\sqrt{" cat Sprint(g) cat "})/" cat Sprint(lcmofdens_cubicpart) cat ")^3/" cat Sprint(denominator_noncubepart);
            else
                output_string := Sprint(integernum_noncubepart) cat "(" cat Sprint(j_cubicgcdofnums) cat "(" cat Sprint(cubepart[1]) cat sgn_irrationalpart_cubepart cat Sprint(cubepart[2]) cat "\\sqrt{" cat Sprint(g) cat "}))^3/" cat Sprint(denominator_noncubepart);
            end if;
        elif integernum_noncubepart ne 1 then
            if lcmofdens_cubicpart ne 1 then
                output_string := Sprint(integernum_noncubepart) cat "(" cat Sprint(j_cubicgcdofnums) cat "(" cat Sprint(cubepart[1]) cat sgn_irrationalpart_cubepart cat Sprint(cubepart[2]) cat "\\sqrt{" cat Sprint(g) cat "})/" cat Sprint(lcmofdens_cubicpart) cat ")^3";
            else
                output_string := Sprint(integernum_noncubepart) cat "(" cat Sprint(j_cubicgcdofnums) cat "(" cat Sprint(cubepart[1]) cat sgn_irrationalpart_cubepart cat Sprint(cubepart[2]) cat "\\sqrt{" cat Sprint(g) cat "}))^3";
            end if;
        else
            if lcmofdens_cubicpart ne 1 then
                output_string := "(" cat Sprint(j_cubicgcdofnums) cat "(" cat Sprint(cubepart[1]) cat sgn_irrationalpart_cubepart cat Sprint(cubepart[2]) cat "\\sqrt{" cat Sprint(g) cat "})/" cat Sprint(lcmofdens_cubicpart) cat ")^3";
            else
                output_string := "(" cat Sprint(j_cubicgcdofnums) cat "(" cat Sprint(cubepart[1]) cat sgn_irrationalpart_cubepart cat Sprint(cubepart[2]) cat "\\sqrt{" cat Sprint(g) cat "}))^3";
            end if;
        end if;
        return output_string;
    end if;
    if noncubepart[2] gt 0 then
        sgn_irrationalpart_rempart := " + ";
    elif noncubepart[2] lt 0 then
        sgn_irrationalpart_rempart := " - ";
        noncubepart[2] := -noncubepart[2];
    end if;

    if denominator_noncubepart ne 1 then
        if lcmofdens_cubicpart ne 1 then
            output_string := Sprint(integernum_noncubepart) cat "(" cat Sprint(j_cubicgcdofnums) cat "(" cat Sprint(cubepart[1]) cat sgn_irrationalpart_cubepart cat Sprint(cubepart[2]) cat "\\sqrt{" cat Sprint(g) cat "})/" cat Sprint(lcmofdens_cubicpart) cat ")^3(" cat Sprint(noncubepart[1]) cat sgn_irrationalpart_rempart cat Sprint(noncubepart[2]) cat "\\sqrt{" cat Sprint(g) cat "})/" cat Sprint(denominator_noncubepart);
        else
            output_string := Sprint(integernum_noncubepart) cat "(" cat Sprint(j_cubicgcdofnums) cat "(" cat Sprint(cubepart[1]) cat sgn_irrationalpart_cubepart cat Sprint(cubepart[2]) cat "\\sqrt{" cat Sprint(g) cat "}))^3(" cat Sprint(noncubepart[1]) cat sgn_irrationalpart_rempart cat Sprint(noncubepart[2]) cat "\\sqrt{" cat Sprint(g) cat "})/" cat Sprint(denominator_noncubepart);
        end if;
    elif integernum_noncubepart ne 1 then
        if lcmofdens_cubicpart ne 1 then
            output_string := Sprint(integernum_noncubepart) cat "(" cat Sprint(j_cubicgcdofnums) cat "(" cat Sprint(cubepart[1]) cat sgn_irrationalpart_cubepart cat Sprint(cubepart[2]) cat "\\sqrt{" cat Sprint(g) cat "})/" cat Sprint(lcmofdens_cubicpart) cat ")^3(" cat Sprint(noncubepart[1]) cat sgn_irrationalpart_rempart cat Sprint(noncubepart[2]) cat "\\sqrt{" cat Sprint(g) cat "})";
        else
            output_string := Sprint(integernum_noncubepart) cat "(" cat Sprint(j_cubicgcdofnums) cat "(" cat Sprint(cubepart[1]) cat sgn_irrationalpart_cubepart cat Sprint(cubepart[2]) cat "\\sqrt{" cat Sprint(g) cat "}))^3(" cat Sprint(noncubepart[1]) cat sgn_irrationalpart_rempart cat Sprint(noncubepart[2]) cat "\\sqrt{" cat Sprint(g) cat "})";
        end if;
    else
        if lcmofdens_cubicpart ne 1 then
            output_string := "(" cat Sprint(j_cubicgcdofnums) cat "(" cat Sprint(cubepart[1]) cat sgn_irrationalpart_cubepart cat Sprint(cubepart[2]) cat "\\sqrt{" cat Sprint(g) cat "})/" cat Sprint(lcmofdens_cubicpart) cat ")^3(" cat Sprint(noncubepart[1]) cat sgn_irrationalpart_rempart cat Sprint(noncubepart[2]) cat "\\sqrt{" cat Sprint(g) cat "})";
        else
            output_string := "(" cat Sprint(j_cubicgcdofnums) cat "(" cat Sprint(cubepart[1]) cat sgn_irrationalpart_cubepart cat Sprint(cubepart[2]) cat "\\sqrt{" cat Sprint(g) cat "}))^3(" cat Sprint(noncubepart[1]) cat sgn_irrationalpart_rempart cat Sprint(noncubepart[2]) cat "\\sqrt{" cat Sprint(g) cat "})";
        end if;
    end if;
    return output_string;
end function;

function tex_ratnum(r);
    rnum := Numerator(r);
    rden := Denominator(r);
    if rden ne 1 then
        s := "\\frac{" cat Sprint(rnum) cat "}{" cat Sprint(rden) cat "}";
    else
        s := Sprint(rnum);
    end if;
    return s;
end function;

Ns_new := [133,134,146,166,177,205,206,213,221,255,266,287,299,330];
Ns := [67, 73, 85, 93, 103, 106, 107, 115, 122, 129, 133, 134, 146, 154, 158, 161, 165, 166, 167, 170, 177, 186, 191, 205, 206, 209, 213, 215, 221, 230, 255, 266, 285, 286, 287, 299, 330, 357, 390];

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//   Function to get the Latex script for Table 6: Rational noncusp points, j-invariants and CM discriminants   //
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////

function tex_table_for_N(N);
    pts, polsofjs, factorized_polsofjs, Qj, js, hascm, cmdiscs := jinvs(N);
    s := Sprint(N);
    for i := 1 to #pts do
        if i eq 1 then
            s := s cat " & $\\infty'$ & $\\text{";
        elif i eq 2 then
            primefacsN := PrimeFactors(N);
            s := s cat "$" cat &cat[(k eq #primefacsN) select Sprint(p) else Sprint(p) cat "{\\cdot}" where p is primefacsN[k] : k in [1..#primefacsN]] cat "$";
            pt := pts[i];
            x_pt := pt[1];
            y_pt := pt[2];
            s := s cat " & $(" cat tex_ratnum(x_pt) cat ", " cat tex_ratnum(y_pt) cat ")$ & $\\text{";
        elif i eq 3 and N in Ns_new then
            s := s cat "new";
            pt := pts[i];
            x_pt := pt[1];
            y_pt := pt[2];
            s := s cat " & $(" cat tex_ratnum(x_pt) cat ", " cat tex_ratnum(y_pt) cat ")$ & $\\text{";
        else
            pt := pts[i];
            x_pt := pt[1];
            y_pt := pt[2];
            s := s cat " & $(" cat tex_ratnum(x_pt) cat ", " cat tex_ratnum(y_pt) cat ")$ & $\\text{";
        end if;

        for k := 1 to #hascm[i] do
            yesorno := (hascm[i,k]) select "yes" else "no";
            s := s cat yesorno;
            if k ne #hascm[i] then
                s := s cat ", ";
            end if;
        end for;
        s := s cat "}$ & $";
        for k := 1 to #cmdiscs[i] do
            cmdisc := (cmdiscs[i,k] ne 0) select Sprint(cmdiscs[i,k]) else "";
            s := s cat cmdisc;
            if k ne #cmdiscs[i] then
                s := s cat ", ";
            end if;
        end for;
        s := s cat "$ & $";
        for k := 1 to #factorized_polsofjs[i] do
            ff := factorized_polsofjs[i,k][1];
            if Degree(ff) gt 2 then
                s := s cat "\\Q(";
                gens := Qj[i,k];
                gens_ordered := Sort(gens,func<a,b| AbsoluteValue(a) - AbsoluteValue(b)>);
                for l := 1 to #gens_ordered do
                    s := s cat "\\sqrt{" cat Sprint(gens_ordered[l]) cat "}";
                    if l ne #gens_ordered then
                        s := s cat ", ";
                    end if;
                end for;
                s := s cat ")";
            elif Degree(ff) eq 2 then
                s := s cat tex_factor_quadj(Qj[i,k,1],js[i,k]);
            elif Degree(ff) eq 1 then
                rat_jinv := Roots(ff)[1,1];
                if rat_jinv eq 0 then
                    s := s cat "0";
                else
                    sgn := (rat_jinv lt 0) select "-" else "";
                    s := s cat sgn;
                    primefacs := Sort(PrimeFactors(Numerator(rat_jinv)) cat PrimeFactors(Denominator(rat_jinv)));
                    for l := 1 to #primefacs do
                        p := primefacs[l];
                        s := s cat Sprint(p) cat "^{" cat Sprint(Valuation(rat_jinv,p)) cat "}";
                        if l ne #primefacs then
                            s := s cat "~";
                        end if;
                    end for;
                end if;
            end if;
            if k ne #factorized_polsofjs[i] then
                s := s cat ", ";
            end if;
        end for;
        s := s cat "$\\\\\n";
    end for;
    s := s cat "\\midrule\n";
    return s;
end function;

for N in Ns do
    tex_table_for_N(N);
end for;

