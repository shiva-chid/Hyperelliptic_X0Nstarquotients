SetDebugOnError(true);
SetLogFile("qc_X0287star.log");
load "qc_modular.m";
load "divisor_heights.m";
load "qc_init_g2.m";
load "howe_zhu.m";
_<x> := PolynomialRing(Rationals());

levelN := 287;
printf "X_0(%o)^*:\n", levelN;
X := X0NQuotient(levelN, [p^Valuation(levelN,p) : p in PrimeDivisors(levelN)]);
X := SimplifiedModel(X);
assert IsHyperelliptic(X);

f, h := HyperellipticPolynomials(X);
assert h eq 0;

// Move rational points away from infinity. If there are no rational points at infinity
// mod p, then we only need quadratic Chabauty on one affine patch, because the disks at
// infinity can be handled via the Mordell-Weil sieve.

function find_transformation(X,p)
  N := 15;
  height_bound := 200;
  gX := Genus(X);
  for a,b,c,d in [0..3] do
    if a*d - b*c eq 0 then
      continue;
    end if;
    Xprime, m := Transformation(X, [a,b,c,d]);
    f, h := HyperellipticPolynomials(Xprime);
    assert h eq 0;
    // is X' defined over Z?
    if not forall{an : an in Coefficients(f) | IsCoercible(Integers(), an)} or not forall{an : an in Coefficients(h) | IsCoercible(Integers(), an)} then
      continue;
    end if;

    if #PointsAtInfinity(BaseChange(Xprime, Bang(Rationals(), GF(p)))) eq 0 then
      printf "Trying transformation with %o.\n", [a,b,c,d];

      J := Jacobian(Xprime);
      try
	      //print Xprime;
        ptsX := Points(Xprime : Bound := height_bound);
        index_of_base_point := [i : i in [1..#ptsX] | ptsX[i,3] ne 0][1]; // first index of ptsX such that the z-coordinate is non-zero
        assert ptsX[index_of_base_point,3] ne 0;
        base_pt := [ptsX[index_of_base_point,1]/ptsX[index_of_base_point,3], ptsX[index_of_base_point,2]/ptsX[index_of_base_point,3]^(gX+1)]; 
        printf "Using base point %o.\n", base_pt;

        // Compute generators for the full Mordell-Weil group using Stoll's MordellWeilGroupGenus2
//	printf "computing generators of Mordell-Weil group...\n";
//        torsion_bas, torsion_orders, bas := generators(J);
//	printf "computed generators of Mordell-Weil group\n";
//        assert #bas eq 2; // rank = 2
        // This spares us the trouble of checking saturation in MW sieve computation.
//	printf "computing splitting generators...\n";
//        splitting_generators, divisors, intersections, splitting_indices, odd_divisors_Qp := height_init_g2(Xprime, p, bas: N := N, multiple_bound := 40); 
//	printf "computed splitting generators\n";

    /*  _, _, bad_affine_rat_pts_xy, _, _, bad_Qppoints := QCModAffine(y^2-f, p : printlevel := 2, N := N, prec := 40, base_point := base_pt);
      printf "There are %o bad Q_%o-points.\n", #bad_Qppoints, p;
      printf "There are %o bad Q-points : %o\n", #bad_affine_rat_pts_xy, [pt @@ m : pt in bad_affine_rat_pts_xy];

      if #bad_Qppoints gt 0 then
        continue;
      end if;*/
      catch e 
	      printf "%o\n", e;
        continue;
      end try;

      printf "Using transformation with %o.\n", [a,b,c,d];
      return Xprime;
    end if;
  end for;
  error "Did not find a small transformation.";
end function;

primes := [19, 29];
X := find_transformation(X, primes[1]); // find a linear transformation such that X has no Q-points at infinity and no bad Qp-points
// X := Transformation(X, [ 0, 1, 1, 2 ]);
f, h := HyperellipticPolynomials(X);
assert h eq 0;
printf "Using X: %o\n", X;

J := Jacobian(X);
assert HasAbsolutelyIrreducibleJacobian(X, 1000 : printlevel := 0);
printf "The Jacobian of X is absolutely simple.\n";

gX := Genus(X);
height_bound := 1000;
ptsX := Points(X : Bound := height_bound);
printf "There are %o points of height <= %o:\n%o\n", #ptsX, height_bound, ptsX;


// Find primes for the quadratic Chabauty computation. In particular, check whether they 
// look promising for a combination of qc and the Mordell-Weil sieve
qc_primes, groups, good_primes := 
               find_qc_primes(X : mws_primes_bound := 1000, qc_primes_bound := 200, number_of_bad_disks := 1, inf_modp_allowed := false,
                                   ordinary := false, known_rat_pts := ptsX, printlevel := 0);
                                   // we want exactly one bad Q_p point, so there is an odd degree model over Q_p
printf "You might want to use the primes %o for QC.\n", qc_primes;
// [ 3, 5, 19, 23, 29, 31, 53, 59, 67, 89, 97, 103, 131, 137, 179, 197 ]
// 3, 5: lambda


exponents := [1 : p in primes];//[Valuation(#BaseChange(J, GF(p)), p)]; // exponent of p in #J(F_p)?
printf "Using p in %o.\n", primes;
S0 := CuspidalSubspace(ModularSymbols(levelN, 2));
S := S0; // compute the modular symbols space associated to X_0(levelN)^*
for q in PrimeDivisors(levelN) do
    S := AtkinLehnerSubspace(S, q, 1);
end for;
assert forall{p : p in primes | hecke_operator_generates(S, p)};

// First compute local heights of representatives for generators of J(Q) tensor Q at p. 

index_of_base_point := [i : i in [1..#ptsX] | ptsX[i,3] ne 0][1]; // first index of ptsX such that the z-coordinate is non-zero
assert ptsX[index_of_base_point,3] ne 0;
base_pt := [ptsX[index_of_base_point,1]/ptsX[index_of_base_point,3], ptsX[index_of_base_point,2]/ptsX[index_of_base_point,3]^(gX+1)]; 
printf "Using base point %o.\n", base_pt;

torsion_bas, torsion_orders, bas, mMW := generators(J);
assert #bas eq gX; // rank = 2


// find a finite index subgroup (generated by divisors) of J(Q) given by differences of P in C(Q), and writes them in the basis bas of J(Q) (splitting_indices)
function divisors_from_curve(X)
  divisors_found := [];
  splitting_indices_found := [];
  indices_found := [];
  index := 0;
  for P1P2 in Subsets({P : P in ptsX}, 2) do
    P1, P2 := Explode(Setseq(P1P2));
    if 0 in {P1[3], P2[3]} then // exclude the case where one point is at infinity
      continue;
    end if;
    for Q1Q2 in Subsets({P : P in ptsX}, 2) do
      Q1, Q2 := Explode(Setseq(Q1Q2));
      if 0 in {Q1[3], Q2[3]} or P1P2 eq Q1Q2 then // exclude the case where one point is at infinity
        continue;
      end if;
      divisors := [* [* [[P1[1]/P1[3],P1[2]/P1[3]^(gX+1)]], [[P2[1]/P2[3],P2[2]/P2[3]^(gX+1)]] *],
                     [* [[Q1[1]/Q1[3],Q1[2]/Q1[3]^(gX+1)]], [[Q2[1]/Q2[3],Q2[2]/Q2[3]^(gX+1)]] *]*];
      D1 := P1 - P2; // in J(Q)
      D2 := Q1 - Q2;
      splitting_generators := [D1, D2];
      
      D1_in_MW := D1 @@ mMW;
      D2_in_MW := D2 @@ mMW;
      splitting_indices := [Eltseq(D1_in_MW)[#torsion_bas+1..#torsion_bas+gX], Eltseq(D2_in_MW)[#torsion_bas+1..#torsion_bas + #bas]]; // D1, D2 in bas.i
      
      // compute the index of the span of divisors in the MW group
      index := Index(Domain(mMW), sub< Domain(mMW) | [D1_in_MW, D2_in_MW] >);
      if index ne 0 then
        Append(~divisors_found, divisors);
        Append(~splitting_indices_found, splitting_indices);
        Append(~indices_found, index);
      end if;
      if index eq &*torsion_orders then // we found the whole free part of the MW group
        break;
      end if;
    end for;
    if index eq &*torsion_orders then
      break;
    end if;
  end for;
  // take the configuration with minimal finite index
  min, pos := Minimum(indices_found);
  assert min gt 0;
  divisors := divisors_found[pos];
  splitting_indices := splitting_indices_found[pos];
  printf "Use independent points %o\n", divisors;
  printf "splitting indices: %o\n", splitting_indices;
  printf "index in J(Q): %o\n", min;
  return divisors, splitting_indices;
end function;

//divisors, splitting_indices := divisors_from_curve(X);

function run_QC(p, N1, N2)
  assert N1 ge N2;

  try
    // Compute good generators and intersection data for Coleman-Gross heights
    printf "computing CG heights with N1 = %o\n", N1;
    splitting_generators, divisors, intersections, splitting_indices, odd_divisors_Qp := height_init_g2(X, p, bas :
                                                                                                       N := N1, multiple_bound := 40); 

    printf "computing odd degree model\n";
    odd_f_Qp := HyperellipticPolynomials(Curve(odd_divisors_Qp[1,1,1]));
    odd_f := ChangeRing(odd_f_Qp, Rationals());
    odd_data := coleman_data(y^2-odd_f, p, N1 : useU := false, heights);
    odd_divisors := [* [*rationalize(D[1]), rationalize(D[2])*] : D in odd_divisors_Qp *];

    odd_data_divisors :=  [
    [  [<set_point(pair[1,i,1], pair[1,i,2], odd_data), 1> ,
      <set_point(pair[2,i,1], pair[2,i,2], odd_data), -1>] : i in [1..#pair]]
          : pair in odd_divisors];

    // Need to manipulate the representatives to get disjoint support for 
    // local height pairings.
    // The following is specific to genus 2.
    odd_data_divisors_inv := [
    [ [<set_point(odd_divisors[1,1,i,1], -odd_divisors[1,1,i,2], odd_data), 1>, 
    <set_point(odd_divisors[2,2,i,1], odd_divisors[2,2,i,2], odd_data), -1>] 
    : i in [1,2]  ],  
    [ [<set_point(odd_divisors[2,1,i,1], -odd_divisors[2,1,i,2], odd_data), 1>, 
    <set_point(odd_divisors[1,2,i,1], odd_divisors[1,2,i,2], odd_data), -1>] 
    : i in [1,2]  ]
    ];
    odd_data`ordinary := true;
    odd_data`cpm := -cup_product_matrix(odd_data`basis, odd_data`Q, 2, odd_data`r, odd_data`W0);

    printf "\nStart computation of local height at %o between first pair of divisors\n", p;
    time ht1, D1_data := local_height_divisors_p(odd_data_divisors[1], odd_data_divisors_inv[1],odd_data);
    "Time for first height";
    printf "Start computation of local height at %o between second pair of divisors\n", p;
    time ht2 := local_height_divisors_p(odd_data_divisors[1], odd_data_divisors[2],odd_data :D1_data := D1_data);
    "Time for second height";
    printf "Start computation of local height at %o between third pair of divisors\n", p;
    time ht3 := local_height_divisors_p(odd_data_divisors_inv[2], odd_data_divisors[2], odd_data);
    "Time for third height";
    local_CG_hts := [-ht1, ht2, -ht3];

    "local heights", local_CG_hts;

    printf "Computing Coleman data with N = %o.\n", N1;
    data := coleman_data(y^2 - f, p, N1 : useU := false);
    height_coeffs := height_coefficients(divisors, intersections, local_CG_hts, data);

    printf "\nStarting quadratic Chabauty for p = %o.\n", p;
    good_affine_rat_pts_xy, no_fake_pts, bad_affine_rat_pts_xy, data, fake_rat_pts, bad_Qppoints :=
        QCModAffine(y^2-f, p : printlevel := 1, unit_root_splitting := true,
              N := N1, base_point := base_pt, height_coeffs := height_coeffs, use_log_basis := true); // prec := 40, 
    printf "There are %o fake rational points: %o\n", #fake_rat_pts, fake_rat_pts;
    printf "There are %o bad Q_%o-points.\n", #bad_Qppoints, p;

    function recompute_Coleman_data(N1, N2, fake_rat_pts)
      try
        // BUG: recompute Coleman data
        // Here * good_affine_rat_pts_xy contains the found rational points in disks where the Frob lift is defined 
        //      * no_fake_pts is true iff the solutions are exactly the rational points
        //      * bad_affine_rat_pts_xy contains the found rational points in disks where the Frob lift isn't defined 
        //      * data is the Coleman data of X at p used in the qc computation
        //      * fake_rat_pts contains the p-adic solutions that don't look rational
        //      * bad_Qppoints contains the disks where Frob isn't defined
        //
        // Express the images of the solutions under Abel-Jacobi in terms of the generators mod p^N
        fake_rat_pts_new := [];
        for i in [1..#fake_rat_pts] do
          fake_rat_pts_new[i] := [ChangePrecision(fake_rat_pts[i,j], N2 div 2) : j in [1..2]]; // N2 div 2
          // lower precision for speed and to avoid issues in Coleman integrals.
        end for;
        printf "Re-computing Coleman data with N2 = %o.\n", N2;
        data := coleman_data(y^2-f, p, N2 : useU := false);

        fake_coeffs_mod_pN, rat_coeffs_mod_pN := coefficients_mod_pN(fake_rat_pts_new, good_affine_rat_pts_xy, divisors, base_pt, splitting_indices, data : printlevel := 3); 
        // Check that the coefficients of the known rational points are correct.
        assert &and[&+[rat_coeffs_mod_pN[j,i] * bas[i] : i in [1..gX]] eq X!good_affine_rat_pts_xy[j] - X!base_pt : j in [1..#good_affine_rat_pts_xy]];
      catch e 
        printf "%o\n", e;
        if N2 lt N1 then
          N2 +:= 1;
        else 
          error "reached N2 = N1";
        end if;
        printf "trying N1 = %o, N2 = %o ...\n", N1, N2;
        return $$(N1, N2, fake_rat_pts);
      end try;
      return fake_coeffs_mod_pN, rat_coeffs_mod_pN;
    end function;

    fake_coeffs_mod_pN, rat_coeffs_mod_pN := recompute_Coleman_data(N1, N2, fake_rat_pts);
  catch e
    printf "%o\n", e;
    N1 +:= 1;
    if N1 ge 30 then
      error "reached N1 = 30";
    end if;
    return $$(p, N1, 8);
  end try;
  
  return fake_coeffs_mod_pN, rat_coeffs_mod_pN;
end function;

fake_coeffs := [];
for p in primes do
  fake_coeffs_mod_pN, rat_coeffs_mod_pN := run_QC(p, 15, 8);
  Append(~fake_coeffs, [fake_coeffs_mod_pN]);
end for;

printf "\nUse the Mordell-Weil sieve to show that the additional %o solutions aren't rational.\n", [#fake_coeffs_mod_pN[1] : fake_coeffs_mod_pN in fake_coeffs];

printf "generating cosets ...\n";
qc_fake_coeffs_mod_M := coeffs_CRT(fake_coeffs, primes, exponents);
printf "number of cosets: %o\n", #qc_fake_coeffs_mod_M;
qc_M := &*[primes[i]^exponents[i] : i in [1..#primes]];  // modulus
M := qc_M;
aux_int := 1;
printf "adding information modulo %o\n", aux_int;
fake_coeffs_mod_M := combine_fake_good(qc_fake_coeffs_mod_M, qc_M, aux_int);
M := qc_M*aux_int; // modulus
qc_rat_coeffs_mod_M := [];
for pt in ptsX do
  ptJ := X!pt - X!base_pt;
  Append(~qc_rat_coeffs_mod_M, [t mod M : t in Eltseq(ptJ@@mMW)]);
end for;
printf "number of cosets: %o\n", #fake_coeffs_mod_M;
mws_primes := sieving_primes(M, good_primes, groups, 70);
printf "sieving with S = %o\n", mws_primes;
printf "gcd(#J(F_ell), #J(F_q)) (ell in S, q | MM') = %o\n", Gcd([#BaseChange(J, GF(v)) : v in mws_primes cat PrimeDivisors(M)]);
factored_orders := [FactoredOrder(BaseChange(J, GF(v))) : v in mws_primes];
printf "with [#J(F_v) : v in S] = %o\nand gcd_v(#J(F_v)) = %o\n", factored_orders, Factorization(Gcd([#BaseChange(J, GF(v)) : v in mws_primes]));

printf "starting Mordell Weil sieve\n";
time done_fake := MWSieve(J, mws_primes, M, bas cat torsion_bas, X!base_pt, fake_coeffs_mod_M : known_rat_coeffs := qc_rat_coeffs_mod_M, printlevel := 0);

printf "done with the MW sieve: %o\n", done_fake;
assert done_fake;
printf "No additional solutions are rational.\n";

/*
for p in primes do
  // Finally exclude points in bad disks and infinite. We checked above that none of these contain a known rational point.
  printf "Use the Mordell-Weil sieve to show that there are no rational points in bad or infinite disks for p = %o\n", p;
  aux_int := 1; // Originally this started with N=1, but we now know that N=60 works...
  printf "auxiliary integer = %o\n", aux_int;
  assert #Roots(ChangeRing(f,GF(p))) eq 1;
  bad_pts_p := [[Roots(ChangeRing(f,GF(p)))[1,1],0,1]];
  infinite_pts_p := [Eltseq(P) : P in PointsAtInfinity(ChangeRing(X, GF(p)))]; // bad points (assume there is exactly one) and infinite points
  printf "there are %o infinite points\n", #infinite_pts_p;
  assert #infinite_pts_p eq 0;
  bad_pts_p cat:= infinite_pts_p;
  modulus := aux_int*Exponent(AbelianGroup(BaseChange(J, GF(p))));
  printf "modulus = %o\n", modulus;
  coeffs_mod_Mp := prerun_mwsieve_g2r2(J, bas, base_pt, modulus, p, bad_pts_p : printlevel := 0);
  printf "number of cosets: %o\n", #coeffs_mod_Mp;
  mws_primes_p := sieving_primes(modulus, good_primes, groups, 20);  // compute sieving primes
  //mws_primes_p := [7,11,19,233,283,331,467,983,1049,1667,10861,25771];
  printf "starting MW-sieve to exclude rational points in bad and infinite disks at p = %o\n", p;
  time done_bad := MWSieve(J, mws_primes_p, modulus, bas cat torsion_bas, X!base_pt, coeffs_mod_Mp : special_p_points := [<p, bad_pts_p>], printlevel := 0); 
  assert done_bad;
  printf "There are no rational points in bad or infinite disks for p = %o", p;
end for;
*/