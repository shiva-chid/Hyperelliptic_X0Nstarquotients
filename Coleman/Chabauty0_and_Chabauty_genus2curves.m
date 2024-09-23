L_mwrk0 := [104, 117, 168, 180];
HallDivs := [[d : d in Divisors(N) | d ne 1 and GCD(d,N div d) eq 1] : N in L_mwrk0];
for i := 1 to #L_mwrk0 do
    N := L_mwrk0[i]; divs := HallDivs[i];
    X := SimplifiedModel(X0NQuotient(N,divs));
    J := Jacobian(X);
    A, phi, boo1, boo2, rkbd := MordellWeilGroupGenus2(J);
    assert not 0 in AbelianInvariants(A);
    ans := Chabauty0(J);
    printf "Number of rational points on X0(%o)star = %o\n", N, #ans;
end for;
/*
Number of rational points on X0(104)star = 3
Number of rational points on X0(117)star = 4
Number of rational points on X0(168)star = 4
Number of rational points on X0(180)star = 4
*/

L_mwrk1 :=  [88, 116, 121, 153, 184, 198, 380, 112, 135, 204, 276, 284];
HallDivs := [[d : d in Divisors(N) | d ne 1 and GCD(d,N div d) eq 1] : N in L_mwrk1];
for i := 1 to #L_mwrk1 do
    N := L_mwrk1[i]; divs := HallDivs[i];
    X := SimplifiedModel(X0NQuotient(N,divs));
    J := Jacobian(X);
    A, phi, boo1, boo2, rkbd := MordellWeilGroupGenus2(J);
    n := #Generators(A);
    assert Order(A.n) eq 0;
    ans := Chabauty(phi(A.n));
    printf "Number of rational points on X0(%o)star = %o\n", N, #ans;
end for;

/*
Number of rational points on X0(88)star = 6
Number of rational points on X0(116)star = 8
Number of rational points on X0(121)star = 6
Number of rational points on X0(153)star = 4
Number of rational points on X0(184)star = 4
Number of rational points on X0(198)star = 4
Number of rational points on X0(380)star = 6
Number of rational points on X0(112)star = 6
Number of rational points on X0(135)star = 3
Number of rational points on X0(204)star = 6
Number of rational points on X0(276)star = 4
Number of rational points on X0(284)star = 4
*/
