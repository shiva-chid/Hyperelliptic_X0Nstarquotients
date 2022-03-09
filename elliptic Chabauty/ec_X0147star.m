SetLogFile("ec_X0147star.log");

function TwoCoveringQ(d)
A<theta>:=Parent(d);
f<x>:=Modulus(A);
n:=Degree(f);
PA:=PolynomialRing(A,n);
g:=d*(&+[PA.i*theta^(i-1): i in [1..n]])^2;
Cg,Mg:=CoefficientsAndMonomials(g);
F:=BaseField(A);
PF:=PolynomialRing(F,n);
Q:=[0*PF.1: j in [1..n]];
for i in [1..#Cg] do
EC:=[j*Monomial(PF,Exponents(Mg[i])): j in ElementToSequence(Cg[i])];
for j in [1..#EC] do Q[j]:=Q[j]+EC[j]; end for;
end for; 
CQ:=Curve(ProjectiveSpace(PF),Q[3..n]);
mCQ:=map<CQ->ProjectiveSpace(F,1)|[-Q[1],Q[2]]>;
return CQ,mCQ;
end function;



//The following function computes for a given hyperelliptic curve X
//All the "deltas" corresponding to points of the twists of 2-covers of X
//in the form point-theta if the point is not Weierstrass point
//and 1 if the point is at infinity (if the point is Weierstrass 
// returns the answer of TwoCoverDescent of Bruin-Stoll).
//It also prints the deltas not corresponding to points. 
//it returns a boolean that is true if all deltas are productive
//and a list of all the productive deltas. 


function MyDeltas(X,uXrat);
P1:=Scheme(Setseq(uXrat)[1]);
uX:=map<X->P1|[X.1,X.3]>;
Hk,AtoHk:=TwoCoverDescent(X);
A<theta>:=Domain(AtoHk);
deltas:=[h@@AtoHk : h in Hk];
b:=true;
deltasp:=[];
if 1 in deltas then deltasp:=[A!1]; Remove(~deltas,1); end if;
for d in deltas do 
C,mC:=TwoCoveringQ(d);
Ptw:={pt: pt in uXrat | #Points((Codomain(mC)![pt[1],pt[2]])@@mC) gt 0};
if #Ptw eq 0 then print "Delta=",d," is not productive "; b:=false; 
else PtnW:=[pt: pt in Ptw | #Points((Codomain(uX)![pt[1],pt[2]])@@uX) gt 1];
if #PtnW eq 0 then Append(~deltasp,d); 
elif PtnW[1][2] eq 0 then Append(~deltasp,A!1);
else 
Append(~deltasp,PtnW[1][1]/PtnW[1][2]-theta); 
end if;
end if;
end for;
return b,deltasp; 
end function; 


//We collect in a function the final application of Elliptic Chabauty
//We pass a degree 4 polynomial over a number field K
//a list of deltas (elements of A=K[x]/(f) )
//a set of (K-)rational points of P1 whose preimage by C->P1 is K-rational
//where C is the hyperelliptic curve given by y^2=f(x)
//and the map is the "x-map"
//It answers the set of twists done (not very useful)
//and the rational points obtained 
//The parameter IndexBound allows to put some more primes for Chabauty
//with larger primes, more easy Chabauty succeds, but longer to show saturation


function MyEllipticChabauty(g,deltas,uXrat: IndexBound:=2*3*5)
P1:=Scheme(Setseq(uXrat)[1]);
A:=Parent(deltas[1]);
K:=BaseRing(g);
twistsb:=[];
pointsdone:={};
L<Th>:=quo<PolynomialRing(K)| g>; AtoL:=hom<A->L|Th>;
twist_list:=[Norm(AtoL(delta)):delta in deltas];
//The following computes the real list of twists (with the points they produce)
twists:=[];twistspt:=[];
PointsCover:={};
for tw in twist_list do 
H:=HyperellipticCurve(tw*g);
Ptw:={pt: pt in uXrat | pt[2] ne 0 and #Points(H,pt[1]/pt[2]) gt 0};
if #PointsAtInfinity(H) gt 0 then Ptw:=Ptw join {pt: pt in uXrat| pt[2] eq 0};end if;
if #(Ptw meet PointsCover) ne #Ptw then Append(~twists,tw); 
PointsCover:=PointsCover join Ptw; Append(~twistspt,Ptw);
end if;
end for;
print(twists);
print(twistspt);
for i in [1..#twists] do
tw:=twists[i];
H:=HyperellipticCurve(tw*g);
P0:=Setseq(PointsAtInfinity(H)) cat Setseq(&join{Points(H,pt[1]/pt[2]) : pt in twistspt[i]| pt[2] ne 0});
p0:=P0[1]; 
E,HtoE:=EllipticCurve(H,p0);
Em,EtoEm:=IntegralModel(E);
if tw eq 1 then Em:=E; EtoEm:=Isomorphism(E,E); end if;
rank, gs:=DescentInformation(Em: RankOnly:=true);
print"Rank for twist=",i,"=",rank;
//if rank[1] lt rank[2] then
//print"Analytic rank is",AnalyticRank(Em);
//end if;
if rank[1] lt Degree(K) then 
TEm,mTEm:=TorsionSubgroup(Em);
HtoP1:=map<H->P1|[H.1,H.3]>;
EmtoP1:=Inverse(EtoEm)*Inverse(HtoE)*HtoP1; 
u := Extend(EmtoP1);
if rank[1] eq 0 then V:=TEm; mwmap:=mTEm; 
b:=true;
else 
ABB,AB:=AbelianBasis(TEm);
G:=AbelianGroup(AB cat [0: i in [1..rank[1]]]);
G;
gs:=[mTEm(a): a in ABB] cat gs;
gs:=Saturation(gs, 6);
gs;
mwmap:=map<G->Em|a:->&+[a[i]*gs[i]:i in [1..#gs]]where a:=Eltseq(a)>;
//SetVerbose("EllChab", 1);
V,R:=Chabauty(mwmap,u:IndexBound:=IndexBound); 
print "supp(R) =", PrimeDivisors(R);
b:=&and[IsPSaturated(mwmap,p) : p in PrimeDivisors(R)]; 
print "Verify Saturation=",  b; 
end if;
pttw:={EvaluateByPowerSeries(u,mwmap(P)):P in V};
pttw:={pt: pt in pttw | pt in P1(Rationals())};
if b then Append(~twistsb,tw); pointsdone:=pointsdone join pttw;
print "Solutions for twist ",i," = ",pttw;
end if;
end if;
end for;
return twistsb,pointsdone;
end function;









///////////////////////////////////////

//N=147
_<x>:=PolynomialRing(Rationals());
P1:=ProjectiveSpace(Rationals(),1);

f:= x^6 - 4*x^4 + 2*x^3 + 8*x^2 - 12*x + 9;
X:=HyperellipticCurve(f);
Ff:=Factorization(f);
Ff;
Xrat:=Points(X: Bound:=10000);
Xrat;
uX:=map<X->P1|[X.1,X.3]>;
uXrat:={uX(P):P in Xrat};

print "Set of x-coordinates:", uXrat;

b,deltas:=MyDeltas(X,uXrat);

print "Productive deltas =", deltas; 


g:=Ff[2][1];g;

K:=NumberField(Factorization(f)[2][1]);
Ff2:=Factorization(ChangeRing(f,K));
Ff2;
g:=Ff2[3][1]*Ff2[4][1];
g;

MyEllipticChabauty(g,deltas,uXrat);


/*
[
    1,
    -3,
    1/3*(-14*K.1^3 - 14*K.1^2 + 14*K.1 + 21),
    1/16*(14*K.1^3 + 14*K.1^2 - 14*K.1 - 21)
]
[
    { (1 : 1), (1 : 0), (-5/3 : 1) },
    { (0 : 1) },
    { (-2 : 1) },
    { (3/2 : 1) }
]


Using model [
1/3*(2*F.1^3 + 2*F.1^2 - 2*F.1 - 6),
2*F.1^3 + 2*F.1^2 - 2*F.1 + 14,
10*F.1^3 + 10*F.1^2 - 10*F.1 + 22,
17*F.1^3 + 17*F.1^2 - 17*F.1 + 223,
0
]
Torsion Subgroup = Z/2
The 2-Selmer group has rank 2
New point of infinite order (x = 1/3*(-35*$.1^3 - 35*$.1^2 + 35*$.1 + 51))
After 2-descent: 
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 1 = [ 1, 1 ]
Abelian Group isomorphic to Z/2 + Z
Defined on 2 generators
Relations:
    2*G.1 = 0
[ (1/4*(-K.1^3 - K.1^2 + K.1 + 1) : 1/3*(-2*K.1^3 - 2*K.1^2 + 2*K.1 - 6) : 1), 
(1/4*(3*K.1^3 + 3*K.1^2 - 3*K.1 - 19) : 1/6*(5*K.1^3 + 5*K.1^2 - 5*K.1 + 27) : 
    1) ]
supp(R) = [ 2, 3 ]
Verify Saturation= true
Solutions for twist  1  =  { (1 : 1), (1 : 0), (-5/3 : 1) }

Using model [
1/3*(-2*F.1^3 - 2*F.1^2 + 2*F.1 - 18),
1/3*(-10*F.1^3 - 10*F.1^2 + 10*F.1 - 102),
1/3*(-70*F.1^3 - 70*F.1^2 + 70*F.1 + 678),
65*F.1^3 + 65*F.1^2 - 65*F.1 + 1967,
0
]
Torsion Subgroup = Z/2
The 2-Selmer group has rank 2
New point of infinite order (x = 1/3*(113*$.1^3 + 113*$.1^2 - 113*$.1 + 195))
After 2-descent: 
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 2 = [ 1, 1 ]
Abelian Group isomorphic to Z/2 + Z
Defined on 2 generators
Relations:
    2*G.1 = 0
[ (1/3*(5*K.1^3 + 5*K.1^2 - 5*K.1 - 21) : 16*K.1^3 + 16*K.1^2 - 16*K.1 - 144 : 
    1), (1/3*(113*K.1^3 + 113*K.1^2 - 113*K.1 + 195) : -440*K.1^3 - 440*K.1^2 + 
    440*K.1 + 288 : 1) ]
supp(R) = [ 2, 3 ]
Verify Saturation= true
Solutions for twist  2  =  { (0 : 1) }

Using model [
1/3*(28*F.1^3 + 28*F.1^2 - 28*F.1 - 108),
56*F.1^3 + 56*F.1^2 - 56*F.1 - 808,
-2576*F.1^3 - 2576*F.1^2 + 2576*F.1 + 6928,
-14000*F.1^3 - 14000*F.1^2 + 14000*F.1 + 139696,
0
]
Torsion Subgroup = Z/2
The 2-Selmer group has rank 2
New point of infinite order (x = 1/363*(8036*$.1^3 + 8036*$.1^2 - 8036*$.1 + 
126828))
After 2-descent: 
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 3 = [ 1, 1 ]
Abelian Group isomorphic to Z/2 + Z
Defined on 2 generators
Relations:
    2*G.1 = 0
[ (28*K.1^3 + 28*K.1^2 - 28*K.1 + 292 : 1/3*(112*K.1^3 + 112*K.1^2 - 112*K.1 + 
    12432) : 1), (1/363*(8036*K.1^3 + 8036*K.1^2 - 8036*K.1 + 126828) : 
1/3993*(-283696*K.1^3 - 283696*K.1^2 + 283696*K.1 + 19105968) : 1) ]
supp(R) = [ 2, 3, 5 ]
Verify Saturation= true
Solutions for twist  3  =  { (-2 : 1) }

Using model [
14*F.1^3 + 14*F.1^2 - 14*F.1 + 6,
-126*F.1^3 - 126*F.1^2 + 126*F.1 - 1746,
-6174*F.1^3 - 6174*F.1^2 + 6174*F.1 + 7614,
-47439*F.1^3 - 47439*F.1^2 + 47439*F.1 + 944703,
0
]
Torsion Subgroup = Z/2
The 2-Selmer group has rank 2
New point of infinite order (x = 1/529*(-1113*$.1^3 - 1113*$.1^2 + 1113*$.1 + 
888201))
After 2-descent: 
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 4 = [ 1, 1 ]
Abelian Group isomorphic to Z/2 + Z
Defined on 2 generators
Relations:
    2*G.1 = 0
[ (-105*K.1^3 - 105*K.1^2 + 105*K.1 + 873 : -504*K.1^3 - 504*K.1^2 + 504*K.1 - 
    19656 : 1), (1/529*(-1113*K.1^3 - 1113*K.1^2 + 1113*K.1 + 888201) : 
1/12167*(-135698472*K.1^3 - 135698472*K.1^2 + 135698472*K.1 + 78456168) : 1) ]
supp(R) = [ 2, 3, 5 ]
Verify Saturation= true
Solutions for twist  4  =  { (3/2 : 1) }
[
    1,
    -3,
    1/3*(-14*K.1^3 - 14*K.1^2 + 14*K.1 + 21),
    1/16*(14*K.1^3 + 14*K.1^2 - 14*K.1 - 21)
]
{ (3/2 : 1), (1 : 1), (0 : 1), (-2 : 1), (1 : 0), (-5/3 : 1) }*/


