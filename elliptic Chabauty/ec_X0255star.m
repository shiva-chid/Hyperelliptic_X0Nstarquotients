SetLogFile("ec_X0255star.log");

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

//N=255
_<x>:=PolynomialRing(Rationals());
P1:=ProjectiveSpace(Rationals(),1);

f:= x^6 - 4*x^5 - 12*x^4 + 2*x^3 + 8*x^2 - 4*x + 1;
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
    5,
    1/625*(13*K.1^3 - 91*K.1^2 + 39*K.1 + 252),
    1/16*(2*K.1^3 - 14*K.1^2 + 6*K.1 + 39)
]
[
    { (1 : 0) },
    { (-2 : 1) },
    { (3/5 : 1), (-1 : 1), (0 : 1) },
    { (1/2 : 1) }
]


Using model [
1/5*(-2*F.1^3 + 14*F.1^2 - 6*F.1 - 34),
6*F.1^3 - 42*F.1^2 + 18*F.1 + 130,
1/5*(-134*F.1^3 + 938*F.1^2 - 402*F.1 - 2578),
1/5*(967*F.1^3 - 6769*F.1^2 + 2901*F.1 + 19349),
0
]
Torsion Subgroup = Z/2
The 2-Selmer group has rank 2
New point of infinite order (x = 0)
After 2-descent: 
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 1 = [ 1, 1 ]
Abelian Group isomorphic to Z/2 + Z
Defined on 2 generators
Relations:
    2*G.1 = 0
[ (1/20*(-7*K.1^3 + 49*K.1^2 - 21*K.1 - 149) : K.1^3 - 7*K.1^2 + 3*K.1 + 19 : 
    1), (0 : 1/20*(67*K.1^3 - 469*K.1^2 + 201*K.1 + 1289) : 1) ]
supp(R) = [ 2, 5 ]
Verify Saturation= true
Solutions for twist  1  =  { (1 : 0) }

Using model [
1/5*(4*F.1^3 - 28*F.1^2 + 12*F.1 + 268),
1/5*(-56*F.1^3 + 392*F.1^2 - 168*F.1 + 4328),
1/5*(-3344*F.1^3 + 23408*F.1^2 - 10032*F.1 + 39632),
1/5*(-43216*F.1^3 + 302512*F.1^2 - 129648*F.1 + 627088),
0
]
Torsion Subgroup = Z/2
The 2-Selmer group has rank 2
New point of infinite order (x = 0)
After 2-descent: 
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 2 = [ 1, 1 ]
Abelian Group isomorphic to Z/2 + Z
Defined on 2 generators
Relations:
    2*G.1 = 0
[ (1/5*(68*K.1^3 - 476*K.1^2 + 204*K.1 - 884) : 144*K.1^3 - 1008*K.1^2 + 432*K.1
    + 688 : 1), (0 : 1/5*(3344*K.1^3 - 23408*K.1^2 + 10032*K.1 - 39632) : 1) ]
supp(R) = [ 2, 5 ]
Verify Saturation= true
Solutions for twist  2  =  { (-2 : 1) }

Using model [
1/5*(2*F.1^3 - 14*F.1^2 + 6*F.1 - 6),
1/5*(14*F.1^3 - 98*F.1^2 + 42*F.1 + 58),
1/5*(-34*F.1^3 + 238*F.1^2 - 102*F.1 - 38),
1/5*(-233*F.1^3 + 1631*F.1^2 - 699*F.1 + 389),
0
]
Torsion Subgroup = Z/2
The 2-Selmer group has rank 2
New point of infinite order (x = 1/5*(-31*$.1^3 + 217*$.1^2 - 93*$.1 + 3))
After 2-descent: 
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 3 = [ 1, 1 ]
Abelian Group isomorphic to Z/2 + Z
Defined on 2 generators
Relations:
    2*G.1 = 0
[ (1/5*(K.1^3 - 7*K.1^2 + 3*K.1 - 13) : 1/5*(24*K.1^3 - 168*K.1^2 + 72*K.1 + 8) 
: 1), (1/5*(-3*K.1^3 + 21*K.1^2 - 9*K.1 - 41) : 1/5*(28*K.1^3 - 196*K.1^2 + 
    84*K.1 - 44) : 1) ]
supp(R) = [ 2, 5 ]
Verify Saturation= true
Solutions for twist  3  =  { (0 : 1), (-1 : 1), (3/5 : 1) }

Using model [
1/5*(2*F.1^3 - 14*F.1^2 + 6*F.1 + 194),
-10*F.1^3 + 70*F.1^2 - 30*F.1 - 14,
1/5*(-394*F.1^3 + 2758*F.1^2 - 1182*F.1 + 13282),
-405*F.1^3 + 2835*F.1^2 - 1215*F.1 - 7551,
0
]
Torsion Subgroup = Z/2
The 2-Selmer group has rank 2
New point of infinite order (x = 1/361*(25*$.1^3 - 175*$.1^2 + 75*$.1 - 39753))
After 2-descent: 
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 4 = [ 1, 1 ]
Abelian Group isomorphic to Z/2 + Z
Defined on 2 generators
Relations:
    2*G.1 = 0
[ (5*K.1^3 - 35*K.1^2 + 15*K.1 - 113 : -16*K.1^3 + 112*K.1^2 - 48*K.1 + 848 : 
    1), (1/361*(25*K.1^3 - 175*K.1^2 + 75*K.1 - 39753) : 1/6859*(750936*K.1^3 - 
    5256552*K.1^2 + 2252808*K.1 + 5358992) : 1) ]
supp(R) = [ 2, 5 ]
Verify Saturation= true
Solutions for twist  4  =  { (1/2 : 1) }
[
    1,
    5,
    1/625*(13*K.1^3 - 91*K.1^2 + 39*K.1 + 252),
    1/16*(2*K.1^3 - 14*K.1^2 + 6*K.1 + 39)
]
{ (-2 : 1), (1/2 : 1), (0 : 1), (-1 : 1), (1 : 0), (3/5 : 1) }
*/


