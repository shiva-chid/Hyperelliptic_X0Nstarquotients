SetLogFile("ec_X0330star.log");

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

//N=330
_<x>:=PolynomialRing(Rationals());
P1:=ProjectiveSpace(Rationals(),1);
X := X0NQuotient(2*3*5*11,[2,3,5,11]);
X := SimplifiedModel(X);
f,_ := HyperellipticPolynomials(X);

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
g:=Ff2[4][1]*Ff2[5][1]; //one can modify this
g;

MyEllipticChabauty(g,deltas,uXrat);

Degree(K); //4
#deltas; //3


