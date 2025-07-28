\\ Update july 03, 2025
 
\\  For three quartic cyclotomic number fields: "k=bnfinit(p)"
\\  p=x^4+1 (so it has torsion group of order m=8)
\\  p=x^4-x^3+x^2-x+1 (then m=10)
\\  p=x^4-x^2+1   (then m=12)
\\  Below we show an implementation which verify the following three claims.

\\ Claim I:
\\       S:=\bicup_{j=0}^{m-1}w^{j}*C_0 (a polyhedral complex of "m" pointed cones,for m=8, 10 or 12)
\\ can be written as a disjoint union: {0}\cup (\bigcup w^{j}*C'_0)={0}\cup S' for j=0,1,...,m-1, 
\\ and C'_0=C_0-(C_0\cap C_1),  C_0=Cone[1,w,w^2,w^3], with w m-root of unit (or a power of this).


\\ Claim II: 
\\        u*S \subset S,
\\ where "u" is one fundamental unit of "k=bnfinit(p)" given by PARI/GP.


\\ Claim III: 
\\    There are positive constants c' and d' such that P^{Delta,Delta}(c') \subset S \subset P^{Delta,Delta}(d')

\\ These claims are based in our MANUSCRIPT (MS):
\\ https://www.sciencedirect.com/science/article/abs/pii/S0022314X23002299

/************************************************************************************************************/
\\ VERIFICATION OF CLAIM I:

\\    S a polyhedral complex of "m" pointed polyhdral cones, for m=8, 10 or 12.
\\    can be written as a disjoint union: {0}\cup (\bigcup w^{j}*C'0) for j=0,1,...,m-1

\\ Input: given "bnf=bnfinit(p)", where p = x^4+1, x^4-x^3+x^2-x+1 or x^4-x^2+1 
\\ Output: return the difference "C0-(S')" of C0 with S', and a vector [0/1] of size m-1 ,
\\ since we want to verify that S (union of closed polyhedral cones) can be write as 
\\ a disjoint union {0}\cup S':= {0}\cup (\bigcup w^{j}*C'0) for j=0,1,...,m-1 (of semi-closed cones)
\\ It is clear that {0}\cup S' is contained in S
\\ Only need to verify that S is contained in {0}\cup S'
\\ for this, it is enough to compute the difference: C0-S' (one cone with the complex S')
\\ we want to verify that L1=C0-(S') is [] which it is interpreted in this case as the vertex {0}

DifConeS(bnf)=
{my(k,p,m,w,S,S1,C1,L0,L1,v1,v2,f,h,h1,h2,l);
k=bnf; p=k.pol;
[m,w]=[k.tu[1],lift(k.tu[2])]; \\ order of torsion group m=8, 10, 12, whose generator is "w"
v1=precision(conjvec(Mod(w,p)),10000); 
[h1,h2]=abs(arg([v1[1],v1[3]]))*(m/(2*Pi)); [h1,h2]=ceil([h1,h2]); l=vecmax([h1,h2]); \\l=3 or 5
if([h1,h2]==[1,l], w=lift(Mod(w^l,p)));
S=vector(m,j,lift(Mod(w^(j-1)*[1,w,w^2,w^3],p))); \\The union S of the "m" closed cones given by generators
S1=vector(m,j,concat(HV(S[j],k),[[1,1,1,1]])); \\ S now given by [generators, inequalities, [1,1,1,1]]
C1=kcomplex2(S,k);  \\ represent the complex: S' of semi-closed cones
L0=vector(m-1,j);  
for(j=2,m, 
   v2=intCones2([C1[1],C1[j]],k); \\ intersection of C1[1] with C1[j], j=2...m
   [f,h]=[v2[2],v2[3]];
   if(f==0 && h==0, L0[j-1]=1);
   );
L1=[S1[1]];
for(i=1,#C1, if(#L1>0, L1=kdcomplex(L1,C1[i],k))); \\difference of closed cone C0:=S1[1] with the complex C1=S'
return([L1[1][1], L0]);  \\ L1[1][1]=C0-C1= [](?)
\\L0=vector of 0/1, which means that the union S' is disjoint, if all returns are 1's.
}


/************************************************************************************************************/
\\ VERIFICATION OF CLAIM II: 
\\                u*S \subset S
\\ WE CONSIDER THE FOLLOWING IMPLEMENTATION.

\\ INPUT: given "k=bnfinit(p)" and "u" one fundamental unit of k,
\\ here we consider: 
\\   u=x^2+x+1 for m=8,
\\   u=-x+1 for m=10,
\\   u=-x^3-x^2 for m=12. All of these have a modulus less than 1 in their first embedding.

\\ OUTPUT: D=u*S-S, if returns empty, then u*S \subset S, otherwise it's not contained.

DiffComplex2(bnf,u)=
{my(k,p,m,w,v1,v2,h1,h2,l,S,C1,C2,D,D1);
k=bnf;p=k.pol;
[m,w]=[k.tu[1],lift(k.tu[2])]; \\ order of torsion group m=8, 10, 12, whose generator is "w"
v1=precision(conjvec(Mod(w,p)),10000); 
[h1,h2]=abs(arg([v1[1],v1[3]]))*(m/(2*Pi)); [h1,h2]=ceil([h1,h2]); l=vecmax([h1,h2]); \\l=3 or 5
if([h1,h2]==[1,l], w=lift(Mod(w^l,p)));
S=vector(m,j,lift(Mod(w^(j-1)*[1,w,w^2,w^3],p)));
\\S1=vector(m,j,concat(HV(S[j],k),[[-1,1,1,1]]));
C1=kcomplex2(S,k);
v2=conjvec(Mod(u,p)); if(abs(v2[1])>1, u=lift(Mod(u^(-1),p)));   \\ <u> free part of the group G, with abs(u[1])<1
C2=kmultcomplex(u,C1,p);
D=vector(#C1,j);
for(j=1,#C2,
    D1=[C2[j]]; 
    for(i=1,#C1, if(#D1>0, D1=kdcomplex(D1,C1[i],k)));
    D[j]=D1);   
D=concat(D);
return(D);
\\ D represents the difference of polyhedral complexes "u*S-S=u*(S')-(S')", if this return [] (empty), u*S \subset S.
}


/************************************************************************************************************/
\\ VERIFICATION OF CLAIM III: 
\\ There are positive constants c' and d' such that P^{Delta,Delta}(c') \subset S \subset P^{Delta,Delta}(d')
\\ WE CONSIDER THE FOLLOWING THREE STEPS.

\\ STEP 1
\\ INPUT: (bnf,c,d)
\\ where bnf=bnfinit(p), and
\\ [c,d] are positive integers:
\\ [c,d]=[1/5,5] for p=x^4+1,
\\ [c,d]=[1/6,4] for p=x^4-x^3+x^2-x+1,
\\ [c,d]=[1/8,2] for p=x^4-x^2+1.

\\ OUTPUT: [A,R], where
\\ A:=f(P^{\Delta,\Delta}(c)) and R:=f(P^{\Delta,\Delta}(d)),
\\ They represent complexes of three k-rational 4-dimensional polyhedral cones with "6" generators and "5" inequalities.
\\ BASED ON LEMMA 10 OF MANUSCRIPT (MS).


ApproxRComplex(bnf,c,d)= 
{my(M1,M2,R1,R2,C1,C2);
M1=KMat2(bnf,c,3,3)[1];  \\list of "3" columns vector of size "3" 
M2=KMat2(bnf,d,3,3)[1];
R1=vector(3,j); R2=vector(3,j);
for(e=1,2, R1[e]=concat(M1[e],M1[e+1]); R2[e]=concat(M2[e],M2[e+1]););
R1[3]=concat(M1[3],M1[1]); R2[3]=concat(M2[3],M2[1]);
for(j=1,3, 
    C1=R1[j]; 
    C2=R2[j]; 
    R1[j]=vector(6,i,C1[i]/abs(content(C1[i]))); 
    R2[j]=vector(6,i,C2[i]/abs(content(C2[i])));
   );
return([R1,R2]); 
}


/************************************************************************************************************/
\\ STEP 2
\\ INPUT: (bnf, C1, C2)
\\ where k=bnf=bnfinit(p);
\\ C1 and C2 are two complexes of k-rational polyhedral cones obtained in STEP 1: 
\\  C1=f(P^{\Delta,\Delta}(c)) and C2=f(P^{\Delta,\Delta}(d))

\\ OUTPUT: Calculate [T1,T2], where
\\ T1=C1-S and T2=S-C2
\\ S=complex of "m" k-rational polyhedral four-dimensional pointed cones
\\ if T1=T2=empty, then C1 \subset S \subset C2.


DiffComplex1(bnf,C1,C2)=
{my(k,p,w,m,S,S1,S2,Q1,Q2,T1,D1,T2,D2,v1,h1,h2,l);
k=bnf;p=k.pol;
[m,w]=[k.tu[1],lift(k.tu[2])]; \\ order of torsion m=8, 10, 12, whose generator is "w"
v1=precision(conjvec(Mod(w,p)),10000); 
[h1,h2]=abs(arg([v1[1],v1[3]]))*(m/(2*Pi)); [h1,h2]=ceil([h1,h2]); l=vecmax([h1,h2]);
if([h1,h2]==[1,l], w=lift(Mod(w^l,p)));
S=vector(m,j,lift(Mod(w^(j-1)*[1,w,w^2,w^3],p)));
\\S1=vector(m,j,concat(HV(S[j],k),[[-1,1,1,1]]));
S=kcomplex2(S,k);
Q1=kcomplex2(C1,k); \\attractor candidate: Q1 is contained in S
Q2=kcomplex2(C2,k); \\repulsor candidate: S is contained in Q2
T1=vector(#Q1,j);
  for(j=1,#Q1,
    D1=[Q1[j]]; 
    for(i=1,#S, if(#D1>0, D1=kdcomplex(D1,S[i],k)));
    T1[j]=D1);   
T1=concat(T1);\\ T1 represents the difference of polyhedral complexes "Q1-S=f(P(c))-S", if this is empty, Q1 is contained in S.
T2=vector(#S,j);
  for(j=1,#S,
    D2=[S[j]]; 
    for(i=1,#Q2, if(#D2>0, D2=kdcomplex(D2,Q2[i],k)));
    T2[j]=D2);   
T2=concat(T2);\\ T2 represents the difference of polyhedral complexes "S-Q2=S-f(P(d))", if this is empty, S is contained in Q2.
return([T1,T2]);
}



/***********************************************************************************************************/
\\ STEP 3
\\ INPUT: [c,d] where [c,d]=[1/5,5] for m=8; [1/6,4] for m=10 and [1/8,2] for m=12

\\ OUTPUT: [c',d'] are positive constants
\\ such that P^{Delta,Delta}(c') \subset f(P^{Delta,Delta}(c) and 
\\ f(P^{Delta,Delta}(d)) \subset P^{Delta,Delta}(d')
\\ BASED ON LEMMA 15 OF OUR MANUSCRIPT (MS).

Bounds(S)=  
{my(P1,P2,P3,Q1,Q2,v,g1,g2,e,D1,D2,c,d,d1,d2);
d1=3; d2=3; 
[c,d]=S;
P1=Rtapprox2(1,d1); P2=Rtapprox2(1,d2); P3=-P2;
\\P1=[[1,0], [-1/2,866/1000], [-1/2,-866/1000]]; P2=P1; P3=-P2;
Q1=[[1,1],[-1,1],[-1,-1],[1,-1]];
Q2=[[1,0],[0,1],[-1,0],[0,-1]];
v=[lambda3([Q1,P3]), lambda3([Q1,P1]), lambda3([P1,Q2]), lambda3([P2,Q2])];
g1=(v[1]*(c*v[3]+v[4]))^(-1);
g2=c*(v[4]*(c*v[1]+v[2])+4*c)^(-1);
e=1/150; \\e<g1 and e<g2
D1=(c-e*(v[4]*(c*v[1]+v[2])+4*c))/(1+e*(v[3]*(c*v[1]+v[2])-4));
D2=(d+e*v[2]*(d*v[3]+v[4]))/(1-e*v[1]*(d*v[3]+v[4]));
return([D1,D2]); 
\\ LEMMA 15 OF MANUSCRIPT (MS):
\\ (i) if \varepsilon<g1, then f(P^{Delta,Delta}(d)) \subset P^{Delta,Delta}(d') 
\\ (ii) if \varepsilon<g2, then  P^{Delta,Delta}(c') \subset f(P^{Delta,Delta}(c)
}




/*******************************************************************************************************/
\\Subroutines used in CLAIM II.

kmultcomplex(u,C,pol)=   \\ multiplication of a unit (u) by the complex  C of semi-closed cones
{my(p,R,P,M);
p=pol;
R=vector(#C,j);
for(j=1,#C,
    P=[C[j][1],C[j][2]]; M=mulc(u,P,p); R[j]=concat(M,[C[j][3]]);
);
return(R);               \\ R=u*C as a complex of semiclosed cones
}

/** multiplication of one element "u" on K on the cone given as mod(polynomial) where the cone is given as V-repr and H-repr */
/*** INPUT: Given "u" in K */
/*** C=[C.generators,C.inequalities] */
/*** poli=polynomial defining the number field K */

/*** OUTPUT: return a new cone with this unit acting */ 

mulc(u,C,poli)=         
{my(A,B);
A=vector(#C[1],i,lift(Mod(u*C[1][i],poli)));       \\ multiplication of the unit u in the V-repr
A=vector(#A,i,A[i]/abs(content(A[i])));              \\ here we divide each entries by its abs(gcd(--)) > 0
B=vector(#C[2],i,lift(Mod(u^(-1)*C[2][i],poli)));  \\ multiplication of the unit u in the H-repr
B=vector(#B,i,B[i]/abs(content(B[i])));
return([A,B]);   \\ new representation of the cone u*C=[Generators,Inequalities]
}


/*******************************************************************************************************/
\\Subroutines used in STEP 1 (of CLAIM III)

KMat2(bnf,c,d1,d2)=  \\ c>0, d1>=3 and d2>=3 (d1 and d2 are integers)
{my(p,KB,Vr1,Vr2,M,D,g,f,zg,zf);
p=bnf.pol;
KB=Kapprox(bnf);  \\approximation k-rational of canonical basis of R^4
Vr1=Rtapprox2(1,d1);   \\ Polygon "\triangle"
Vr2=Rtapprox2(c,d2);   \\ Polygon "c^(-1)*\Gamma", so "\triangle x (c^(-1))*\Gamma"
M=vector(d2,j);
for(j=1,d2,
   D=vector(d1,j);
   g=Vr2[j];
   zg=Mod(g[1]*KB[3]+g[2]*KB[4],p);
   for(i=1,d1,
      f=Vr1[i];
      zf=Mod(f[1]*KB[1]+f[2]*KB[2],p);
      D[i]=lift(Mod(zf+zg,p));  
   );
   M[j]=D;
);
return([M,KB]);     \\ Here M represent the matrix with entries v[i,j] of size (d1)x(d2)
}

/*****************************************************************************/
/*                                                                           */
/*      "Kapprox(-)" compute a k-rational basis for R^4 sufficiently         */
/*         near to canonical basis e_1, e_2, e_3, e_4 of R^4.                */
/*****************************************************************************/
\p 1200
Kapprox(bnf)=    \\ Here return the Q-basis of elements in K=bnf which is near to canonical basis e_1,e_2,e_3,e_4 of R^4. 
{my(V,M); 
M=Tinvmat(bnf);
V=vector(4,j,Canoapp(bnf,M,j));
if(ncheck(V,bnf)[2]==0, warning("The four elements chosen aren't a K-rational basis for R^4"));
return(V);
}

Tinvmat(bnf)=
{my(Z,p,R,M,f);
Z=[1,x,x^2,x^3];
p=bnf.pol;
R=vector(4,j);
for(j=1,4,
f=Vec(conjvec(Mod(Z[j],p)));
R[j]=[real(f[1]),imag(f[1]),real(f[3]),imag(f[3])];
);
M=mattranspose(Mat(R~));
M=matsolve(M,matid(4));   \\ inverse of M
return(M);
}


Canoapp(bnf,M,h)=  \\Here h:=1,2,3,4
{my(p,B,a,l,Z);
Z=[1,x,x^2,x^3];
p=bnf.pol;
l=20;B=Vec(bestappr(M,l)); 
a=vecsum(vector(4,j,B[h][j]*Z[j]));
while(chbapprox(bnf,a,h)==0, l=l+5; B=Vec(bestappr(M,l)); a=vecsum(vector(4,j,B[h][j]*Z[j])); next);
return(a);
}

chbapprox(bnf,a,h)=   \\ Here check if the element a=e'_h obtained by bapprox(--) is to distance less than 1/150 from e_h (h=1,2,3,4)
{my(p,b,t);
p=bnf.pol;
b=conjvec(Mod(a,p));
b=[b[1],b[3]];
b=[real(b[1]),imag(b[1]),real(b[2]),imag(b[2])];
b[h]=b[h]-1;
if(abs(b[1])<1/150 && abs(b[2])<1/150 && abs(b[3])<1/150 && abs(b[4])<1/150, t=1, t=0);  \\ epsilon=1/150<=1/114
return(t);
}

ncheck(V,d)=
{my(nf,m,n,f,B,e);
m=#V;                  \\ V is a set of m elements of K.
n=d.r1+2*d.r2; nf=d.nf; f=0;
\\if(m>=n,
  B=vector(m,i,nfalgtobasis(nf,V[i])); B=Mat(B); e=matrank(B);
  if(e==n, f=1); 
\\  );
return([e,f]);          \\ f=1 means the set V contains n independent elements. f=0 otherwise. e=represent the dimension generated by V
}

Rtapprox2(c,d)= \\ c is small, c<=1, d>=3
{my(v,z,zr,l,B,w);
v=vector(d,j);
B=(1/100)*cos(Pi/d);
for(j=1,d,
z=c^(-1)*exp(I*(2*Pi*(j-1)/d)); \\ vertices of d-gon 
l=10000;zr=bestappr(z,l);
while(abs(z-zr)>=B, l=l+5; zr=bestappr(z,l); next);
v[j]=zr;
);
w=vector(d,j,[real(v[j]),imag(v[j])]); \\ rational vertices near to vertices of d-gon
return(w); \\Return a rational approximation to a regular d-gon of radius c^(-1)
}

/*******************************************************************************************************/
\\Subroutines used in STEP 2 (OF CLAIM III)

\\ Below bnf:=bnfinit(p), where p=minimimal polynomial of degree 4 which a defines to "bnf" as totally complex quartic field.
\\ kcomplex2(--) return a disjoint union of k-rational semiclosed 4-cones given S=complex of closed polyhedral cones

kcomplex2(S,bnf)= 
{my(P,C,q,h,a);
P=vector(#S,j,HV(S[j],bnf)); \\ here HV(--) is its representation as [generators, inequalities]
P=concat(P,[P[1]]);
C=vector(#S,j);
for(j=1,#P-1,
     q=setintersect(Set(P[j][2]),Set(-P[j+1][2]))[1]; 
     h=vfind(P[j][2],q);a=vector(#P[j][2],i,1); a[h]=-1;
     C[j]=concat(P[j],[a]);
);
return(C); 
\\Each semiclosed cone is given by [generators; ineqs; set signs +1 or -1], "+1" inequality is ">=", otherwise is ">"
}


\\ Below the routine:=kdcomplex(--) return the differences of a polyhedral complex with a polyhedral cone as a disjoint finite union of  polyhedral cones, this is given as a list of vectors of form [generators, inequalities, set of sign(+1 or -1)]

\\ Below bnf:=bnfinit(p).

kdcomplex(C,Q,bnf)=   \\ Here we obtain the difference between a complex C and a cone Q
{my(L,P,J,f,A,B,h,cert,S1,S2,S);
for(j=1,#C,
    P=C[j];           \\ semiclosed cone
    [J,f,h]=intCones2([P,Q],bnf);      \\ J=intersection between Q and P, f=1 means full-dim intersection 
    if(f==0 && h==0, C[j]=[P],      \\ f=0 means intersection less four but as h=0, not exist intersection of P and Q (return e=0)    
        [A,B]=kdiffCones(P,J,bnf); S=concat(A,B); if(#S>0, C[j]=S, C[j]=[]));
    );
L=concat(C);
return(L);
}


kdiffCones(P,Q,bnf)= \\ Pointed cones P and Q, where Q=P\cap P' is intersection of two cones given as: [genrs, ineqs, +/-1]
{my(D,v1,v2,A,S,w,a,h,B);
  v1=P[3];  \\ vector of signs +/-1
  v2=Q[3];  \\ vector of signs +/-1
  D=StrC([P,Q],bnf);
  D[1]=[D[1][1],D[1][2],concat(v1,-v2[1])];
  for(j=2,#D, w=concat(vector(j-1,i,v2[i]),-v2[j]); D[j]=[D[j][1],D[j][2],concat(v1,w)]);  
  A=[]; B=[];
  for(j=1,#D,
     S=D[j]; a=ncheck(S[1],bnf)[2];
     if(a==1, S=elimredun(S,bnf); A=concat(A,[S]));   \\full dimensional semiclosed cones
     if(a==0, h=vfyinclusion([S[1],S,P],bnf); if(h==1, B=concat(B,[S])));\\h=1 means exist a skinny cone in the difference of cones
    );
\\ C=[A,B] represents to P-Q as a disjoint union of full-dimensional semiclosed cones (A) with (possible) skinny cones (B).
\\ also A or B (or both) could be empty.
return([A,B]);     
}

/*****************************************************************************/
/*                                                                           */
/*     We verify if two Q-rational polyhedral cones of dimension n           */
/*                  intersect on its interior.                               */
/*                                                                           */
/*****************************************************************************/

intCones2(B,d)= \\ B=[Cone1, Cone2], Cone=[rays,ineqs,+/-1] a semiclosed cone ; d=bnfinit(p)
{my(H1,H2,H,s1,s2,s,J,f,h,a);
H1=B[1][2]; H2=B[2][2]; H=concat(H1,H2);
s1=B[1][3]; s2=B[2][3]; s=concat(s1,s2);
J=HV(H,d);           \\ #J[1]=0 mean the intersection between both cones is trivial = {Origen}
f=ncheck(J[2],d)[2];
if(f==0,   \\ f=0 means that the intersection J is not full-dimensional
  J=[J[2],J[1],s]; 
  if(#J[1]>0, h=vfyinclusion([J[1],B[1],B[2]],d), h=0);          
  );
if(f==1, J=elimredun([J[2],H,s],d); h=1); \\ if f=1, means that the intersection J is full-dimensional 
a=[J,f,h];
return(a);
}


vfyinclusion(D,d)=
{my(Q,C1,C2,v1,v2,s1,s2,L1,L2,g1,g2,a1,a2,h);
Q=D[1];     \\ we want to verify that Q=[Generators] is contained in boundary of C1 or C2 (semiclosed cones)
C1=D[2];    \\ [gens, ineqs, +/-1]
C2=D[3];    \\ [gens, ineqs, +/-1]
v1=[]; for(j=1,#C1[2], if(C1[3][j]==-1, v1=concat(v1,C1[2][j])));
v2=[]; for(j=1,#C2[2], if(C2[3][j]==-1, v2=concat(v2,C2[2][j])));
s1=vector(#v1,j,1);
for(j=1,#v1, 
    L1=v1[j]; \\ inequality
    g1=vector(#Q,i,nfelttrace(d.nf,L1*Q[i])); \\ verify if Q is contained in the halspace generate by L1 (open restriction of C1)
    if(g1==vector(#Q,i), s1[j]=0);
   );
s2=vector(#v2,j,1);
for(j=1,#v2, 
    L2=v2[j]; \\ inequality
    g2=vector(#Q,i,nfelttrace(d.nf,L2*Q[i])); \\ verify if Q is contained in the halspace generate by L2 (open restriction of C2)
    if(g2==vector(#Q,i), s2[j]=0);
   );
a1=prod(j=1,#s1,s1[j]); a2=prod(j=1,#s2,s2[j]);
if(a1==0 || a2==0, h=0, h=1); \\ h=0 means the cone Q is not contained in boundary of C1 or C2.
return(h);
}

\\ Eliminate redundant inequalities of semi-closed 4-cones:
\\ P=[R-repre. of closure(P), (closed or semi-closed) inequalities (H), vectors of signs +/-1], 
\\ +1="means H>=0", otherwise "means H>0"

elimredun(P,bnf)=
{my(nf,p,Q,H1,H2,Vp,certp,Vn,certn,Vpp,certpp,C,CoP,CoH,Cp1,Cn1,ineq,certp1,C1,Dn,Cn2,w,CoR,rs,Hn,C2,C3,Ry,Dim,dm,F2,F1,F0,rs1,Hn1,rs2,Hn2,rs3,Hn3);
nf=bnf.nf;
p=bnf.pol;
\\step 0: remove repeated inequalities, and if exist two ineqs of the form: "H>=0 and H>0", only consider the strict constraint "H>0"
Q=vector(#P[2],j, [P[2][j],P[3][j]]); \\ vectores [polymod, signs +/-1]
for(j=1,#Q, Q[j][1]=Q[j][1]/abs(content(Q[j][1]))); \\ normalization
H1=[v|v<-Q, v[2]==+1]; \\ list of ineqs>=0 in P
H2=[v|v<-Q, v[2]==-1]; \\ list of ineqs>0 in P
Vp=[]; for(j=1,#H1, certp=vfind(Vp,H1[j]); if(certp==0, Vp=concat(Vp,[H1[j]])));
Vn=[]; for(j=1,#H2, certn=vfind(Vn,H2[j]); if(certn==0, Vn=concat(Vn,[H2[j]])));
Vpp=[]; for(j=1,#Vp, certpp=vfind(Vn,[Vp[j][1],-1]); if(certpp==0, Vpp=concat(Vpp,[Vp[j]]))); \\ "H>=0 and H>0" implies "H>0"
C=concat(Vpp,Vn);      \\version of P without repeating inequalities.
\\step 1: obtains irredundant inequalities "> or >=" of P which defines a 3-face of the closure(P)
CoP=HV(P[1],bnf);      \\[R-repres, H-repres] representation of the closure(P)
CoH=CoP[2];            \\ list of irredundant ineqs in the closure(P)
Cp1=[]; Cn1=[];
for(j=1,#CoH, 
   ineq=CoH[j]; certp1=vfind(C,[ineq,1]);
   if(certp1==0, Cn1=concat(Cn1,[[ineq,-1]]), Cp1=concat(Cp1,[[ineq,+1]]) );
   );
C1=concat(Cp1,Cn1);  \\ version of P satisfying step 0 and 1
\\step 2: finally we need to see if is neccessary to add some inequalities ">" of P which defines an open e-face (with e<3) of P
Dn=[v|v<-Vn, vfind(Cn1,v)==0];  \\strict inequalities ">" no considered in "Cn1" contained in "Vn" (if Vn is no empty)
if(#Dn==0, C2=C1,
   Ry=vector(#Dn,j,[r|r<-CoP[1], nfelttrace(nf,Dn[j][1]*r)==0]);
   Dim=vector(#Dn,j,ncheck(Ry[j],bnf)[1]);
   dm=vector(3,i,[j|j<-[1..#Dn], Dim[j]==3-i]); \\possible [2-faces, 1-faces, 0-face (apex)] to remove in Closure(P)
   F2=vector(#dm[1],j,[Dn[dm[1][j]],Ry[dm[1][j]]]); 
   F1=vector(#dm[2],j,[Dn[dm[2][j]],Ry[dm[2][j]]]); 
   F0=vector(#dm[3],j,[Dn[dm[3][j]],Ry[dm[3][j]]]); \\ Union(F2[1],F1[1],F0[1])=Dn
   if(#dm[1]>0, \\2-faces
     for(j=1,#dm[1], rs1=lift(Mod(vecsum(F2[j][2]),p)); Hn1=vector(#Cn1,j,nfelttrace(nf,Cn1[j][1]*rs1));
         if(vfind(Hn1,0)==0, Cn1=concat(Cn1,[F2[j][1]])));
     );     
   if(#dm[2]>0, \\1-faces 
       for(j=1,#dm[2], rs2=lift(Mod(vecsum(F1[j][2]),p)); Hn2=vector(#Cn1,j,nfelttrace(nf,Cn1[j][1]*rs2));
         if(vfind(Hn2,0)==0, Cn1=concat(Cn1,[F1[j][1]])));
     );      
   if(#dm[3]>0,  \\0-faces
      for(j=1,#dm[3], rs3=lift(Mod(vecsum(F0[j][2]),p)); Hn3=vector(#Cn1,j,nfelttrace(nf,Cn1[j][1]*rs3));
         if(vfind(Hn3,0)==0, Cn1=concat(Cn1,[F0[j][1]])));
     ); 
  C2=concat(Cp1,Cn1);   
);
C3=[CoP[1],vector(#C2,j,C2[j][1]),vector(#C2,j,C2[j][2])];
return(C3); \\ Version with irredundant ineqs "> or >=" of the pointed 4-cone P
}

/*****************************************************************************/
/*                                                                           */
/*     Calculate the sustration of two Q-rational polyhedral cones           */
/*       of dimension n as union of cones not necessarily simplicials        */
/*                                                                           */
/*****************************************************************************/

/* Now we want to implemented an algorithm that allows us to find the different of two Q-rational polyhedral cone */
/* as (possibly empty) union of Q-rational  such polyhedral cones are not necessarily simplicials */

/*** INPUT: Given two cones C1 and C2 with intersection on their interiors */
/*** v=[v[1],v[2]]=[[R-rep.,H-rep.], [R-rep.,H-rep.]]; d=bnfinit(polynomial) */

/*** OUTPUT: return the difference of this two cones as finite union of cones */
/**** such that these cones only has intersection between their facets***/ 

StrC(v,d)=  
{my(N,D,w);
N=v[2][2];     \\ N is an H-repre. of v[2].
D=vector(#N);
D[1]=StrC1([v[1],[-N[1]]],d);
for(j=2,#N,
    w=vector(j,i,N[i]); w[j]=-N[j]; D[j]=StrC1([v[1],w],d);
    );
return(D); 
}
\\ Note: D are parts of the sustration of C1 with C2, this depend of order of the elements on N (H-representations of C2)
\\ and the number of part on this sustration D is at most #(ineqs) of C2. 



/*** INPUT: list of H-repres that we want to add at one cone given: */
/*** v=[v[1], v[2]], where v[1]=[R-rep.,H-rep.] a cone and v[2]=[List of H-rep(inequalities) that we want to add at cone v] */
/*** d=bnfinit(polynomial) */

/*** OUTPUT: new cone with this list added */ 

StrC1(v,d)=   
{my(H,C,L,R);
C=v[1][1]; \\ V-repre. of a cone
H=v[1][2]; \\ its H-repre.
L=v[2];    \\ these are H-reprs. that we want add to cone [C,H].
for(j=1,#L,
    R=AddC([L[j],C,H],d); 
    [C,H]=R;     \\ new cone V-repres. and H-repres.
    );
return([C,H]);  
}

\\ Below the routine:=HV(--) return its representation by generators of pointed K-(rational) cones from its description by inequalites
\\ and vice-versa when it is full-dimesional, where K:=bnfinit(polynomial), all free of redundancies.
\\ This is based on "the double description method (DDM) implemented by Fukuda-Prodon"
\\ WARNING: When working this algorithm? This working when the k-rational cone is full-dimensional (i.e. n=[K:Q]-dimensional) pointed
\\ or when the k-rational cone is pointed and given by inequalities (with possible redundances), then return its irredundant generators.
\\ BUT if it is given a pointed k-rational cone by generators, this algorithm not returns irredundant description by inequalities
/*****************************************************************************/
/*                                                                           */
/*     "HV" calculate an V-representation from its H-representation          */
/*         whose generators are in K_+ (and vice-versa by duality)           */
/*    (Here we use the method of Double Description Method "DDM")            */
/*              "BASED IN THE PAPER OF FUKUDA AND PRODON [FP96]"             */
/*****************************************************************************/
/* Given a number field K=bnfinit(polynomial)=Q(theta) */

/* This algorithm transforms an H-repr. into an irredundant V-repr. of a polyhedral cone if it is POINTED */
/* and conversely it also transforms a V-repre. into an irredundant H-repr. if the polyhedral cone is n-DIMENSIONAL */

/*** INPUT: v=[v_1,v_2...v_e] is a collection of elements in K (number field)    */
/*** which define an H-repres (respectively V-represen) of an n-dimensional pointed polyhedral cone P */
/*** d:=bnfinit(polynomial) data given by Pari/gp */

/*** Recall that: v define a V-represen. for P, if P=C[v_1,v_2,...,v_e]:={sum_{j}t_jv_j: t_j=>0} */
/*** and v define an H-represen. for P, if P=H(L_1,...L_e):={x in X: L_j(x)=tr(v_jx) =>0} (intersection of halfspaces), X=R^(r1)*C^(r2)*/


/*** OUTPUT: A pair [H-represen.,V-represen.(irredudant)] (respectively [V-represen.,H-repr.(irredundant)]) description for P */ 

HV(v,d)=  \\ v define an H-representation (respec. V-repren.) of an n-dimensional POINTED cone.
{my(w,S,L,R); 
w=check(v,d);     \\ taking a subset of n independent linear vectors on V_Q in the set v. (w subcollections of H-reprs.)
S=HV1(w,d);       \\ transformation of w on a V-repr.
L=[g|g<-v, vfind(w,g)==0];     \\these are the H-reprs. that we want add to the  cone w (or S)
for(j=1,#L,
    R=AddC([L[j],S,w],d);  \\ add H-repr. L[j] to the V-repr. initial S=HV1(T[1],d).
    [S,w]=R;
    );
return([v,S]);  \\ we note that if v is an H-repre (respec. V-repre) then S is V-repre (respec. H-repre) with S is irredundant ("By duality").
}

/**************************************************************************/
/* HV1 is to the case when the cone is a  "simplicial n-dimensional cone" */
/*** INPUT: S=simplicial cone (n=[k:Q])-dimensional with a V-represention (H-representation) whose generators are in K; d=bnfinit(poly) */

/*** OUTPUT: H= is an H-reprentation (V-representation) of the SIMPLICIAL n-dimensional cone S  */

HV1(S,d)=          
{my(nf,H,L,n,a);     
n=d.r1+2*d.r2;             \\n=[K:Q]
nf=d.nf; L=matrix(n,n, i,j, nfelttrace(nf,S[i]*S[j]));
H=matsolve(L,matid(n));   \\ inverse of the matrix L
H=Vec(H);
for(j=1,#H,
   a=vecsum(vector(n,i,Vec(H[j])[i]*S[i]));    \\ return a polymod which define the H-repr(V-repr) of S.
   H[j]=a/abs(content(a));
   );
return(H);         \\ when S is a V-repr.(H-repr.) of the cone then  H is an H-repr.(V-repr.) V ("By duality").
}

/*** INPUT: V is set of elements in k not necessarily independent, d=bnfinit(poly) */
/*** OUTPUT: E a subset (of V) of n independent elements over Q  */ 

check(V,d)= 
{my(nf,m,n,B,C,D,E);
m=#V;               \\ V is a set of m elements of K (m>=n).
n=d.r1+2*d.r2; nf=d.nf;
if(m>=n,
  B=vector(m,i,nfalgtobasis(nf,V[i])); B=mattranspose(Mat(B));
    if(matrank(B)==n,
        C=matindexrank(B); D=vecextract(B,C[1],C[2]); D=Vec(mattranspose(D)); E=vector(#D);
        for(j=1,#D, E[j]=lift(nfbasistoalg(nf,D[j])));
       );
  );
return(E);
\\E is a subset of n vectors on V independent linear in V_Q. If E=0 then the set given have no "n" elements independent. 
}

/*Algorithm for verify when two (extreme) rays (v1,v2) in P(A) are neighbour or adjacent on P(A):=[w_1,...,w_m]:={x : tr(w_jx) >= 0} given*/
/*** INPUT: Given two rays v1 and v2 on a polyhedral cone P(A)=H-representation */ 
/*** T=[[v1,v2],P(A)] is a triple; d=bnfinit(k) */

/*** OUTPUT: return 1 if both rays generate a 2-dimensional face on the cone P(A), 0 otherwise */ 

nbour(T,d)=         
{my(nf,v1,v2,A,S,n,Z1,Z2,Z,B,C,f);
[v1,v2]=T[1]; A=T[2];     \\ all the elements of A be in K (warning!: here is necessary that P(A) be an H-representation)
S=[1..#A]; n=d.r1+2*d.r2; nf=d.nf;
Z1=[j|j<-S, nfelttrace(nf,A[j]*v1)==0]; \\ zone of zeros of ray v1
Z2=[j|j<-S, nfelttrace(nf,A[j]*v2)==0]; \\ zone of zeros of ray v2
Z=setintersect(Z1,Z2);    \\ because Z1 and Z2 are sets.
f=0;
if(#Z>=(n-2),          \\ If Z1 and Z2 are adjacent then Z has at least n-2 elements. 
   B=vecextract(A,Z);  \\ extracting the entries of vector A correspondiente to position on Z
   C=vector(#B,i,nfalgtobasis(nf,B[i])); C=Mat(C);
   if(matrank(C)==n-2, f=1);
  );
return(f);             \\f=1 means that the rays v1 and v2 are neighbour (or adjacent) on the polyhedral P(A).
}


/* Adding some restriction [w]: tr(wx) => 0, w\in k, of a pair (R;L) given , where L is an H-repr. and R thus V-repr. of L */
/*** INPUT: v=[w,R,L], where w is a inequality "tr(wx) => 0" and [R,L]=[V-representation,H-representation] is a cone given*/
/*** d= bnfinit(poly) */

/*** OUTPUT: return a new cone with this inequality added */ 

AddC(v,d)=         
{my(nf,w,R,L,Rp,Rn,R0,T,S,ray,e,f);
nf=d.nf;
[w,R,L]=v;
Rp=[r|r<-R, nfelttrace(nf,w*r)>0];   \\ set of positive rays on R respect to hyperplane "tr(wx)=0" generated by the restriction.
Rn=[r|r<-R, nfelttrace(nf,w*r)<0];   \\ similarly (negative rays)
R0=[r|r<-R, nfelttrace(nf,w*r)==0];  \\ similarly (zero rays)
T=[[a,b]|a<-Rp;b<-Rn];               \\ this is the set of pairs of rays positives and negatives respect to restriction "tr(wx)"
if(#T==0,S=[], T=[ad|ad<-T, nbour([ad,L],d)==1];  \\ here we consider only the adjacent pairs.
    S=vector(#T,j);
    for(j=1,#T, e=T[j][1]; f=T[j][2]; ray=nfelttrace(nf,w*e)*f-nfelttrace(nf,w*f)*e; S[j]=ray/abs(content(ray)));
  );
L=concat(L,[w]);
R=concat(concat(Rp,R0),S); \\ new V-representation of P after add the restriction w.
return([R,L]);   \\ new V-repr (without redundancies) and H-repr of the cone when we add the restriction w. (Here L could have some redudances)
}

/*** INPUT: given a vector(v) and a element (elmnt)  */
/*** OUTPUT: verify if such element is in the vector given  */ 

vfind(v,elmnt)=
{my(l);
l=0;
for(j=1,length(v),
    if(v[j]==elmnt,l=j; break(1));   \\ comparation between two polymods if such elements belongs to a number field.
   );
return(l); \\it is the l-th position of vector v where is "elmnt", if l=0 then v not contain "elmnt" 
}



/*******************************************************************************************************/
\\Subroutines used in STEP 3 (OF CLAIM III)

lambda1(S)= \\S=[w,[v1,v2]]=[Point, segment]
{my(v1,v2,w,M,R);
[v1,v2]=S[2]; w=S[1]; \\ v1,v2,w vectors in Q^2
M=Mat([w~,(v1-v2)~]);
if(matdet(M)==0, R=[0,0],
R=matsolve(M,v1~); 
R=[R[1]^(-1),R[2]]);
return(R); 
\\here R=[lambda, t] where the scalars (lambda,t) should be positive with t in [0,1], since we are looking: lambda^(-1)w=t*v1+(1-t)*v2
}

lambda2(S)= \\S=[Point, Polygon]
{my(P,w,AA,v);
P=S[2]; \\S=[v_1,v_2....v_d] consecutive vertices
w=S[1];
AA=concat(vector(#P-1,j,[P[j],P[j+1]]),[[P[#P],P[1]]]); \\ set of all the aristas of polygon P
v=vector(#P,j,lambda1([w,AA[j]]));
v=[e|e<-v, e[1]>0 && e[2]>=0 && e[2]<=1];
return(v);
}


lambda3(S)= \\S=[Polygon1, Polygon2]
{my(P1,P2,L);
P1=S[1]; P2=S[2];
L=[];
for(j=1,#P1,
   L=concat(L,lambda2([P1[j],P2]));
   );
L=vector(#L,j,L[j][1]); L=vecmax(L);
return(L); \\lambda^(S[1])_(S[2])
}





\\ Given the set L of polynomials L=[x^4+1, x^4-x^3+x^2-x+1, x^4-x^2+1] as INPUT.
\\ The follows routine created a file which verify:
\\ f(P^{Delta,Delta}(c)) \subset S \subset f(P^{Delta,Delta}(d))

CyclotomicComplexes(L)= 
{my(v,a,b,k,p,A,R,m,w,v1,h1,h2,l,S,S1,Q1,Q2,SCineq,SCgen,QCineq1,QCgen1,QCineq2,QCgen2);
v=vector(3,j);
a=[1/5,1/6,1/8]; 
b=[5,4,2];
for(j=1,3, 
    k=bnfinit(L[j]); p=k.pol;
    [A,R]=ApproxRComplex(k,a[j],b[j]); 
    [m,w]=[k.tu[1],lift(k.tu[2])]; \\ order of torsion m=8, 10, 12, whose generator is "w"
    v1=precision(conjvec(Mod(w,p)),10000); 
    [h1,h2]=abs(arg([v1[1],v1[3]]))*(m/(2*Pi)); [h1,h2]=ceil([h1,h2]); l=vecmax([h1,h2]);
    if([h1,h2]==[1,l], w=lift(Mod(w^l,p)));
    S=vector(m,j,lift(Mod(w^(j-1)*[1,w,w^2,w^3],p)));
    S1=kcomplex2(S,k);
    Q1=kcomplex2(A,k); \\Q1 represent an attractor: Q1 \subset S1
    Q2=kcomplex2(R,k); \\Q2 represent a repulsor: S1 \subset Q2
    SCineq=vector(m,i,vector(#S1[i][2],j,[S1[i][2][j],S1[i][3][j]]));\\[inequality,+ or -1],"+1" means ">=0"; "-1" means">0"
    SCgen=vector(m,i,S1[i][1]); \\ list of cones given generators which represent the closure of the cones in "Cineq"
    QCineq1=vector(#Q1,i,vector(#Q1[i][2],j,[Q1[i][2][j],Q1[i][3][j]]));
    QCgen1=vector(#Q1,i,Q1[i][1]); 
    QCineq2=vector(#Q2,i,vector(#Q2[i][2],j,[Q2[i][2][j],Q2[i][3][j]]));
    QCgen2=vector(#Q2,i,Q2[i][1]); 
    v[j]=[[p,w,m], SCineq, SCgen, QCineq1, QCgen1, QCineq2, QCgen2];
    );
\\return(v);
write(Cyclotomicc,"data = ", v, ";");
}

