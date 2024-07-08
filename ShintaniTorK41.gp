\\ update june 2024

\\ Input: Let p be an irreducible quartic polynomial which defines a totally complex quartic field k.

\\ Output: F=FD(p,t), where t=order of the torsion group of k.

torFDK41(p)= 
{my(k,t,F);
k=bnfinit(p); t=k.tu[1];
F=FD(p,t); 
\\ you can also to determine a Shintani domain for a torsion subgroup, putting a divisor of t
return(F);
}



/***********************************************************************************************/
\\ Shintani domains for totally complex quartic number fields k with torsion subgroup of order m

\\ Input: p= a polymod which defines a totally complex quartic number field
\\        m= a natural number which represents the order of torsion subgroup <w>, whose posible values of m are 1,2,3,4,5,6,8,10,12

\\ Output: A Shintani Fundamental domain for the action of group G=T*<E>=<w>*<E> acting on (C*)^2
\\  if m=1, then this returns a Shintani domain for a torsion-free subgroup of the units group of k.

FD(p,m)=
{my(k,E,v,v1,t,w,w1,wp,rg,e,F,S,C1,r,ut,C2,T,L,f,tm,a,d,Cineq,Cgen,h1,h2,D,dim,Df,mr,Cineq1,Cineq2,Cgen1,Cgen2);
tm=getwalltime();
k=bnfinit(p,1);   \\ flag=1
E=topu(k)[1]; v=conjvec(Mod(E,p)); if(abs(v[1])>1, E=lift(Mod(E^(-1),p)));   \\ <E> free part of the group G, with abs(E[1])<1
[t,w]=[k.tu[1],lift(k.tu[2])];    \\[order of torsion, generator of torsion group of k]
rg=precision(k.reg,10);
e=t/m;
if(type(e)=="t_INT" && m>0 && type(m)=="t_INT",
if(m==1,F=FDK41(p),  \\here FDK41 return a Shintani domain for free-torsion groups G=<E> of the units group of k
   S=TorAttractor(k);
   C1=kcomplex(S,k);
   if(t==2 || t==4, if(rg>0.802, r=1, r=3));
   if(t==6, if(rg>0.405, r=1, r=2));
   if(t==8 || t==12, r=3);
   if(t==10, r=4);
   if(t==8 || t==10 || t==12, v1=conjvec(Mod(x,p)); [h1,h2]=[abs(arg(v1[1])),abs(arg(v1[3]))]*(t/(2*Pi)); [h1,h2]=ceil([h1,h2]);
      if([h1,h2]==[1,3] || [h1,h2]==[1,5],  E=lift(Mod(E^(-1),p))); \\ with abs(E[1])>1
    );
   if(r>1,[Df,mr]=minr(C1,E,r,k),[Df,mr]=[vector(r,j,[]),1]);
   ut=vector(mr,j,lift(Mod(E^(j),p)));    \\ vector of power of the unit u: u,u^2,u^3,...,u^(mr)
   C2=vector(mr,j,kmultcomplex(ut[j],C1,p)); C2=concat(C2);
   if(t==2, f=2, f=1);
   T=vector(f,j);
   for(j=1,f,
      L=[C1[j]];
      for(i=1,#C2, L=kdcomplex(L,C2[i],k));
      T[j]=L;
      );
  T=concat(T); 
  if(e==1, w1=w);
  if(e>1, w1=lift(Mod(w^(e),p));
  wp=vector(e,j,lift(Mod(w^(j-1),p)));
  T=concat(vector(e,j,kmultcomplex(wp[j],T,p)));
   );
  a=#T;
  tm=getwalltime()-tm; 
  D=vector(a,j,ncheck(T[j][1],k));
  dim=vector(4,j,#[e|e<-D, e[1]==4-j+1]);  \\ vector with information of [#4-cones, #3-cones, #2-cones, #1-cones] in the difference "F".
  d=[tm, p, rg, k.disc, [[t,w],[m,w1]], E, r,mr, a, dim];
  Cineq=vector(a,i,vector(#T[i][2],j,[T[i][2][j],T[i][3][j]])); \\ [inequality, + or -1], "+1" means ">=0"; "-1" means ">0"
  Cgen=vector(a,i,T[i][1]); \\ list of cones given generators which represent the closure of the cones in "Cineq"
  Cineq1=[]; Cgen1=[]; Cineq2=[]; Cgen2=[];
  for(j=1,a,
  if(ncheck(Cgen[j],k)[2]==1, Cineq1=concat(Cineq1,[Cineq[j]]); Cgen1=concat(Cgen1,[Cgen[j]]),
                              Cineq2=concat(Cineq2,[Cineq[j]]); Cgen2=concat(Cgen2,[Cgen[j]]));
   );
  Cineq=concat(Cineq1,Cineq2); Cgen=concat(Cgen1,Cgen2);
  F=[d, Cineq, Cgen]),
  \\F=[d,T]),
  warning("...The number entered " m " must be a natural number and divide the order of the torsion group, which is " t ".");
);
return(F);
}


/*****************************************************************************************************************/
TorshK41(S)= \\S=list of totally complex quartic polynomials
{my(t1,F,D);
for(j=1,#S,
   t1=getwalltime();
   F=torFDK41(S[j]);
   D=datatorSK41(F);
   write(dataTorSK41,"",D,""); \\ return an archive with the information obtaind by "datatorSK41(--)" of all field in S
   print1([[j],getwalltime()-t1]);
  );
}

datatorSK41(S)=  \\where S=torFDK41(poly)=vectors of size 3
{my(Cineq,Cgen,z,D,c,a1,a2,e,bnf,p,Cineq1,Cgen1,z1,c1);
Cineq=S[2]; z=#Cineq; 
Cgen=S[3]; D=vector(5,j); c=vector(z,j,[#Cgen[j],#Cineq[j]]); D[5]=c;
p=S[1][2]; bnf=bnfinit(p);
if(S[1][9]==S[1][10][1], \\#Cones==#(4-cones)????
   D[1]=1; 
   a1=vector(z,j,#HV(Cgen[j],bnf)[2]); a2=vector(z,j,#Cineq[j]);
   if(a1==a2, e=1, e=0); 
   D[2]=concat([e],S[1]);
   D[3]=[vecmax(vector(z,j,#Cgen[j])),vecmax(vector(z,j,#Cineq[j]))];\\[maximal # of generators (in closure), and inequalities (> or >=)]
   D[4]=precision(exp(log(vecsum(c)/#c)),5),
   D[1]=0; 
   Cineq1=[]; Cgen1=[]; 
   for(j=1,z, if(ncheck(Cgen[j],bnf)[2]==1, Cineq1=concat(Cineq1,[Cineq[j]]); Cgen1=concat(Cgen1,[Cgen[j]]))); 
   \\ Cineq1 and Cgen1 only consider 4-cones in the list of cones given in Cineq
   z1=#Cineq1; a1=vector(z1,j,#HV(Cgen1[j],bnf)[2]); a2=vector(z1,j,#Cineq1[j]);
   if(a1==a2, e=1, e=0); D[2]=concat([e],S[1]);
   D[3]=[vecmax(vector(z1,j,#Cgen1[j])),vecmax(vector(z1,j,#Cineq1[j]))];\\[maximal # of generators (in closure); inequalities (> or >=)]
   c1=vector(z1,j,[#Cgen1[j],#Cineq1[j]]);
   D[4]=precision(exp(log(vecsum(c1)/#c1)),5);
   );
return(D); \\D is a vector of size five
}

minr(S,E,r,k)= \\ we want to determine the minimum r' such that E^(r')*S is contained in S for r' in [1..r]
{my(mr,p,Df,u,Q,T,L,v,a);
   p=k.pol;
   Df=vector(r,j);
   for(h=1,r,
   u=lift(Mod(E^h,p)); Q=kmultcomplex(u,S,p); 
   T=vector(#Q,j);
   for(j=1,#Q,
      L=[Q[j]];
      for(i=1,#S, L=kdcomplex(L,S[i],k));
      T[j]=L;
      );
   Df[h]=concat(T); \\ E^(h)*S-S
   );
v=vector(r,j,#Df[j]); a=vfind(v,0);
return([Df,a]);
}

/******************************************************************************************************************************/
\\ Below the routine:=kdcomplex(--) return the differences of a polyhedral complex with a polyhedral cone as a disjoint finite union of  polyhedral cones, this is given as a list of vectors of form [generators, inequalities, set of sign(+1 or -1)]

\\ Below bnf:=bnfinit(p).

kdcomplex(C,Q,bnf)=   \\ Here we obtain the difference between a complex C and a cone Q
{my(L,P,J,f,A,B,h,cert,S1,S2,S);
for(j=1,#C,
    P=C[j];           \\ semiclosed cone
    [J,f,h]=intCones2([P,Q],bnf);      \\ J=intersection between Q and P, f=1 means full-dim intersection 
    \\if(f==0 && h==0, C[j]=[P],      \\ f=0 means intersection less four but as h=0, not exist intersection of P and Q (return e=0)    
    \\    [A,B]=kdiffCones(P,J,bnf); S=concat(A,B); if(#S>0, C[j]=S, C[j]=[]));
    if(f==0 && h==0, C[j]=[P]);
    if(f==0 && h==1, [A,B]=kdiffCones(P,Q,bnf); S=concat(A,B); if(#S>0, C[j]=S, C[j]=[]));
    if(f==1 && h==1, [A,B]=kdiffCones(P,J,bnf); S=concat(A,B); if(#S>0, C[j]=S, C[j]=[]));
    );
if(#C>0,L=concat(C),L=[]);
return(L);
}


kdiffCones(P,Q,bnf)= \\ given two pointed cones P and Q given as: [genrs, ineqs, +/-1]
{my(D,v1,v2,A,S,w,a,h,B);
  v1=P[3]; \\ vector of signs +/-1
  v2=Q[3];  \\ vector of signs +/-1
  D=StrC([P,Q],bnf);
  D[1]=[D[1][1],D[1][2],concat(v1,-v2[1])];
  for(j=2,#D, w=concat(vector(j-1,i,v2[i]),-v2[j]); D[j]=[D[j][1],D[j][2],concat(v1,w)]);  
  D=[e|e<-D, #e[1]>0]; \\remove the trivial (empty) cones.
  A=[]; B=[];
  for(j=1,#D,
     S=D[j]; a=ncheck(S[1],bnf)[2];
     if(a==1, S=elimredun(S,bnf); A=concat(A,[S]));    \\full dimensional semiclosed cones
     if(a==0, h=vfyinclusion([S[1],S,P],bnf); if(h==1, B=concat(B,[S])));   \\ h=1 means exist a skinny cone in the difference of cones
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
\\ P=[R-repre. of closure(P), (closed or semi-closed) inequalities (H), vectors of signs +/-1], +1="means H>=0", otherwise "means H>0"
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

/***********************************************************************************************************************/
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
return([A,B]);       \\ new representation of the cone u*C=[Generators,Inequalities]
}


/********************************************************************************************************/
/*                                                                                                      */
/*     the routine:=kcomplex(--) below returns the complex C:=\cup_{1<=j<=g}C_j of polyhedral 4-cones   */
/*      which represents the vertices of prims with regular d-polygons in its base, taking d=g>=3.      */
/*        Where the cones are given as C_j:=[generators, (semi)-closed inequalities, sign(+1 or -1)]    */
/*                                                                                                      */
/********************************************************************************************************/

\\ Below bnf:=bnfinit(p), where p=minimimal polynomial of degree 4 which a defines to "bnf" as totally complex quartic field.

kcomplex(S,bnf)=  \\ Here S is an attractor complex obtained below is union of k-rational 4-cones
{my(P,C,q,h,a,g,hf,tr);
P=vector(#S,j,HV(S[j],bnf)); \\ here HV(--) is its representation as [generators, inequalities]
P=concat(P,[P[1]]);
C=vector(#S,j);
for(j=1,#P-1,
     \\q=setintersect(Set(P[j][2]),Set(-P[j+1][2]))[1]; 
     g=setintersect(Set(P[j][1]),Set(P[j+1][1])); \\ intersection of generators of the cones P[j] and P[j+1]
     hf=P[j][2]; tr=vector(#hf,i,vecsum(vector(#g,j,nfelttrace(bnf.nf,g[j]*hf[i])))); h=vfind(tr,0);
     \\h=vfind(P[j][2],q); 
     a=vector(#P[j][2],i,1); a[h]=-1;
     C[j]=concat(P[j],[a]);
);
return(C); \\ Here each semiclosed cone is given by [generators; ineqs; set signs +1 or -1], "+1" inequality is ">=", otherwise is ">"
}

TorAttractor(bnf)= \\ t=2,4,6,8,10,12 (considering the torsion group)
{my(k,p,b,t,w,S,C0);
k=bnf; p=k.pol;
b=Kapprox(k); \\b=[tilde(e_1),tilde(e_2),tilde(e_3),tilde(e_4)]
[t,w]=[k.tu[1],lift(k.tu[2])];  \\[order of torsion, generator of torsion group of k]
if(t==2, S=Attractor(k,4)[1]);   \\ S= union of four polyhedral 4-cones with 8 generators and 6 inequalities
if(t==4 || t==6, C0=concat(vector(t,j,lift(Mod(w^(j-1)*b[1]+b[3],p))),vector(t,j,lift(Mod(w^(j-1)*b[1]+w*b[3],p))));
   S=vector(t,j,lift(Mod(w^(j-1)*C0,p))); \\ S= union of t polyhedral 4-cones with 2*t generators and 2+t inequalities
   for(j=1,t, S[j]=vector(2*t,i,S[j][i]/abs(content(S[j][i])))));
if(t==8 || t==10 || t==12, C0=[1,x,x^2,x^3];
   S=vector(t,j,lift(Mod(w^(j-1)*C0,p)));  \\ S= union of t polyhedral 4-cones with four generators and four inequalities
   for(j=1,t, S[j]=vector(4,i,S[j][i]/abs(content(S[j][i]))));
   );
return(S);
}

Attractor(bnf,d)=  
{my(M,S,C,KB);
[M,KB]=KMat(bnf,d);     \\ list of "d" columns vector of size "d" and KB=k-rational basis near to canonical basis of R^4
S=vector(d,j);
for(e=1,d-1, S[e]=concat(M[e],M[e+1]));
S[d]=concat(M[d],M[1]);
for(j=1,d, 
    C=S[j];
    S[j]=vector(2*d,i,C[i]/abs(content(C[i])));
);
return([S,KB]); \\ Here attractor S which represent a complex of d full-dim. k-rational cones with 2d vertices
}



KMat(bnf,d)=
{my(p,Br,Vr,W,D,g,f,zg,zf);
p=bnf.pol;
Br=Kapprox(bnf);  \\ comes from step 1, #Br=4
Vr=Rtapprox(d);   \\ comes from step 2, #Vr=d
W=vector(d,j);
for(j=1,d,
   D=vector(d,j);
   g=Vr[j];
   zg=Mod(g[1]*Br[3]+g[2]*+Br[4],p);
   for(i=1,d,
      f=Vr[i];
      zf=Mod(f[1]*Br[1]+f[2]*Br[2],p);
      D[i]=lift(Mod(zf+zg,p));
   );
   W[j]=D;
);
return([W,Br]);     \\ Here W represent the matrix with entries v[i,j]
}

Rtapprox(d)= 
{my(v,z,zr,l,B,w);
v=vector(d,j);
B=(1/100)*cos(Pi/d);
for(j=1,d,
z=exp(I*(2*Pi*(j-1)/d)); \\ vertices of d-gon 
l=10000;zr=bestappr(z,l);
while(abs(z-zr)>=B, l=l+5; zr=bestappr(z,l); next);
v[j]=zr;
);
w=vector(d,j,[real(v[j]),imag(v[j])]); \\ rational vertices near to vertices of d-gon
return(w); \\Return a rational approximation to a regular d-gon
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

Canoapp(bnf,M,h)=  \\Here h:=1,2,3,4
{my(p,B,a,l,Z);
Z=[1,x,x^2,x^3];
p=bnf.pol;
l=20;B=Vec(bestappr(M,l)); 
a=vecsum(vector(4,j,B[h][j]*Z[j]));
while(chbapprox(bnf,a,h)==0, l=l+5; B=Vec(bestappr(M,l)); a=vecsum(vector(4,j,B[h][j]*Z[j])); next);
return(a);
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


chbapprox(bnf,a,h)=   \\ Here check if the element a=e'_h obtained by bapprox(--) is to distance less than 1/150 from e_h (h=1,2,3,4)
{my(p,b,t);
p=bnf.pol;
b=conjvec(Mod(a,p));
b=[b[1],b[3]];
b=[real(b[1]),imag(b[1]),real(b[2]),imag(b[2])];
b[h]=b[h]-1;
if(abs(b[1])<=1/150 && abs(b[2])<=1/150 && abs(b[3])<=1/150 && abs(b[4])<=1/150, t=1, t=0);  \\ epsilon=1/150<=1/114
return(t);
}

ncheck(V,bnf)=
{my(nf,m,n,f,B,e,r1,r2);
m=#V;                  \\ V is a set of m elements of K.
[r1,r2]=bnf.sign; n=r1+2*(r2); nf=bnf.nf; f=0;
\\if(m>=n,
  B=vector(m,i,nfalgtobasis(nf,V[i])); B=Mat(B); e=matrank(B);
  if(e==n, f=1); 
\\  );
return([e,f]);          \\ f=1 means the set V contains n independent elements. f=0 otherwise. e=represent the dimension generated by V
}


\\ Below the routine:=HV(--) return its representation by generators of pointed K-(rational) cones from its description by inequalites
\\ and vice-versa when it is full-dimesional, where K:=bnfinit(polynomial), all free of redundances.
\\ This is based on "the double description method (DDM) implemented by Fukuda-Prodon"
\\ WARNING: When working this algorithm? This working when the K-cone is full-dimensional (i.e. n=[K:Q]-dimensional) pointed
\\ or when the K-cone is pointed and given by inequalities (with possible redundances), then return its irredundant generators.
\\ but if it is given a pointed K-cone by generators, this algorithm not returns irredundant description by inequalities


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



/*** INPUT: V is set of elements in K not necessarily independents, d=bnfinit(poly) */
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
return(E);    \\ E is a subset of n vectors on v independent linear in V_Q. If E=0 then the set given have no "n" elements independent. 
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

/********************************************************************************************************/
/*** Shintani domains for torsion-free totally complex quartic number fields k *******************/
/*** developed in 2023 ***/

FDK41(p)= \\ p is a which defines a totally complex quartic number field
{my(K,u,r,S,C1,C2,ut,C3,Qr,T,L,a,c,Cineq,Cgen,V,tim1,D,dim,KB);
tim1=getwalltime();
 K=bnfinit(p,1); \\ flag=1
 [u,r]=Runits(p)[1];   \\ r>=1, u=fundamental unit given by PARI/GP
 [S,KB]=Attractor(K,3);     \\ d>=3, KB=K-basis of dimension 4
 C1=kcomplex(S,K); 
 if(r>1,
   C2=kmultcomplex(u,C1,p);    \\ multiplication of complex Q:=C1 by the unit u
   ut=vector(r-1,j,lift(Mod(u^(j+1),p)));    \\ vector of power of the unit u: u^2,u^3,...,u^r
   C3=vector(r-1,j,kmultcomplex(ut[j],C1,p)); Qr=C3[r-1];  \\ Qr:=u^r*Q which is contained in Q
   C3=concat(C3);
   C2=concat(C2,C3), C2=kmultcomplex(u,C1,p); Qr=C2);
 T=vector(#C1,j);
 for(j=1,#C1,
    L=[C1[j]];
    for(i=1,#C2, L=kdcomplex(L,C2[i],K));
    T[j]=L;
    );
T=concat(T); 
a=#T;     \\This just is the number of cones obtained of difference F:=Q-(u*Q,u^2*Q,---,u^r*Q) (possibly some cone of dimension<4)
tim1=getwalltime()-tim1; 
\\D=vector(a,j,ncheck(T[j][1],K));
\\dim=vector(4,j,#[e|e<-D, e[1]==4-j+1]);  \\ vector with information of [#4-cones, #3-cones, #2-cones, #1-cones] in the difference "F".
\\ c=[tim1, p, precision(K.reg,10), K.disc, u, r, a, dim];
c=[tim1, p, precision(K.reg,10), K.disc, u, r, a];
Cineq=vector(a,i,vector(#T[i][2],j,[T[i][2][j],T[i][3][j]])); \\ [inequality, + or -1], "+1" means ">=0"; "-1" means ">0"
Cgen=vector(a,i,T[i][1]); \\ list of cones given generators which represent the closure of the cones in "Cineq"
V=[c, KB, Cineq, Cgen]; 
return(V); \\ V=data of the shintani domain of number field generated by the polynomial"p" which contains 4 entries
}



Runits(p)=
{my(u,bnf,Disck,m,t,T,v,S,a,f,b,D);
bnf=bnfinit(p,1);
Disck=bnf.disc;
u=topu(bnf)[1]; 
t=lift(bnf.tu[2]); \\ generator of torsion group
m=bnf.tu[1]; \\ order of torsion group
T=[lift(Mod(t^j,p))| j<-[0..m-1]];
v=conjvec(Mod(u,p));
if(abs(v[1])>1, u=lift(Mod(u^(-1),p)); v=conjvec(Mod(u,p)));
a=abs(v[1]^2);
f=floor(log(0.184)/log(a));
if(a<0.184 || Disck>=223503, D=[[u,1]],
   S=[[lift(Mod(u^j,p)),ceil(log(0.184)/log(a^j))]| j<-[1..f]];
   D=vector(m,j);
   for(j=1,m,
      b=T[j];
      D[j]=[[lift(Mod(s[1]*b,p)),s[2]]| s<-S];
      );   
   D=concat(D);
   \\D=concat([[p,m,f]],D);
   );
return(D);
}


/*******************************************************************************************/
/*                                                                                         */
/*   Calculate of generator of the totally positive units group of a number field          */
/*                 (code established in the Manual Pari/gp)                                */
/*                                                                                         */
/*******************************************************************************************/

/* exponents of totally positive units generators on bnf.tufu */

tpuexpo(bnf)=
{my(K, S = bnfsignunit(bnf), [m,n] = matsize(S)); \\ m = bnf.r1, n = r1+r2-1
S = matrix(m,n, i,j, if (S[i,j] < 0, 1,0));
S = concat(vectorv(m,i,1), S); \\ add sign(-1)
K = matker(S * Mod(1,2));
if (K, mathnfmodid(lift(K), 2), 2*matid(n+1));
}

/* totally positive fundamental units (with a representation on integral basis) */
/*** INPUT: bnf=bnfinit(p) */
/*** OUTPUT: Totally positive fund'l units with representation on its integral basis */ 

tpu(bnf)=
{ my(ex = tpuexpo(bnf)[,2..-1]); \\ remove ex[,1], corresponds to 1 or -1
vector(#ex, i, nffactorback(bnf, concat(Mod(bnf.tu[2],bnf.pol),bnf.fu), ex[,i])); \\bnf.tufu=[bnf.tu,bnf.fu]
}

/*totally positive fundamental units*/
/*** INPUT: bnf=bnfinit(p) */
/*** OUTPUT: U= totally positive fund'l units with representation in k_+ */
 
topu(bnf)=
{my(T,nf,U);
T=tpu(bnf);
nf=bnf.nf;
U=vector(#T,i,lift(nfbasistoalg(nf,T[i])));
return(U);
}



/******************************************************************************************************************************/
/****** BOUNDS OF LEMMA 15 ON OUR PAPER (ATTRACTOR-REPELLER CONSTRUCTION OF SHINTANI DOMAINS FOR TOTALLY COMPLEX QUARTIC FIELDS ***/

Bounds(S)=  \\ S=[c,d1,d2], where d1 and d2>=3 are integers (to obtain d1- and d2-regular polygons), and c is a small constant, c<=1
{my(P1,P2,P3,Q1,Q2,v,g1,g2,e,D1,D2,c,d1,d2);
[c,d1,d2]=S; 
P1=Rtapprox(d1); P2=Rtapprox(d2); P3=-P2;
\\P1=[[1,0], [-1/2,866/1000], [-1/2,-866/1000]]; P2=P1; P3=-P2;
Q1=[[1,1],[-1,1],[-1,-1],[1,-1]];
Q2=[[1,0],[0,1],[-1,0],[0,-1]];
v=[lambda3([Q1,P3]), lambda3([Q1,P1]), lambda3([P1,Q2]), lambda3([P2,Q2])];
g1=(v[1]*(c*v[3]+v[4]))^(-1);
g2=c*(v[4]*(c*v[1]+v[2])+4*c)^(-1);
e=1/150;
D1=(c+e*v[2]*(c*v[3]+v[4]))/(1-e*v[1]*(c*v[3]+v[4]));
D2=(c-e*(v[4]*(c*v[1]+v[2])+4*c))/(1+e*(v[3]*(c*v[1]+v[2])-4));
return([v,g1,g2,D1,D2]); \\ Lemma 15 of article JNT, (i) \varepsilon<g1, with D=D1 and (ii) \varepsilon<g2 with c'=D2
}


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




