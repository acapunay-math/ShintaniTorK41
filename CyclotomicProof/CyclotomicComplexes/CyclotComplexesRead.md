# Cyclotomic Complexes

 This README file is meant to aid in interpreting the accompanying files [Cyclotomicc.txt](https://github.com/acapunay-math/ShintaniTorK41/blob/main/CyclotomicProof/CyclotomicComplexes/Cyclotomicc.txt) and [Cyclotomicc-ML.sage](https://github.com/acapunay-math/ShintaniTorK41/blob/main/CyclotomicProof/CyclotomicComplexes/Cyclotomicc-ML.sage)

##  k-rational complexes of polyhedral cones for three cyclotomic number fields  

 For each one of the cyclotomic quartic number fields $k=\mathbb{Q}(\zeta_m)$ where $\zeta_m=\mathrm{e}^{2\pi i/m}$ for $m=8, 10, 12$, whose minimal polinomial $p$ is

   $$p:=x^4+1,\quad x^4-x^3+x^2-x+1,\quad x^4-x^2+1,$$

  respectively. We explicitly show the three complexes of $k$-rational four-dimensional polyhedral cones: 
  
  $$S:=\bigcup_{j=0}^{m-1} \mathcal{C}_ j,\quad A:=f(P^{\Delta,\Delta}(c)),\quad R:=f(P^{\Delta,\Delta}(d)),$$
  
 mentioned in the proof of [Lemma I](https://github.com/acapunay-math/ShintaniTorK41/tree/main/CyclotomicProof). Such sets satisfy $A\subset S \subset R$.

 The file [Cyclotomicc.txt](https://github.com/acapunay-math/ShintaniTorK41/blob/main/CyclotomicProof/CyclotomicComplexes/Cyclotomicc.txt) is a text file meant to be downloaded and read into PARI GP via the command

 ```bash
 \r Cyclotomicc.txt
 ```

It can, of course, be read and used by other software, bearing in mind that square brackets [] 
are used for lists, its elements are separated by commas. The file [Cyclotomicc-ML.sage](https://github.com/acapunay-math/ShintaniTorK41/blob/main/CyclotomicProof/CyclotomicComplexes/Cyclotomicc-ML.sage) can be read by SageMath using the command

 ```bash
 load('PCyclotomicc-ML.sage')
 ```

This returns the same list as in the file PCyclotomicc.txt and has the same structure.

## Description of file [Cyclotomicc.txt](https://github.com/acapunay-math/ShintaniTorK41/blob/main/CyclotomicProof/CyclotomicComplexes/Cyclotomicc-ML.sage):

The file PCyclotomicc.txt contains a data of three vectors. It consists of one long line of text of the form 

  $$data = [D_1,D_2,D_3];$$

ending in a semicolon (to prevent PARI GP from printing this big  file to screen). Each $D_i$ (i.e., $data[i]$ for $1\leq i\leq 3$) has the form  

  $$[a_1,a_2,a_3,a_4,a_5,a_6,a_7]$$

1. The first entry $a_1$ (i.e., $data[1][1]$) has the form 

  $$[p,w,m]$$

with 

* $p=$ quartic irreducible polynomial defining a totally complex number field  $k:= \text{the quotient ring } \mathbb{Q}[X]/(p)$, in our case $p$ is equal to $x^4+1$, $x^4-x^3+x^2-x+1$ or $x^4-x^2+1$.

* $w$ denotes a generator of torsion group of $k$ whose embedding in $\mathbb{C}\times\mathbb{C}$ is of the form 

  $$w=(\zeta_m^{\ell},\zeta_m),\quad \text{ where } \ell=3 \text{ if } m=8,10, \text{ and } \ell=5 \text{ if } m=12.$$

* $m=$ order of (full) torsion group of $k$ (here $m=8, 10, 12$).

2. The second entry $a_ 2$ of $D_ i$ (i.e., $data[i][2]$) has the form 

  $$\[C'_0,C'_1,\ldots,C'_{m-1}\],$$
  
  $$[C'_ 0,\ldots,C'_{m-1}]$$
  
  which represents a polyhedral complex of $m$ four-dimensional $k$-rational semi-closed cones:
  
   $$S:=\left(\bigcup_{j=0}^{m-1}C_j'\right)\cup \{0\},\quad C_j':=C_j-C_{j+1} \quad (\text{ taking } j \text{ modulo } m=8,10,12)$$
   
   $$\text{and } \quad C_j:=w^j\cdot\text{Cone}[1,w,w^2,w^3].$$
   
   Each semi-closed cone $C_j'$ is represented by  4 linear inequalities, in this case by 4 closed or open half-spaces whose closure is $C_j$. Thus, each $C_j'$ has the form    
   
   $$[v_1,v_2,v_3,v_4]$$
   
   where $v_i=[w,1]$ or $[w,-1]$ and $w$ is an element of $k$ (depending on $i$ and $j$). If $w$ is followed by $1$, then the corresponding (closed) half-space is the set of elements $x$ of $\mathbb{R}^4$ with $\text{Trace}(xw) \geq 0$. If $w$ is followed by $-1$, then the corresponding (open) half-space is given by $\text{Trace}(xw) > 0$. Here Trace is the extension to $\mathbb{R}^4$ of the trace map from $k$ to $\mathbb{Q}$.

3. The third entry $a_3$ of $D_i$ (i.e., data[i][3]) has the form  
    $$[C_0,C_1,...,C_{m-1}]$$ 
    where $C_j$ is the closure in $\mathbb{R}^4$ of the cone $C_j'$ in $a_2$. Each closed cone $C_j$ is given here by its list of generators in $k$ mentioned in the item 2. 

4. The fourth entry $a_4$ of $D_i$ (i.e., $data[i][4]$) has the form  
   $$[A_0,A_1,A_2]$$ 
   
   which represents a polyhedral complex of 3 four-dimensional $k$-rational semi-closed cones: 
   $$A:=f(P^{\Delta,\Delta}(c))=\bigcup_{i=0}^2A_i,$$
   where $P^{\Delta,\Delta}(c)$ is the polyhedral complex described in  [Lemma 10: Attractor-Repeller](https://www.sciencedirect.com/science/article/pii/S0022314X23002299) and the map $f$ is an $\varepsilon$-perturbation linear of identity described in [Section 4.4: Attractor-Repeller](https://www.sciencedirect.com/science/article/pii/S0022314X23002299) (taking $\varepsilon\leq 1/150$). Moreover to build such $A$ we consider the parameters: $(c,m)=(1/5,8), (1/6,10), (1/8,12)$ and we take 
   $$\Delta = \left[(1,0), (-1/2,\alpha), (-1/2,-\alpha)\right] \approx [1,\zeta_3,\zeta_3^2],\qquad \alpha:=\dfrac{2521}{2911},$$ 

   which represents a triangle with vertices in $\mathbb{Q}^2$ in the complex plane $\mathbb{C}$ such that their vertices are an approximation of the unit cubic roots, $\zeta_3=\text{exp}(2\pi i/3)$. 

   Each semi-closed cone $A_i$ ($0\leq i\leq 2$) is given in the same form as in item 3, that is, each $A_i$ is represented by intersection of closed or open half-spaces. In this case, each $A_i$ is given by 5 inequalities.

5. The fifth entry  $a_5$ of $D_i$ (i.e., $data[i][5]$) has the form  
   $$[\overline{A}_0,\overline{A}_1,\overline{A}_2]$$
   where $\overline{A}_i$ is the closure in $\mathbb{R}^4$ of the cone $A_i$ in $a_4$. Each closed cone $\overline{A}_i$ is represented by 6 generators in $k$.    

6. The sixth entry $a_6$ of $D_i$ (i.e., $data[i][6]$) has the same form as in $a_4$:
   $$[R_0,R_1,R_2]$$
   
   which represents to the polyhedral complex of 3 four-dimensional $k$-rational semi-closed cones: 
   
   $$R:=f(P^{\Delta,\Delta}(d))=\bigcup_{i=0}^2R_i,$$
   for the following parameters: $(c,m)=(5,8), (4,10), (2,12)$. Again all cones $R_i$ are represent by 5 close or open half-spaces.
   
7. The seventh entry $a_7$ of $D_i$ (i.e. $data[i][7]$) like $a_5$ has the form 
   $$[\overline{R}_0,\overline{R}_1,\overline{R}_2]$$
   where $\overline{R}_i$ is the closure in $\mathbb{R}^4$ of the cone $R_i$ in $a_6$, and each closed cone $\overline{R}_i$ is represented by 6 generators in $k$.

