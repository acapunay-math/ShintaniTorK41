# Cyclotomic Proof

- Alex Capuñay, Facultad de Ciencias, Universidad Arturo Prat. Iquique - Chile.
- Milton Espinoza, Departamento de Matemáticas, Facultad de Ciencias, Universidad de La Serena. La Serena - Chile.
- Eduardo Friedman, Departamento de Matemáticas, Facultad de Ciencias, Universidad de Chile. Santiago - Chile.

This note was created using Markdown in CoCalc.

**Release notes:**

- Version 1.0 \(06 December 2024\). Initial version.

## Two lemmas:

Let $k=\mathbb{Q}(\zeta_m)$
 be one of the three cyclotomic quartic fields, where $\zeta_m=\mathrm{e}^{2\pi i/m}$ for $m=8, 10,$ or $12$. The minimal polynomial which defines $k=\mathbb{Q}(\theta)$ satisfy

$$\theta^4+1=0, \text{ for } m=8,$$

$$\theta^4-\theta^3+\theta^2-\theta+1=0, \text{ for } m=10,$$

$$\theta^4-\theta^2+1=0, \text{ for } m=12.$$

Let the torsion group $W:=\langle{w}\rangle$ of $k$, note that $w=\theta^{t}$ for any $t\in\mathbb{N}$ with $gcd(t,m)=1$. Let us assume that such a generator $w$ of $W$ is embedded $\mathbb{C}\times\mathbb{C}$ as 

$$w=(\zeta_m^{\ell},\zeta_m),\quad \text{ where } \ell=3 \text{ if } m=8,10, \text{ and } \ell=5 \text{ if } m=12.$$

**Here we computationally verify the following claims:**

<u>Lemma I.</u>  There are $c'>0$ and $d'>0$ such that $P^{\Delta,\Delta}(c')\subset S\subset P^{\Delta,\Delta}(d')$.

<u>Lemma II.</u>  $u\cdot S\subset S$.

_where_ 

- $\Delta$ is a triangle whose vertices are one approximation of cubic roots of unity,

$$\Delta = \Big[(1,0), \left(-\dfrac{1}{2},\alpha\right), \left(-\dfrac{1}{2},-\alpha\right)\Big] \approx \Big[1,\zeta_3,\zeta_3^2\Big],\qquad \alpha:=\dfrac{2521}{2911}$$

- $P^{\Delta,\Delta}(\lambda)$ denotes the complex of three polyhedral four\-dimensional cones defined in our previous paper
  [Attractor\-Repeller](https://www.sciencedirect.com/science/article/pii/S0022314X23002299),

$$P^{\Delta,\Delta}(\lambda)=\mathbb{R}_{\geq0}\cdot (\Delta\times (\lambda^{-1}\partial\Delta))=\bigcup_{i=0}^{2}\mathbb{R}_{\geq0}\cdot Q_i,\qquad \lambda>0,$$

with $Q_i=\Delta\times[c^{-1}\Delta_{i},c^{-1}\Delta_{i+1}]$ (take $i$ module 3), $\Delta=[\Delta_0,\Delta_1,\Delta_2]$.

- $S$ denotes the complex of polyhedral cones with coefficients in the field $k$,

$$S:=\displaystyle\bigcup_{j=0}^{m-1} \mathcal{C}_j,\qquad \mathcal{C}_j=w^j\cdot\text{Cone}[1,w,w^2,w^3].$$

- $u=(u_1,u_2)\in\mathbb{C}\times\mathbb{C}$ denotes the following fundamental units of $k$ such that $|u_1|<1$,

|   $m$  | $u$ |
|:---------------:| -------------:|
|        8 |          $\theta^2+\theta+1$ |
|         10     |     $-\theta+1$  |      
|     12     |    $-\theta^3-\theta^2$ |

## Proof of the two Lemmas:

- _**Proof of Lemma I.**_ Open the computational algebraic system PARI/GP and loading our the file [NameFile.gp](??) using the command
  ```
  \r NameFile.gp
  ```

  Then fixing one of three cyclotomic quartic fields $k=\mathbb{Q}(\zeta_m)$ for $m=8, 10$, or $12$. For this, we execute on PARI/GP the classical command
  ```
  bnf=bnfinit(p);
  ```

  where we taking as input $p=x^4+1$, $x^4-x^3+x^2-x+1$, $x^4-x^2+1$.
  
  <u>**Step 1:**</u>  Since the cones in $P^{\Delta,\Delta}(\lambda)$ do not necessarily have their generators in $k$,  we need below to consider $f$, to be linear map which it is little perturbation of identity map, called $\varepsilon$-perturbation of identity, and as $k$ is dense in $\mathbb{R}^4$, we can always obtain one new polyhedral complex $f(P^{\Delta,\Delta}(\lambda))$ from $P^{\Delta,\Delta}(\lambda)$, now with generators in $k$. For this, we apply the command 
  ```
  [A,R]=ApproxRComplex(bnf,c,d);
  ```

  Considering the following parameters $(c,d)$ according to each $p$ taken:
  | $p$ |  $c$ | $d$ |
  | :---------------- | :---: | --: |
  | $x^4+1$ | $1/5$ | $5$ |
  | $x^4-x^3+x^2-x+1$ | $1/6$ | $4$ |
  | $x^4-x^2+1$ | $1/8$ | $2$ |

  So we can obtain two complexes of three $k$\-rational four\-dimensional polyhedral cones each one

  $$A:=f(P^{\Delta,\Delta}(c)),\quad R:=f(P^{\Delta,\Delta}(d)).$$

  <u>**Step 2:**</u> Now apply the command in the pair (A,R) of the previous step
  ```
  [D1,D2]=DiffComplex1(bnf,A,R);
  ```

  to obtain the difference\-sets

  $$D_1:=A-S,\qquad D_2:=S-R$$

  Since we obtain that such difference\-sets are both empty, then this implies that

  $$A\subset S \subset R.$$
  
  That is,
  
  $$f(P^{\Delta,\Delta}(c))\subset S\subset f(P^{\Delta,\Delta}(d)).$$

  N.B. We note that here cannot apply the command DiffComplex1(--) directly on the complexes  $P^{\Delta,\Delta}(c)$ and $P^{\Delta,\Delta}(d)$, because such complexes are not $k$-rational, that is, their generators are not elements of number field $k$. 
  
  <u>**Step 3:**</u> Finally, using the command 
  ```
  [c',d']=Bounds([c,d]);
  ```

  By Lemma 15 in our paper [Attractor\-Repeller](https://www.sciencedirect.com/science/article/pii/S0022314X23002299), we can explicitly obtain positive constants $c'>0$ and $d'>0$ to ensure that

 $$P^{\Delta,\Delta}(c')\subset f(P^{\Delta,\Delta}(c)),\qquad f(P^{\Delta,\Delta}(d))\subset P^{\Delta,\Delta}(d').$$
 In this case our algorithm returns the following parameters $(c',d')$ according to each $(c,d)$ and $\varepsilon=1/150$: 
  
  | $c$ | $d$ | $c'$ | $d'$ |
  | :--- | :---  | :--: | ---: |
  | $1/5$ | $5$ |   $\dfrac{1814222527}{11043058985}\approx 0.164$ |    $\dfrac{151154723}{24972421}\approx 6.052$ |
  | $1/6$ | $4$ |   $\dfrac{3518892479}{26481431049}\approx 0.132$ |    $\dfrac{242139697}{51405543}\approx 4.710$ |
  | $1/8$ | $2$ |   $\dfrac{3299787329}{35272057207}\approx 0.093$ |    $\dfrac{121800199}{54326945}\approx 2.241$ |

  So, by Steps 2 and 3, we have

  $$P^{\Delta,\Delta}(c')\subset S\subset P^{\Delta,\Delta}(d').$$

  Completing the Proof of Lemma I.

- _**Proof of Lemma II:**_ Using the fundamental units $u$ given above for each $m=8,10,12$, we can verify that $$u\cdot S\subset S.$$

   For this, we apply the following command
   
      D=DiffComplex2(bnf,u);
      
  which compute the difference $u\cdot S-S$ of these complexes. In the three cases ($m=8,10,$ and $12$), our implementation return empty-set. That is, the (polyhedral) complex $u\cdot S$ is contained in the complex $S$. Completing the Proof of Lemma II.

