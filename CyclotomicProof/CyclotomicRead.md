# Cyclotomic Proof

- Alex Capuñay, Facultad de Ciencias, Universidad Arturo Prat, Iquique - Chile.
- Milton Espinoza, Departamento de Matemáticas, Facultad de Ciencias, Universidad de La Serena. La Serena - Chile.
- Eduardo Friedman, Departamento de Matemáticas, Facultad de Ciencias, Universidad de Chile. Santiago - Chile.

This note was created using Markdown in CoCalc.

**Release notes:**

- Version 1.0 (03 December 2024). Initial version.

## Two lemmas:

Let $k=\mathbb{Q}(\zeta_m)$
 be one of the three cyclotomic quartic fields, where $\zeta_m=\mathrm{e}^{2\pi i/m}$ for $m=8, 10,$ or $12$. The minimal polynomial which defines $k=\mathbb{Q}(\theta)$ satisfy

$$\theta^4+1=0, \text{ for } m=8,$$

$$\theta^4-\theta^3+\theta^2-\theta+1=0, \text{ for } m=10,$$

$$\theta^4-\theta^2+1=0, \text{ for } m=12.$$

Assuming that the generator $w\in k$ of the torsion group $W=\langle{w}\rangle$ of field $k$ is embedded in $\mathbb{C}\times\mathbb{C}$ as 

$$w=(\zeta_m^{\ell},\zeta_m),\quad \text{ where } \ell=3 \text{ if } m=8,10, \text{ and } \ell=5 \text{ if } m=12.$$

**Here we computationally verify the following claims:**

<u>Lemma I.</u>  There are $c'>0$ and $d'>0$ such that $P^{\Delta,\Delta}(c')\subset S\subset P^{\Delta,\Delta}(d')$.

<u>Lemma II.</u>  $\widetilde{E}\cdot S\subset S$.

_where_ 

- $\Delta$ is a triangle whose vertices are one approximation of cubic roots of unity,

$$\Delta = \Big[(1,0), \left(-\dfrac{1}{2},\alpha\right), \left(-\dfrac{1}{2},-\alpha\right)\Big] \approx \Big[1,\zeta_3,\zeta_3^2\Big],\qquad \alpha:=\dfrac{2521}{2911}$$

- $P^{\Delta,\Delta}(\lambda)$ denotes the complex of polyhedral cones defined in our previous paper
  [Attractor\-Repeller](https://www.sciencedirect.com/science/article/pii/S0022314X23002299),

$$P^{\Delta,\Delta}(\lambda)=\bigcup_{i=1}^3\mathbb{R}_{\geq0}\cdot (\Delta\times (\lambda^{-1}\partial\Delta)),\qquad \lambda>0.$$ 

- $S$ denotes the complex of polyhedral cones with coefficients in the field $k$,

$$S:=\displaystyle\bigcup_{j=0}^{m-1} \mathcal{C}_j,\qquad \mathcal{C}_j=w^j\cdot\text{Cone}[1,w,w^2,w^3].$$

- $\widetilde{E}=(\widetilde{E}_1,\widetilde{E}_2)\in\mathbb{C}\times\mathbb{C}$ denotes the following fundamental units of $k$ such that $|\widetilde{E}_1|<1$,

|   $m$  | $\widetilde{E}$ |
|:---------------:| -------------:|
|        8 |          $\theta^2+\theta+1$ |
|         10     |     $-\theta+1$  |      
|     12     |    $-\theta^3-\theta^2$ |

## Proof of the two Lemmas:

- _**Proof of Lemma I.**_ Open the algebraic software PARI/GP and loading the file ?? using the command

  <u>Step 0:</u> Fixing one of three cyclotomic quartic fields $k=\mathbb{Q}(\zeta_m)$ for $m=8, 10$, and $12$. Execute on PARI/GP the classical command
  
      bnf=bnfinit(p);
  
  taking as input $p=x^4+1$, $x^4-x^3+x^2-x+1$, $x^4-x^2+1$.
  
  <u>Step 1:</u> In PARI/GP apply the command 
  
      Am=ApproxRComplex(bnf,c,3,3);
      Rm=ApproxRComplex(bnf,d,3,3);
  
  We can obtain two complexes of $k$-rational polyhedral cones
  
     $$A_m:=f(P^{\Delta,\Delta}(c)),\quad R_m:=f(P^{\Delta,\Delta}(d))$$
  
  For this, we consider the following parameters $(m,c,d)$:
  
  | $p$ | $m$ | $c$  | $d$ |
  | :------------ | :------------ |:---------------:| -------------:|
  | $x^4+1$  | $8$     | $1/5$ |    $5$ |
  | $x^4-x^3+x^2-x+1$ | $10$ |  $1/6$ |  $4$ |
  | $x^4-x^2+1$ | $12$ |  $1/8$  |      $2$ |
  
  <u>Step 2:</u> Using the command ?? to obtain the differences-set
  
  $$A_m-S,\qquad S-R_m$$
  
  Since we obtain that such differences-set are both empty, then we have that
  $$A_m\subset S \subset R_m.$$
  
  <u>Step 3:</u> Using the command ?? we can explicitly obtain positive constants $c'>0$ and $d'>0$ such that
  
  $$P^{\Delta,\Delta}(c')\subset A_m=f(P^{\Delta,\Delta}(c'))$$
  
  and
  
  $$R_m=f(P^{\Delta,\Delta}(d))\subset P^{\Delta,\Delta}(d')$$
  
  For this, we use the parameters $(c',d')$
  
  |  $m$ | $c'$  | $d'$ |
  | :------------ |:---------------:| -------------:|
  | $8$     | ? |  ?   |
  | $10$ | ?  | ? |
  | $12$ | ?  | ?   |
  

- _**Proof of Lemma II:**_

