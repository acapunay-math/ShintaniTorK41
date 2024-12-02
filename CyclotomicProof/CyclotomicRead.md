## Cyclotomic Quartic Fields

Let $k=\mathbb{Q}(\zeta_m)$
 be one of the three cyclotomic quartic fields, where $\zeta_m=\mathrm{e}^{2\pi i/m}$ for $m=8, 10,$ or $12$. The minimal polynomial which defines $k=\mathbb{Q}(\theta)$ satisfy

$$\theta^4+1=0, \text{ for } m=8,$$

$$\theta^4-\theta^3+\theta^2-\theta+1=0, \text{ for } m=10,$$

$$\theta^4-\theta^2+1=0, \text{ for } m=12.$$

Assuming that the generator $w\in k$ of the torsion group $W=\langle{w}\rangle$ of field $k$ is embedded in $\mathbb{C}\times\mathbb{C}$ as 

$$w=(\zeta_m^{\ell},\zeta_m),\quad \text{ where } \ell=3 \text{ if } m=8,10, \text{ and } \ell=5 \text{ if } m=12.$$

**Here we computationally verify the following claims:**

I)  $P^{\Delta,\Delta}(c')\subset S\subset P^{\Delta,\Delta}(d'),$ for certain constants $c'>0$ and $d'>0$.

II)    $E_0\cdot S\subset S$

_where_ 

- $\Delta$ is an a triangle whose vertices are one approximation of cubic roots of unity,

   $$\Delta = \Big[(1,0), \left(-\dfrac{1}{2},\alpha\right), \left(-\dfrac{1}{2},-\alpha\right)\Big] \approx \Big[1,\zeta_3,\zeta_3^2\Big],\qquad \alpha:=\dfrac{2521}{2911}$$

- $P^{\Delta,\Delta}(\lambda)$ denotes the complex of polyhedral cones defined in our previous paper
  [Attractor\-Repeller](https://www.sciencedirect.com/science/article/pii/S0022314X23002299)

$$P^{\Delta,\Delta}(\lambda)=\bigcup_{i=1}^3\mathbb{R}_{\geq0}\cdot (\Delta\times (\lambda^{-1}\partial\Delta)),\qquad \lambda>0.$$ 

- $S$ denotes the complex of polyhedral cones with coefficients in the field $k$,

$$S:=\displaystyle\bigcup_{j=0}^{m-1} \mathcal{C}_j,\qquad \mathcal{C}_j=w^j\cdot\text{Cone}[1,w,w^2,w^3].$$

- $E_0$ denotes the following fundamental units of $k$,

|   $m$  | $E_0$ |
|:---------------:| -------------:|
|        8 |          $\theta^2+\theta+1$ |
|         10     |     $-\theta+1$  |      
|     12     |    $-\theta^3-\theta^2$ |

