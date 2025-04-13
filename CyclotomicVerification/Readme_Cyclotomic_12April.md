## Notes on Shintani domain calculations in the  cyclotomic case

This README file describes the computational verification of the three claims made in Section 3 of the manuscript Shintani fundamental domains for   quartic number fields with many  roots of unity by  A. Capuñay, M. Espinoza and E. Friedman. We  will refer to that Ms. as [C/E/F].  The claims involve unions of cones connected to Shintani domains for  the three quartic cyclotomic fields $k=\mathbb{Q}(\Theta)$ where $\Theta$ is a primitive root of unity of order  $m=8$, 10 or 12. 

The first two claims   in need of computer verification  in  Section 3 of  [C/E/F] appear in  display (20) there, while the third one appears on the next to last paragraph of the paper. Namely, 

$$S=\lbrace{0\rbrace}\cup \bigcup_{\ell=0}^{m-1}(\Theta^\ell\cdot \mathcal{C}_0')  \qquad   \text{(disjoint   union)}, \qquad (\ast)$$

$$E\cdot S\subset S, \qquad \qquad \qquad\qquad \qquad \qquad\qquad \qquad\qquad   (\ast\ast)$$

$$P^{\Delta,\Delta}(c)\subset S\subset P^{\Delta,\Delta}(d),\qquad \qquad\qquad\qquad \qquad (\ast\ast\ast)$$

with notation as in  display (19) of [C/E/F]. We  will give $\Delta, a$ and $b$ explicitly. 

 
## Overview of the calculations

We first address ($\ast\ast$) since it is the easiest one. By definition (see display (19) of [C/E/F])   

$$S:= \bigcup_{\ell=0}^{m-1}(\Theta^\ell\cdot \mathcal{C}_0)$$

is independent of $E$ and satisfies $\Theta\cdot S=S$. Hence  to verify ($\ast\ast$) for any unit of infinite order $E\in k$,  it suffices to do so for  $E=u$ for any generator $u$ of the units of $k$ modulo torsion. This is done using an algorithm giving the difference $E\cdot S-S$ of unions of k-rational cones again as such a difference. SEE FILE XXX This, and other  algorithms below, are described in our earlier paper [CEF] [Attractor-repeller construction of Shintani domains for totally complex quartic fields, J. Number Th. 258 (2024) 146--172](https://www.sciencedirect.com/science/article/abs/pii/S0022314X23002299). 

We now address ($\ast$). Since the inclusions $0\in S$ and $(\Theta^\ell\cdot\mathcal{C}_0')\subset S$ are obvious from the definition of $S$ in Section 3 of [ C/E/F], the equality in ($\ast$) is verified by checking that

$$\mathcal{C}_ 0-\bigcup_{\ell=0}^{m-1}(\Theta^\ell\cdot \mathcal{C}_ 0')=\lbrace{0\rbrace}.$$

This is done  using  the algorithm IN FILE XXX. The notation $P^{\Delta,\Delta}(c)\subset\mathbb{C}\times\mathbb{C}$ is defined in  [CEF,(10)]. For $\Delta$ we take the closed convex set (in fact, a triangle) with vertices 

$$\Big[1,-\frac12+i\frac{2521}{2911},-\frac12-i\frac{2521}{2911}\Big],$$

where $i:=\sqrt{-1}$ and $\frac{2521}{2911}$ was chosen as a rational approximation of $\sqrt{3}/2$. We first try  the values    

$$
(c',d'):=
\begin{cases}
(1/5,5) \ &\text{if } m=8,
\\
(1/6,4) \ &\text{if } m=10,
\\
(1/8,2) \ &\text{if } m=12.
\end{cases}
$$

Unfortunately,  $P^{\Delta,\Delta}(c')$ and $P^{\Delta,\Delta}(d')$ are not $k$-rational (i.e., are not a finite union of $k$-rational cones). As our algorithm can only compute with $k$-rational cones, we  cannot directly prove the inclusions ($\ast\ast$) above. We therefore find an $\varepsilon$-deformation (see [CEF,(19)] with  of the identity $f$ with $\varepsilon=1/150$ such that $f\big(P^{\Delta,\Delta}(c')\big)$ and $f\big(P^{\Delta,\Delta}(d')\big)$ are $k$-rational. Using FILA YYY we could thus verify 

$$f\big(P^{\Delta,\Delta}(c')\big)\subset S\subset f\big(P^{\Delta,\Delta}(d')\big).$$

Using [CEF, Lemma 15] we  also find a rational pair $(c,d)$ ESPECIFICAR such that 

$$P^{\Delta,\Delta}(c) \subset f\big(P^{\Delta,\Delta}(c')\big)$$

and 

$$f\big(P^{\Delta,\Delta}(d')\big) \subset P^{\Delta,\Delta}(d).$$
