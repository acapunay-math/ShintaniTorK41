## Explicit Shintani domains for totally complex quartic number fields

Let $k$ be a totally complex quartic number field, with $E$ a unit in $k$ of infinite order and $T$ a (finite) subgroup of the torsion group of $k$. For the action of the group $G=T\times\langle{E\rangle}$ on $\mathbb{C}^{\ast}\times\mathbb{C}^{\ast}$, we describe below our algorithm to obtain a Shintani (fundamental) domain implemented in [PARI/GP](https://pari.math.u-bordeaux.fr/). By [Shintani's unit theorem](https://en.wikipedia.org/wiki/Shintani%27s_unit_theorem) such a domain is a finite union of (semi-closed) polyhedral cones with generators in $k$. This implementation is based on the manuscript (abbreviated MS)

[SHINTANI DOMAINS FOR TOTALLY COMPLEX QUARTIC FIELDS WITH TORSION]

by A. CAPUÑAY, M. ESPINOZA AND E. FRIEDMAN, which extend our implementation in [ATTRACTOR-REPELLER](https://github.com/acapunay-math/ShintaniK41/tree/main/Algorithm) given for the case when $G=\langle{E\rangle}$ (torsion-free $T$).

## File description

$(I).$ After uploading the file `ShintaniTorK41.gp` in Pari/GP, using an irreducible polynomial $p$ which defines a totally complex quartic number field, then you can use the command

 ```bash
 F=torFDK41(p,flag);
 ```
Here this GP function has one mandatory input $p$, and an optional one, $flag$, whose meaning is as follows:

  * $flag = 0$ (default): you can type $torFDK41(p)$ or $torFDK41(p,0)$ both return the same result. In this case the data $F$ obtained (described below) represents information about of a Shintani domain for the action on $\mathbb{C}^{\ast}\times\mathbb{C}^{\ast}$ of the group $G=W\times\langle{E\rangle}$, where $W$ is the (full) torsion group for $k$, obtained by PARI/GP.
      
  * $flag = 1$: if you type $torFDK41(p,1)$ you get the same data (with 4 entries) described in [ATTRACTOR-REPELLER](https://github.com/acapunay-math/ShintaniK41/tree/main/Algorithm) by the command $FDK41(p)$, which returns information of a Shintani domain for action of the group $G=\langle{E\rangle}$ (torsion-free $T$).
  
  * $flag = m>1$: if you know a priori the order of the torsion group $W$ of $k$, then $m$ is a divisor of the order of $W$. In this case you can type $torFDK41(p,m)$ to obtain a data $F$ about a Shintani domain for the action of $G=W'\times\langle{E\rangle}$, where now $W'$ represents a subgroup of order $m$ of the torsion group $W$ of $k$.
  
  
So, leaving aside the case $flag=1$, we explain the data obtained in $F$ for the case when $flag=0$ or $flag>1$. This $F$ returns a list of three entries of form $F:=[F_1,F_2,F_3]$ interpreted as follows:

1. The first entry $F_1$ (i.e., $F[1]$) has 10 entries of the form 

      $$[t,p,reg,disc,tor,E,r,r',N,v]$$

with 

* $t =$ real computation time for $F$ in milliseconds

* $p =$ quartic irreducible polynomial defining a totally complex number field $k:= \text{the quotient ring } \mathbb{Q}[X]/(p)$ 

* $reg =$ Regulator of $k$ to $19$ decimals

* $disc =$ Discriminant of $k$

* $tor =$ vector of two entries of the form $[t_1,t_2]$, where $t_1=[a_1,b_1]$, $t_2=[a_2,b_2]$, such that $b_1$ generator of torsion group 
       of $k$ of order $a_1$, and $b_2$ generator of torsion subgroup of $k$ of order $a_2$ (so $a_2$ divides $a_1$, and $b_1, b_2\in k$)

* $E =$  fundamental unit of $k$. The unit $E$, like all other elements of $k$ below, is given as a polynomial $g$ in $\mathbb{Q}[X]$ 
       of degree at most $3$. The associated element of $k$ is the class of $g$ in $\mathbb{Q}[X]/(p)$
       
* $r =$  is a positive integer such that for torsion of order $2$ or $4$, we can take $r=1$ if its regulator $reg(k)>0.802$, $r=3$ otherwise. For torsion of order $6$, we can take $r=1$ if $reg(k)>0.405$, $r=2$ otherwise. And we can take $r=3$ for torsion of order 8 or 12, and $r=4$ for torsion of order $10$. More details see the manuscript MS.
   
* $r' =$ is a positive integer $\leq r$ such that $E^{r'}\cdot S\subset S$, where $S$ is a polyhedral complex of cones is described in the manuscript MS. In many cases $r'=r=1$ when $reg(k)>0.802$ for all fields with torsion of order $2$, $4$ or $6$.

* $N =$ number of (semi-closed) cones in the Shintani domain constructed 

* $v =$ vector of four entries [#(four-cones),#(three-cones),#(two-cones),#(one-cones)] which describes information of the number semi-closed j-cones (by dimension $j=1,2,3,4$) in a Shintani domain obtained by execution of command:  $torFDK41(p,flag)$.


The Shintani domain corresponds to the action on $(\mathbb{C}^{\ast})\times(\mathbb{C}^{\ast})$ of the group $G=T\times\langle{E\rangle}$.


2. The third entry $F_2$ of $F$ (i.e., $F[2]$) has the form  

      $$[C_1,C_2,...,C_N]$$

which is a list of the $T$ (semi-closed) cones in the Shintani domain, where $N = F[1][9]$ was described above. Each cone $C_j$ is given by $\ell$ linear inequalities ($\ell$ depending on the cone) giving $\ell$ closed or open half-spaces whose intersection is $Cj$. Thus, each $C_j$ has the form  

  $$[v_1,v_2,...,v_{\ell}]$$

where $v_i=[w,1]$ or $[w,-1]$ and $w$ is an element of $k$ (depending on $i$ and $j$). If $w$ is followed by $1$, then the corresponding (closed) half-space is the set of elements $x$ of $\mathbb{R}^4$ with $\text{Trace}(xw) \geq 0$. If $w$ is followed by $-1$, then the corresponding (open) half-space is given by $\text{Trace}(xw) > 0$. Here Trace is the extension to $\mathbb{R}^4$ of the trace map from $k$ to $\mathbb{Q}$.

3. The fourth entry $F_3$ of $F$ (i.e., $F[3]$) has the form  

      $$[CC_1,CC_2,...,CC_N]$$

where $CC_j$ is the closure in $\mathbb{R}^4$ of the cone $C_j$ in $F_3$. Each closed cone $CC_j$ is given here by a list of generators in $k$.


$(II)$ A list of examples is given in 

$(II).$ If you want to obtain Shintani domains for a list of (totally complex quartic) polynomials `L`, you can use the command

  ```bash
  ShintaniExamplesK41(L)
  ```

This creates a file with Shintani domains via the command `FDK41(p)` for each polynomial `p` of the list `L`
