## Shintani domains for totally complex quartic number fields with torsion

Let $k$ be a totally complex quartic number field, with $E$ a unit in $k$ of infinite order and $T$ a subgroup of the torsion group of $k$. We propose in the file [ShintaniTorK41.gp](https://github.com/acapunay-math/ShintaniTorK41/blob/main/ShintaniTorK41.gp) an algorithm to obtain Shintani (fundamental) domains for the action of the group $G=T\times\langle{E\rangle}$ on $\mathbb{C}^{\ast}\times\mathbb{C}^{\ast}$, which was implemented in [PARI/GP](https://pari.math.u-bordeaux.fr/). By [Shintani's unit theorem](https://en.wikipedia.org/wiki/Shintani%27s_unit_theorem) such a domain is a finite union of (semi-closed) polyhedral cones with generators in $k$. This implementation is based on the preprint:

[SHINTANI DOMAINS FOR TOTALLY COMPLEX QUARTIC FIELDS WITH TORSION]

by A. CAPUÑAY, M. ESPINOZA AND E. FRIEDMAN, which extend our previous implementation [AlgorithmShitaniDomainK41](https://github.com/acapunay-math/ShintaniK41/tree/main/Algorithm) given for the case when $G=\langle{E\rangle}$ (torsion-free $T$).


## Execution

$(I).$ After uploading the file `ShintaniTorK41.gp` in Pari/GP, using an irreducible polynomial $p$ which defines a totally complex quartic number field, then you can use the command

 ```bash
 F=torFDK41(p,flag);
 ```
Here this GP function has one mandatory input $p$, and an optional one, $flag$, whose meaning is as follows:

  * $flag = 0$ (default): you can type $torFDK41(p)$ or $torFDK41(p,0)$ both return the same result. In this case the data $F$ obtained (described below) represents information about of a Shintani domain for the action on $\mathbb{C}^{\ast}\times\mathbb{C}^{\ast}$ of the group $G=W\times\langle{E\rangle}$, where $W$ is the (full) torsion group for $k$, obtained by PARI/GP.
      
  * $flag = 1$: if you type $torFDK41(p,1)$ you get the same data (with 4 entries) described in [AlgorithmShitaniDomainK41](https://github.com/acapunay-math/ShintaniK41/tree/main/Algorithm) by the command $FDK41(p)$, which returns information of a Shintani domain for action of the group $G=\langle{E\rangle}$ (torsion-free $T$).
  
  * $flag = m>1$: if you know a priori the order of the torsion group $W$ of $k$, then $m$ is a divisor of the order of $W$. In this case you can type $torFDK41(p,m)$ to obtain a data $F$ about a Shintani domain for the action of $G=W'\times\langle{E\rangle}$, where now $W'$ represents a subgroup of order $m$ of the torsion group $W$ of $k$. Moreover, note that $torFDK41(p,|W|)=torFDK41(p)$ for $|W|$ the order of the full torsion group of $k$.
  
  
So, leaving aside the case $flag=1$, we explain the data obtained in $F$ for the case when $flag=0$ or $flag>1$. This $F$ returns a list of three entries of form $F:=[F_1,F_2,F_3]$ interpreted as follows:

1. The first entry $F_1$ (i.e., $F[1]$) has 9 entries of the form 

      $$[t,p,reg,disc,tor,E,r,N,v]$$

with 

* $t =$ real computation time for $F$ in milliseconds

* $p =$ quartic irreducible polynomial defining a totally complex number field $k:= \text{the quotient ring } \mathbb{Q}[X]/(p)$ 

* $reg =$ Regulator of $k$ to $19$ decimals

* $disc =$ Discriminant of $k$

* $tor =$ vector of two entries of the form $[t_1,t_2]$, where $t_1=[a_1,b_1]$, $t_2=[a_2,b_2]$, such that $b_1$ generator of torsion group 
       of $k$ of order $a_1$, and $b_2$ generator of torsion subgroup of $k$ of order $a_2$ (so $a_2$ divides $a_1$, and $b_1, b_2\in k$)

* $E =$  fundamental unit of $k$ used. The unit $E$, like all other elements of $k$ below, is given as a polynomial $g$ in $\mathbb{Q}[X]$ 
       of degree at most $3$. The associated element of $k$ is the class of $g$ in $\mathbb{Q}[X]/(p)$. Moreover, its embedding $E=(E_ 1,E_ 2)$ in $\mathbb{C}\times\mathbb{C}$ satisfy that $|E_1|<1$
       
* $r =$  is a positive integer such that for torsion of order $2$ or $4$, we can take $r=1$ if its regulator $reg(k)>0.802$, $r=3$ otherwise. For torsion of order $6$, $8$, $10$ or $12$, we can take $r=1$.  More details see the preprint.
   
* $N =$ number of (semi-closed) cones in the Shintani domain constructed 

* $v =$ vector of four entries [#(four-cones),#(three-cones),#(two-cones),#(one-cones)] which describes information of the number semi-closed j-dimensional cones (by dimension $j=1,2,3,4$) in a Shintani domain obtained by execution of command:  $torFDK41(p,flag)$. 


2. The second entry $F_2$ of $F$ (i.e., $F[2]$) has the form 

      $$[C_1,C_2,...,C_N]$$

which is a list of the $N$ (semi-closed) cones where $N = F[1][9]$ was described above and the union of such cones form a Shintani domain for the action on $(\mathbb{C}^{\ast})\times(\mathbb{C}^{\ast})$ of the group $G=T\times\langle{E\rangle}$, with $T$ subgroup of the torsion group whose generators is $b_2=F[1][5][2][2]\in k$ which is of order $a_2=F[1][5][2][1]$. Each cone $C_j$ is given by $\ell$ linear inequalities ($\ell$ depending on the cone) giving $\ell$ closed or open half-spaces whose intersection is $C_j$. Thus, each $C_j$ has the form 

  $$[v_1,v_2,...,v_{\ell}]$$

where $v_i=[w,1]$ or $[w,-1]$ and $w$ is an element of $k$ (depending on $i$ and $j$). If $w$ is followed by $1$, then the corresponding (closed) half-space is the set of elements $x$ of $\mathbb{R}^4$ with $\text{Trace}(xw) \geq 0$. If $w$ is followed by $-1$, then the corresponding (open) half-space is given by $\text{Trace}(xw) > 0$. Here Trace is the extension to $\mathbb{R}^4$ of the trace map from $k$ to $\mathbb{Q}$.

3. The third entry $F_3$ of $F$ (i.e., $F[3]$) has the form 

      $$[\overline{C}_1,\overline{C}_2,...,\overline{C}_N]$$

where $\overline{C}_ j$ is the closure in $\mathbb{R}^4$ of the cone $C_ j$ in $F_ 3$. Each closed cone $\overline{C}_ j$ is given here by a list of generators in $k$.

$(II).$ If you want to obtain Shintani domains for a list of (totally complex quartic) polynomials `L`, you can use the command

  ```bash
  TorShExamplesK41(L)
  ```

This creates a file called ExamplesShK41 which contains explicit Shintani domains via the command `torFDK41(p)` for each polynomial `p` of the list `L`.

$(III).$ We show a list of 20 examples of Shintani domains:

* File [ExamplesShK41-M.txt](https://github.com/acapunay-math/ShintaniTorK41/blob/main/ExamplesShK41-M.txt) can be read by PARI/GP via the command

        \r ExamplesShK41-M.txt

* File [ExamplesShK41-ML.sage](https://github.com/acapunay-math/ShintaniTorK41/blob/main/ExamplesShK41-ML.sage) can be read by SAGE-Math via the command 

         load('ExamplesShK41-ML.sage')
         

In both files returns a list of size 20 as a vector: $examples=[E1,\ldots,E{20}]$ which each $Ej$ has the same structure of vector $F$ described in item $(I)$.

