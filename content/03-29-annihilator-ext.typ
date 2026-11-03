#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/29-annihilator-ext.typ": (
  conductor-extension-diagram, projective-trace-diagram,
  pullback-endomorphism-diagram,
)

== Annihilator of Ext <sec:annihilator-ext>
#idx("annihilator", "of Ext")
#source(625)

In §@sec:extensions-lattices we saw the importance of the $R$-module
$op("Ext")_Lambda^1 lr((M,N))$, where $M$ and $N$ are a pair of lattices for the
$R$-order $Lambda$. When $Lambda=R G$, with $G$ a finite group, the fact that
$abs(G) dot op("Ext")(M,N)=0$ for all such $M$ and $N$, can be viewed as a
useful generalization of Maschke's Theorem. We need an analogous result when
$Lambda$ is an arbitrary $R$-order. If $Lambda$ is an $R$-order in a f.d.
semisimple $K$-algebra $A$, then $op("Ext")(M,N)$ is a f.g. $R$-torsion
$R$-module, by @prop:extension-torsion. The significant question is whether we
can find nonzero elements $a in R$, depending only on $Lambda$, such that
$a dot op("Ext")(M,N)=0$ for all $Lambda$-lattices $M$ and $N$. Further, can we
do better by considering those $a in R$ such that for a given $M$,
$a dot op("Ext")(M,N)=0$ for all $N$? We devote this section to answering such
questions.

=== Annihilator of Ext; Higman Ideal <ss:ext-annihilator-higman-ideal>

There are two main results from this section which will play a vital role in
Chapter~@ch:local-global-integral-representations. Suppose that $Lambda$ is an
$R$-order in a separable $K$-algebra $A$, and let $Lambda'$ be a maximal
$R$-order in $A$ containing $Lambda$. Then there exist nonzero elements $a in R$
such that $a Lambda' subset.eq Lambda$ (this is obvious), and for such $a in R$
we will show that
$ a dot op("Ext")_Lambda^1 lr((M,N))=0 $
for all $Lambda$-lattices $M$ and all $Lambda$-modules $N$. The second major
result is a consequence of the first one, namely,
$
  op("Ext")_Lambda^1 lr((M,N)) tilde.equiv
  product_P op("Ext")_(Lambda_P)^1 lr((M_P,N_P))
$
for $M,N$ as above, where $P$ ranges over the finite set of maximal ideals of
$R$ for which $Lambda_P != Lambda'_P$.

There are two rather different approaches to the problem of determining which
elements of $R$ annihilate $op("Ext")(M,N)$ for all $M$ and $N$. One method is
to embed the given $R$-order $Lambda$ in a maximal order $Lambda'$ in $A$, and
then use the fact that every $Lambda'$-lattice is $Lambda'$-projective (see
@th:maximal-orders-are-hereditary). This usually yields stronger results than
the second method, due to D. G. Higman, in which one constructs an ideal
$i(Lambda)$ of $R$ such that
$
  i(Lambda) dot H^1(Lambda,T)=0 "for every" (Lambda,Lambda)"-bimodule" T.
$ <eq:higman-ideal-cohomology-annihilator>
By @prop:extensions-bimodule-cohomology we have
$op("Ext")_Lambda^1 lr((M,N)) tilde.equiv H^1(Lambda,Hom_R (M,N))$ whenever $M$
and $N$ are $Lambda$-lattices, and hence
$
  i(Lambda) dot op("Ext")_Lambda^1 lr((M,N))=0
  "for all" Lambda"-lattices" M "and" N.
$ <eq:higman-ideal-ext-annihilator>
However, even though the _Higman ideal_ $i(Lambda)$ #idx("Higman ideal") is the
largest ideal of $R$ for
#source(626)
which @eq:higman-ideal-cohomology-annihilator holds, it is not necessarily the
largest ideal such that @eq:higman-ideal-ext-annihilator is valid.

Let $A$ be a f.d. separable $K$-algebra, and let $R$ be a Dedekind domain with
quotient field $K$. Let $C$ denote the integral closure of $R$ in the center of
$A$. By @prop:commutative-separable-unique-maximal-order, $C$ is the unique
maximal $R$-order in this center. Furthermore, every maximal $R$-order $Lambda'$
in $A$ must contain $C$, since otherwise $C Lambda'$ is a larger order. The
following concept was first introduced in §@sec:group-rings-maximal-orders:

#definition[
  Let $Lambda$ be an $R$-order in $A$, and let $Lambda subset.eq Lambda'$, where
  $Lambda'$ is a maximal $R$-order in $A$. The _central conductor_ of $Lambda'$
  into $Lambda$ #idx("central conductor") #idx("conductor") is defined to be
  $ F={c in C:c Lambda' subset.eq Lambda}. $
] <def:central-conductor-ext>

Now $alpha Lambda' subset.eq Lambda$ for some nonzero $alpha in R$, so
$alpha in F$, and therefore also $alpha C subset.eq F$. Thus $F$ is an ideal of
$C$ such that $K dot F=K dot C="center of" A$. Further, $F subset.eq Lambda$
since $1 in Lambda'$.

We now prove the following basic result due to Jacobinski @bib:Jacobinski1966:

#theorem[
  Let $Lambda$ be an $R$-order in a semisimple $K$-algebra $A$, and let $F$ be
  the central conductor of $Lambda'$ into $Lambda$, where $Lambda'$ is a maximal
  $R$-order in $A$ containing $Lambda$. Then:
  #idx("Jacobinski's Theorem")
  $
    F dot op("Ext")_Lambda^1 lr((M,N))=0
    "for all" Lambda"-lattices" M "and all" Lambda"-modules" N.
  $
] <th:central-conductor-ext-annihilator>

#proof[
  We write $op("Ext")$ in place of $op("Ext")_Lambda^1$, and $Hom$ in place of
  $Hom_Lambda$, for convenience. Given a $Lambda$-lattice $M$, let
  $ 0 -> X arrow.r^i Y -> M -> 0 $
  be a $Lambda$-exact sequence with $Y=Lambda^((k)) subset.eq A^((k))$ and $i$
  the inclusion map. Then for any $Lambda$-module $N$,
  @rem:ext-long-exact-sequence(iii) gives
  $ op("Ext")(M,N) tilde.equiv Hom(X, N) slash i^ast {Hom(Y, N)}. $
  We need only show that for each $f in Hom(X, N)$ and each $c in F$, the
  element $c f$ lies in the image of $i^ast$. Note that $c f$ is a
  $Lambda$-homomorphism since $c$ lies in the center of $Lambda$.

  We set $Y'=Lambda'Y$ (computed inside $A^((k))$), so $Y'=Lambda'^((k))$. Let
  $X_1=K X inter Y'$, an $R$-pure $Lambda'$-sublattice of $Y'$ by
  @cor:full-order-lattice-existence; then $Y' slash X_1$ is a $Lambda'$-lattice,
  hence is $Lambda'$-projective by @th:maximal-orders-are-hereditary. Therefore
  the exact sequence
  $ 0 -> X_1 -> Y' -> Y' slash X_1 -> 0 $
  is $Lambda'$-split, so there exists a map $j in Hom_(Lambda')(Y',X_1)$ which
  splits the inclusion $X_1 subset.eq Y'$; in other words, $j$ restricted to
  $X_1$ is the identity map.

  #source(627)
  Now let $f$ and $c$ be given, so $c Lambda' subset.eq Lambda$, and hence
  $c Y' subset.eq Y$. Since $Y slash X tilde.equiv M$ and $M$ is a
  $Lambda$-lattice, it follows that $X$ is $R$-pure in $Y$, and thus
  $X=K X inter Y subset.eq X_1$. Therefore
  $ c X_1=c(K X inter Y') subset.eq K X inter c Y' subset.eq K X inter Y=X. $
  We may thus define $f_1 in Hom_Lambda (X_1, N)$ by setting
  $f_1(x_1)=f(c x_1),x_1 in X_1$. Then $f_1$ extends the map $c f:X -> N$.

  Consider the commutative diagram
  #conductor-extension-diagram()
  in which each map is a $Lambda$-homomorphism. Let $g$ be the restriction of
  $f_1 j$ to the $Lambda$-submodule $Y$ of $Y'$. Then $g in Hom(Y, N)$ and
  $i^ast(g)=c f$. We have thus shown that $c f$ extends to a homomorphism from
  $Y$ to $N$, that is, $c f in im(i^ast)$, which completes the proof.
]

Keep the above notation; let $alpha in R$ be a nonzero element such that
$alpha Lambda' subset.eq Lambda$; then $alpha in R inter F$, which shows at once
that $R inter F$ is a nonzero ideal of $R$. Consequently, we obtain:

#corollary[
  Let $Lambda$ be any $R$-order in a separable $K$-algebra $A$. Then there
  exists a nonzero ideal $frak(c)$ of $R$ such that
  $
    frak(c) dot op("Ext")_Lambda^1 lr((M,N))=0
    "for every" Lambda"-lattice" M "and every" Lambda"-module" N.
  $
] <cor:uniform-order-ext-annihilator>

#proof[
  By @th:order-contained-in-maximal-order, $Lambda$ is contained in some maximal
  $R$-order $Lambda'$ in $A$, and it suffices to choose $frak(c)=R inter F$,
  where $F$ is the central conductor of $Lambda'$ into $Lambda$.
]

#remarks(numbered: false)[
  #enum(
    numbering: "(i)",
    [The proof of @th:central-conductor-ext-annihilator carries over unchanged
      to the case where $Lambda'$ is any _hereditary_ order, whether maximal or
      not. We could thus have chosen the ideal $frak(c)$ in
      @cor:uniform-order-ext-annihilator to be the ideal of $R$ generated by all
      elements in $R inter F$, with $F$ ranging over all central conductors of
      hereditary orders (above $Lambda$) into $Lambda$.
    ],
    [For a fixed order $Lambda$, the central conductor of $Lambda'$ into
      $Lambda$ may well depend on the choice of the maximal order $Lambda'$
      containing $Lambda$.
    ],
  )
]

#corollary[
  Let $Lambda,M$ and $N$ be as in @th:central-conductor-ext-annihilator, and let
  $e in C$ be idempotent. Let $M$ and $N$ be $Lambda$-lattices such that either
  $e M=M$ or $e N=N$. Then
  $ {alpha in R:alpha e in F} "annihilates" op("Ext")_Lambda^1 lr((M,N)). $
] <cor:central-idempotent-ext-annihilator>

#source(628)
#proof[
  Let $alpha in R$ be such that $alpha e in F$; then
  $alpha e dot op("Ext")(M,N)=0$ by @th:central-conductor-ext-annihilator. But
  $alpha e$ and $alpha$ act in the same way on $op("Ext")(M,N)$, since the
  hypothesis implies that $e$ acts as the identity map on either $M$ or $N$.
]

To conclude this part of the discussion, we present an improvement of
@cor:extension-primary-decomposition, which may in turn be viewed as a
generalization of @th:extension-localization-group-order:

#proposition[
  Let $Lambda$ be an $R$-order in a separable $K$-algebra $A$, and let
  $
    S(Lambda)={P:P="maximal ideal of" R,
      Lambda_P != "maximal" R_P"-order in" A}.
  $
  Let $M$ and $N$ be left $Lambda$-lattices. Then
  $
    op("Ext")_Lambda^1 lr((M,N)) tilde.equiv
    product_(P in S(Lambda)) op("Ext")_(Lambda_P)^1 lr((M_P,N_P)).
  $
] <prop:extension-localization-nonmaximal-primes>

#proof[
  If $P in.not S(Lambda)$ then $Lambda_P$ is a maximal $R_P$-order, and $M_P$ is
  a $Lambda_P$-lattice. Then $M_P$ is $Lambda_P$-projective since $Lambda_P$ is
  hereditary (see @th:maximal-orders-are-hereditary), so
  $op("Ext")_(Lambda_P)^1 lr((M_P,ast))=0$ by §@sec:ext-tor-cohomology. The
  result now follows from @cor:extension-primary-decomposition.
]

We now restrict our attention to the special case where $Lambda=R G$ and
$A=K G$, with $K$ an algebraic number field and $G$ a finite group. In
@th:jacobinski-central-conductor we determined the central conductor $F$ of a
maximal $R$-order $Gamma$ into $Lambda$, namely
$ F=product_(i=1)^t (n slash n_i)frak(D)^(-1)(R_i slash R). $
Here, $product_(i=1)^t R_i$ is the integral closure of $R$ in the center of
$K G$, and $frak(D)^(-1)(R_i slash R)$ is the inverse different of $R_i$ with
respect to $R$. Further, $n=abs(G)$, and the ${n_i}$ are the integers defined in
@eq:group-algebra-component-degree. Let
$ 1=e_1+dots+e_t $
be the decomposition of 1 into central primitive idempotents in $A$. Then the
ideals ${A e_i}$ are the Wedderburn components of $A$, and the center of $A e_i$
is just $K_i$, the quotient field of $R_i$. By definition,
$ n_i^2=dim_(K_i) A_i, quad 1 <= i <= t. $
Let $e$ be a central idempotent in $A$, so that $e$ is a sum of a subset of
${e_1,dots,e_t}$. For $alpha in R$, we have $alpha e in F$ if and only if
$alpha in (n slash n_i)frak(D)^(-1)(R_i slash R)$ for each $e_i$ occurring in
$e$. As shown in the proof of @th:jacobinski-central-conductor, where
$frak(D)^(-1)(R_i slash R)$ was denoted by $delta_i^(-1)$, we have
$
  R inter (n slash n_i)frak(D)^(-1)(R_i slash R)
  =(n slash n_i)(K inter frak(D)^(-1)(R_i slash R))
  =(n slash n_i)delta_i^(-1),
$
#source(629)
where
$ delta_i^(-1)=K inter frak(D)^(-1)(R_i slash R) supset.eq R. $
<eq:contracted-inverse-different>
Note that $delta_i^(-1)$ is a fractional $R$-ideal in $K$, and its inverse
$delta_i$ is an ideal of $R$. From @cor:central-idempotent-ext-annihilator and
the above discussion, we obtain:

#theorem(title: [Jacobinski @bib:Jacobinski1966])[
  Let $M$ and $N$ be $R G$-lattices, and let
  $ I={i:1 <= i <= t,e_i M != 0}. $
  Then #idx("Jacobinski's Theorem")
  $
    inter.big_(i in I) (n slash n_i)delta_i^(-1)
    "annihilates" op("Ext")_(R G)^1 lr((M,N)).
  $
  In particular,
  $
    inter.big_(i=1)^t (n slash n_i)delta_i^(-1)
    "annihilates" op("Ext")(M,N)
  $
  for any $R G$-lattices $M$ and $N$.
] <th:jacobinski-component-ext-annihilator>

#corollary[
  Let $M$ and $N$ be $R G$-lattices#footnote[
    It suffices to assume $M$ an $R G$-lattice, and $N$ may be any $R G$-module.
  ], such that either $e_i M=M$ or $e_i N=N$. Then
  $ (n slash n_i)delta_i^(-1) dot op("Ext")(M,N)=0. $
] <cor:single-component-ext-annihilator>

If the $A$-module $K M$ is absolutely simple, then $End_A (K M) tilde.equiv K$;
this implies that $K_i=K$, $R_i=R$, and $delta_i^(-1)=R$. Further, in this case
$n_i=dim_K K M$, and we obtain:

#corollary[
  Let $M$ and $N$ be $R G$-lattices, where $K M$ is an absolutely simple
  $A$-module. Let $n_i=dim_K K M$. Then #idx("Reiner's Theorem")
  $ (n slash n_i)op("Ext")(M,N)=0 "for all" N. $
  An analogous result holds when $K N$ is absolutely simple.
] <cor:absolute-simple-ext-annihilator>

This corollary is due to Reiner @bib:Reiner1963. In the next subsection, we
shall show that the result is best possible (see
@cor:reiner-exact-ext-annihilator). We shall also discuss the question of
determining the largest ideal of $R$ which annihilates $op("Ext")(M,N)$ for
fixed $M$ and all $N$.

#source(630)
We conclude with a brief discussion of the Higman ideal. Let $Lambda$ be an
arbitrary $R$-order in a $K$-algebra $A$. By definition, the _Higman ideal_
$i(Lambda)$ #idx("Higman ideal") is the largest ideal of $R$ such that
@eq:higman-ideal-cohomology-annihilator holds true. As shown in
@bib:CurtisReiner1962[CR] (75.11), $i(Lambda) != 0$ if and only if $A$ is a
separable $K$-algebra. Further,
$ i(S^(-1)Lambda)=S^(-1) dot i(Lambda) $
for every multiplicative subset $S$ of $R$. In particular,
$ i(Lambda_P)={i(Lambda)}_P $
for each maximal ideal $P$ of $R$.

Suppose now that we are given a nondegenerate associative bilinear form
$f:A times A -> K$. We may use $f$ to calculate $i(Lambda)$, as follows: Let
$A=plus.o.big_(i=1)^n K a_i$, and let ${b_j}$ be a dual $K$-basis of $A$, chosen
so that $f(a_i,b_j)=delta_(i j),1 <= i,j <= n$. For $x in A$, let
$ c(x)=sum_(i=1)^n b_i x a_i. $ <eq:higman-casimir-map>
Then (see @bib:CurtisReiner1962[CR] §71) $c$ is a well defined map from $A$ into
its center, and does not depend on the choice of bases. Let
$c(A)={c(x):x in A}$; then $c(A)$ coincides with the center of $A$ if and only
if $A$ is a separable $K$-algebra (see @bib:CurtisReiner1962[CR] (71.6); the
result is due to D. G. Higman @bib:Higman1955b).

We now define the _inverse different_ $frak(D)^(-1)(Lambda slash R)$ #idx(
  "inverse different",
) and the _different_ $frak(D)(Lambda slash R)$ #idx("different") by the
formulas
$
  frak(D)^(-1)(Lambda slash R)={a in A:f(Lambda,a) subset.eq R},
  quad frak(D)(Lambda slash R)={x in A:frak(D)^(-1) dot x subset.eq Lambda}.
$
Then D. G. Higman's formula for $i(Lambda)$ is as follows (see
@bib:CurtisReiner1962[CR] (75.14)):
$ i(Lambda)=R inter c(frak(D)(Lambda slash R)), $
where $c$ is defined as in @eq:higman-casimir-map. Further, $i(Lambda) != 0$ if
and only if $A$ is a separable $K$-algebra. When $Lambda=R G$, we have
$i(Lambda)=abs(G)R$ (@bib:CurtisReiner1962[CR], §75, p. 528).

Let us now assume that $A$ is a separable $K$-algebra, and let $tr_(A slash K)$
be the reduced trace from $A$ to $K$. Then we obtain a nondegenerate associative
symmetric bilinear form $f$ by setting $f(a,b)=tr_(A slash K)(a b)$ for
$a,b in A$ (see §@ss:reduced-norms, or @bib:Reiner1975[MO] (9.26)). In that
case, $frak(D)$ is the usual different computed relative to reduced trace. In
particular, suppose that $A$ is commutative; then one verifies
(Exercise~@exc:trace-dual-basis-separable-field) that $c(x)=x$ for each
$x in A$, and hence
$ i(Lambda)=R inter frak(D)(Lambda slash R). $

#source(631)
When $Lambda'$ is a maximal order, we obtain
$ i(Lambda')=R inter frak(D)(Lambda' slash R). $
Now it may well happen that $i(Lambda') subset R$; for example, let $Lambda'$ be
the integral closure $S$ of $R$ in a finite separable field extension $L$ of
$K$. If some prime $P$ of $R$ ramifies in $S$, then
$P_1 supset.eq frak(D)(S slash R)$ for some prime $P_1$ of $S$ lying above $P$.
Then $P=R inter P_1 supset.eq R inter frak(D)(S slash R)$. Hence every prime of
$R$ ramified in $S$ is a divisor of the Higman ideal $i(S)$ relative to $R$.
However, $op("Ext")_S^1 lr((M,N))=0$ for every $S$-lattice $M$ and every
$S$-module $N$, so @th:central-conductor-ext-annihilator and
@cor:uniform-order-ext-annihilator are stronger results than
@eq:higman-ideal-ext-annihilator! Note that in this example, the central
conductor differs from the Higman ideal.

=== Projective Endomorphisms <ss:projective-endomorphisms>

Let $M$ and $N$ be left $Lambda$-modules, where $Lambda$ is any ring. In
§@sec:ext-tor-cohomology we saw that $End_Lambda M$ acts from the right on
$op("Ext")_Lambda^1 lr((M,N))$. Let us review this situation, interpreting
elements of $op("Ext")(M,N)$ as equivalence classes of extensions of $M$ by $N$.
Let $xi in op("Ext")(M,N)$ correspond to the class of the short exact sequence
of $Lambda$-modules
$ xi:0 -> N -> X arrow.r^mu M -> 0. $
Given any $phi in End M$, the class of $xi phi$ corresponds to a sequence
$ 0 -> N -> X_1 -> M -> 0, $
where $X_1$ is the pullback of the pair of maps $mu,phi$ (see
§@ss:homomorphisms). There is thus a commutative diagram #numbered-block[
  #pullback-endomorphism-diagram()
] <eq:ext-endomorphism-pullback>
We may identify $X_1$ with ${(x,m) in X plus.o M:mu(x)=phi(m)}$, and then
$ mu_1(x,m)=m, quad phi_1(x,m)=x, "for" (x,m) in X_1. $

#definition[
  A _projective endomorphism_ of $M$ #idx("projective endomorphism") is an
  element $phi in End_Lambda M$ such that $phi$ annihilates
  $op("Ext")_Lambda^1 lr((M,N))$ for each $N$.
] <def:projective-endomorphism>

Thus, in particular, $M$ is $Lambda$-projective if and only if the identity map
$1_M$ is a projective endomorphism of $M$. In general, $phi$ is a projective
endomorphism if and only if for each sequence $xi$ in
@eq:ext-endomorphism-pullback, the sequence $xi phi$ is split exact.

#source(632)
We now characterize projective endomorphisms in another way. Given a left
$Lambda$-module $M$, we may form its _dual_ $Hom_Lambda (M, Lambda)$ #idx(
  "dual of module",
), consisting of all left $Lambda$-homomorphisms from $M$ into $Lambda$. Since
$Lambda$ is a $(Lambda,Lambda)$-bimodule, the dual can be made into a right
$Lambda$-module in a natural way. Explicitly, for $f in Hom_Lambda (M, Lambda)$
and $lambda in Lambda$, we define $f lambda$ by
$ (f lambda)(m)=f(m)lambda, quad m in M. $
(The fact that $f lambda in Hom_Lambda (M, Lambda)$ is easily checked. It also
follows from general principles, if we recall from
§@sec:hom-tensor-projective-injective-flat that the right action of $Lambda$ on
the bimodule $attach(Lambda, bl: Lambda, br: Lambda)$ produces a right action of
$Lambda$ on $Hom_Lambda (M, Lambda)$.)

#proposition[
  Let $M$ be a f.g. left $Lambda$-module. Define
  $ tau:Hom_Lambda (M, Lambda) times.o_Lambda M -> End_Lambda M $
  by
  $
    tau(f times.o m):m' |-> f(m')m, quad
    m' in M,f in Hom_Lambda (M, Lambda),m in M,
  $
  extended by linearity. Then the image of $tau$ coincides with the set of
  projective endomorphisms of $M$.
] <prop:projective-endomorphism-dual-tensor>

#proof[
  It is easily checked that $tau$ is a well defined two-sided
  $End_Lambda (M)$-homomorphism, if we view $End_Lambda M$ as acting from the
  right on $M$ (see §@ss:morita-theorems). We may choose a $Lambda$-exact
  sequence $0 -> M' -> F -> M -> 0$, in which $F=plus.o.big_(i=1)^n Lambda x_i$
  is a free $Lambda$-module on $n$ generators ${x_i}$. If $phi in End_Lambda M$
  is a projective homomorphism, consider the commutative diagram with exact
  rows:
  #pullback-endomorphism-diagram(free: true)
  Since $phi$ is a projective endomorphism, there exists a map $rho:M -> F_1$
  which splits $mu_1$, that is, $mu_1 rho=1_M$. Write
  $ (phi_1 rho)(m)=sum_(i=1)^n f_i (m)x_i, $
  with each $f_i in Hom_Lambda (M, Lambda)$ (as is easily verified). Then
  $
    phi(m)=(phi mu_1 rho)(m)=(mu phi_1 rho)(m)
    =mu{sum f_i (m)x_i}=sum f_i (m)mu(x_i).
  $
  #source(633)
  It follows that
  $ phi=tau{sum_(i=1)^n f_i times.o mu(x_i)} in im tau, $
  as claimed.

  Let us show conversely that every $phi in im tau$ is a projective endomorphism
  of $M$. Suppose that
  $
    phi=tau{sum_(i=1)^k f_i times.o m_i}, quad
    f_i in Hom_Lambda (M, Lambda),m_i in M.
  $
  Then
  $ phi(m)=sum f_i (m)m_i, quad m in M. $
  Consider the diagram @eq:ext-endomorphism-pullback, and choose $x_i in X$ with
  $mu(x_i)=m_i,1 <= i <= k$. Now let
  $ rho(m)=(sum f_i (m)x_i,m) in X plus.o M "for" m in M. $
  Since
  $ mu{sum f_i (m)x_i}=phi(m) "for" m in M, $
  it follows that $rho in Hom_Lambda (M, X_1)$. Further, $mu_1 rho(m)=m$ for
  $m in M$, so $rho$ is a splitting of $mu_1$. Thus, for each
  $xi in op("Ext")_Lambda^1 lr((M,N))$, the class of sequences corresponding to
  $xi phi$ are split exact. This proves that $phi$ is a projective endomorphism,
  and establishes the proposition.
]

#corollary[
  Let $R$ be a Dedekind domain, $Lambda$ an $R$-algebra, $M$ a finitely
  presented left $Lambda$-module, and $phi in End_Lambda M$. Then $phi$ is a
  projective endomorphism of $M$ if and only if for each maximal ideal $P$ of
  $R$, the localization $phi_P$ is a projective endomorphism of $M_P$.
] <cor:projective-endomorphism-localization>

#proof[
  This follows at once from @prop:projective-endomorphism-dual-tensor and
  @prop:localization-criteria.
]

In order to apply @prop:projective-endomorphism-dual-tensor to the case where
$Lambda$ is an integral group ring $R G$, we need another characterization of
the dual $Hom_(R G)(M,R G)$ of a left $R G$-module $M$.

#lemma[
  Let $Lambda=R G$, where $G$ is a finite group and $R$ is any commutative ring.
  Let $M$ be any left $Lambda$-module. Then there is an isomorphism of right
  $Lambda$-modules
  $ theta:Hom_R (M,R) tilde.equiv Hom_Lambda (M, Lambda), $
  #source(634)
  given by
  $ theta(h):m |-> sum_(x in G) h(x^(-1)m)x, quad m in M. $
  In other words, $theta(h)=sum_x x h x^(-1)$.
] <lem:group-ring-dual-transfer>

#proof[
  We have already seen in Proposition~@prop:frobenius-right-adjoint that $theta$
  is an $R$-isomorphism, so it suffices to verify that
  $ theta(h y)=theta(h)y "for all" h in Hom_R (M,R),y in G. $
  For $m in M$, we have
  $
    {theta(h y)}m & = sum_x (h y)(x^(-1)m) dot x
                    =sum_x h(y x^(-1)m) dot x \
                  & =sum_(z in G) h(z^(-1)m) dot z y
                    ={theta(h)m}y={theta(h)y}m,
  $
  as desired. This completes the proof. Note that $Hom_R (M,R)$ has been made
  into a right $Lambda$-module by using the $(Lambda,R)$-bimodule structure of
  $M$.
]

We shall combine this lemma with @prop:projective-endomorphism-dual-tensor to
obtain a useful description of the projective endomorphisms of an $R G$-lattice.
The result is due to D. G. Higman @bib:Higman1957; for a direct proof, see also
Reiner @bib:Reiner1963.

#theorem[
  Let $Lambda=R G$ with $G$ a finite group and $R$ an arbitrary commutative
  ring. Let $M$ be a left $Lambda$-lattice (that is, a left $Lambda$-module f.g.
  and projective over $R$). Let $phi in End_Lambda M$, then $phi$ is a
  projective endomorphism of $M$ if and only if
  $ phi=sum_(x in G) x h x^(-1) "for some" h in End_R M. $
] <th:higman-projective-endomorphism-transfer>

#proof[
  Let $sigma:End_R (M) -> End_Lambda (M)$ be the additive $R$-homomorphism
  defined by
  $ sigma(h)=sum_(x in G) x h x^(-1), quad h in End_R (M). $
  Let $tau_0:Hom_R (M,R) times.o_R M -> End_R (M)$ be defined as in
  @prop:projective-endomorphism-dual-tensor, using $Lambda=R$ in the definition.
  Then $tau_0$ is surjective, since $M$ is $R$-projective.

  It is easily verified that the following diagram is commutative, where $theta$
  is defined as in @lem:group-ring-dual-transfer:
  #projective-trace-diagram()
  #source(635)
  Since both $tau_0$ and $theta times.o 1$ are surjective, it follows at once
  that $im tau=im sigma$. This implies the desired result, by
  @prop:projective-endomorphism-dual-tensor. (A related result is given in
  @th:gaschutz-relative-projectivity(iii).)
]

#corollary(title: [Reiner @bib:Reiner1963])[
  Let $G$ be a finite group of order $n$, and $R$ a Dedekind domain with
  quotient field $K$, where $"char" K divides.not n$. Let $M$ be an
  $R G$-lattice such that $K M$ is an absolutely simple $K G$-module, and let
  $d=dim_K K M$. Then $d divides n$, and for any $a in R$ we have
  #idx("Reiner's Theorem")
  $
    a dot op("Ext")_(R G)^1 lr((M,ast))=0
    "if and only if" a in (n slash d)R.
  $
] <cor:reiner-exact-ext-annihilator>

#proof[
  The ring $End_Lambda M$ is an $R$-order in $End_(K G)(K M)$. But
  $End_(K G)(K M) tilde.equiv K$ since $K M$ is absolutely simple, and thus it
  follows that $End_Lambda (M) tilde.equiv R$. Hence
  $a dot op("Ext")_(R G)^1 lr((M,ast))=0$ if and only if $a_l$ is a projective
  endomorphism of $M$, where $a_l$ denotes left multiplication by $a$ on $M$. By
  @th:higman-projective-endomorphism-transfer, this occurs precisely when
  $ a_l=sum_(x in G) x h x^(-1) "for some" h in End_R (M). $
  <eq:absolute-simple-scalar-transfer>
  Thus, we must prove that @eq:absolute-simple-scalar-transfer holds if and only
  if $a in (n slash d)R$.

  For each $h in End_R (M)$, let $T(h)$ denote the trace of the $K$-linear
  transformation of $K M$ induced by $h$; then $T(h) in R$ by
  @prop:order-elements-integral. Further, $T(x h x^(-1))=T(h)$ for each
  $x in G$. Finally, for each $h$ the expression $sum x h x^(-1)$ gives an
  element of $End_(R G)(M)$, hence equals $a_l$ for some $a in R$. Taking traces
  on both sides, we obtain the equation
  $ d dot a=n T(h). $
  In particular, choosing $h$ so that $T(h)=1$, we see that $n slash d in R$,
  whence also#footnote[
    Since $n slash d$ lies in every $R$, it belongs to
    $QQ inter "alg. int." {K}$ (assuming $K$ is an algebraic number field), and
    so $n slash d in ZZ$. This also holds for arbitrary $K$, by
    @prop:character-degree-divides-group-order and
    Exercise~@exc:prime-to-p-projective-lifts.
  ] $n slash d in ZZ$, so $d divides n$. Secondly, for arbitrary $h$ we obtain
  $a=(n slash d)T(h) in (n slash d)R$ whenever
  @eq:absolute-simple-scalar-transfer holds. This completes the proof. The
  result strengthens that of @cor:absolute-simple-ext-annihilator.
]

To conclude this subsection, we present Roggenkamp's @bib:Roggenkamp1971 partial
converse of Theorem~@th:jacobinski-component-ext-annihilator. Let $A=K G$,
$Lambda=R G$, where $R$ is a Dedekind domain whose quotient field $K$ is an
algebraic number field. Let $Lambda'$ be a maximal $R$-order in $A$ such that
$Lambda' supset Lambda$, and let $(Lambda':Lambda)_l$ be the left conductor of
$Lambda'$ into $Lambda$ (see @def:left-right-conductor). Let $e$ be a central
idempotent of $A$, and view $Lambda'e$ as left $Lambda$-module. Then each
$f in Hom(Lambda'e, Lambda)$ is given by right multiplication $a_r$ for some
$a in A$ such that $a e in (Lambda':Lambda)_l$. Since $a_r=(a e)_r$, we thus
have an identification
$Hom(Lambda'e, Lambda) tilde.equiv A e inter (Lambda':Lambda)_l$. Both $A e$ and
$(Lambda':Lambda)_l$ are two-sided $Lambda'$-modules (see
@th:jacobinski-conductor-formula), whence so is their intersection.

#source(636)
Let
$ tau:Hom(Lambda'e, Lambda) times.o_Lambda Lambda'e -> End_Lambda Lambda'e $
be the map defined as in @prop:projective-endomorphism-dual-tensor. Identifying
$End_Lambda Lambda'e$ with $Lambda'e$, we see that we may also identify the
image of $tau$ with
$ {A e inter (Lambda':Lambda)_l} dot Lambda'e=A e inter (Lambda':Lambda)_l. $
Thus, the projective endomorphisms of the left $Lambda$-lattice $Lambda'e$ are
given by right multiplications by elements of $A e inter (Lambda':Lambda)_l$. In
particular, for $alpha in R$ we have (see
@cor:single-component-ext-annihilator): #numbered-block[
  $
    cases(
      alpha dot op("Ext")_Lambda^1 lr((Lambda'e,ast))=0,
      "if and only if" alpha in (n slash n_i)delta_i^(-1)
      "for each idempotent summand" e_i "of" e.
    )
  $
] <eq:maximal-order-summand-ext-annihilator>
From this result we obtain:

#theorem(title: [Roggenkamp @bib:Roggenkamp1971])[
  Let $alpha in R$. Then #idx("Roggenkamp's Theorem")
  #enum(
    numbering: "(i)",
    [$alpha dot op("Ext")_Lambda^1 lr((M,N))=0$ for all $Lambda$-lattices $M$
      and $N$ if and only if
      $ alpha in inter.big_(i=1)^t (n slash n_i)delta_i^(-1), $
      using the notation of @th:jacobinski-component-ext-annihilator.
    ],
    [For each central idempotent $e$ of $A$, there exists a $Lambda$-lattice $M$
      (namely $Lambda'e$) such that $e M=M$, and such that
      $
        alpha dot op("Ext")_Lambda^1 lr((M,ast))=0
        "if and only if" alpha in inter.big_(e_i divides e)
        (n slash n_i)delta_i^(-1),
      $
      where the intersection is over all indices $i$ for which the central
      primitive idempotent $e_i$ occurs as a summand of $e$.
    ],
    [For each central primitive idempotent $e_i$ of $A$, there exists a
      $Lambda$-lattice $M$ (namely $Lambda'e_i$) such that $e_i M=M$, and such
      that
      $
        alpha dot op("Ext")_Lambda^1 lr((M,ast))=0
        "if and only if" alpha in (n slash n_i)delta_i^(-1).
      $ <eq:component-sharp-ext-annihilator>
    ],
  )
] <th:roggenkamp-sharp-ext-annihilator>

Note that we have not proved a complete converse to
@th:jacobinski-component-ext-annihilator and
@cor:single-component-ext-annihilator. For example, we have not settled the
following question: let $M$ be a $Lambda$-lattice such that $K M$ is simple, and
let $e_i$ be the central idempotent such that
#source(637)
$e_i M=M$. Does @eq:component-sharp-ext-annihilator hold true in this case?
Reiner's Theorem~@cor:reiner-exact-ext-annihilator shows that it holds whenever
$K M$ is absolutely simple, but there is still a gap for the case where $K M$ is
simple but not absolutely simple. Further results on this problem may be found
in Plesken @bib:Plesken1978.

#remarks(name: "Notes")[
  #enum(
    numbering: "(i)",
    [Let $G$ be a finite group having a normal cyclic Sylow $p$-subgroup $H$,
      and let $hat(ZZ),hat(QQ)$, etc., denote $p$-adic completions. Let $M$ and
      $N$ be $hat(ZZ)G$-lattices such that $hat(QQ)M tilde.equiv hat(QQ)N$, and
      $hat(QQ)M$ is simple. Berman @bib:Berman1966 proved that
      $ op("Ext")_(hat(ZZ)G)^1 lr((hat(M),hat(N)))=0. $
      Gudivok observed that the analogous statement fails when $hat(ZZ)$ is
      replaced by some larger $P$-adic ring. Indeed, the results in
      Exercise~@exc:nonintegrally-closed-cyclotomic-order-extensions lead to a
      counterexample.
    ],
    [Let $R="alg. int." {K}$, and let $V$ and $W$ be f.g. left $K G$-modules.
      Put
      $ sigma(V)={M:M="full" R G"-lattice in" V}. $
      Several authors have considered the question as to whether
      $
        op("Ext")_(R G)^1 lr((M,N))=0
        "for all" M in sigma(V),N in sigma(W),
      $
      and obtained _sufficient conditions_ in certain special cases. See the
      work of Berman-Lichtman @bib:Berman1965a, generalized by Reiner
      @bib:Reiner1967. Also see Plesken @bib:Plesken1978.
    ],
  )
] <rem:integral-extension-vanishing>

#exercises-heading

#exercise[
  Let $L$ be a finite separable field extension of $K$, and let $T:L -> K$ be
  the trace map. Let $f:L times L -> K$ be the bilinear trace form given by
  $f(a,b)=T(a b)$ for $a,b in L$. If ${a_i}$ and ${b_j}$ are dual bases of $L$
  over $K$ relative to $f$, show that
  $ sum a_i b_i=1. $
] <exc:trace-dual-basis-separable-field>

#hint([@exc:trace-dual-basis-separable-field])[
  Let $L=plus.o.big_(i=1)^n K a_i$, $T(a_i b_j)=delta_(i j)$, $1 <= i,j <= n$.
  For $x in L$, write
  $ x a_i=sum_(j=1)^n alpha_(i j)a_j, quad alpha_(i j) in K,1 <= i <= n. $
  Then
  $ sum_i T(x a_i b_i)=sum_(i,j) alpha_(i j)T(a_j b_i)=sum_i alpha_(i i)=T(x). $
  Hence
  $ f(x,1-sum_i a_i b_i)=0 "for all" x in L, $
  and so $sum a_i b_i=1$.
]

#source(638)
#exercise[
  Prove the analogous result when $L$ is a commutative separable $K$-algebra.
  Can the hypothesis of commutativity be omitted?
] <exc:trace-dual-basis-separable-algebra>

#exercise[
  Let $Lambda$ be any ring. Show that the set of projective endomorphisms of a
  left $Lambda$-module $M$ is a two-sided ideal of $End_Lambda (M)$.
] <exc:projective-endomorphisms-ideal>

#exercise[
  Let $M$ and $N$ be $R G$-lattices, and keep the notation of
  @th:jacobinski-component-ext-annihilator. Show that
  $n slash "G.C.D." (n_1,dots,n_t)$ annihilates $op("Ext")_(R G)^1 lr((M,N))$.
] <exc:gcd-degree-ext-annihilator>

#exercise[
  Let $R$ be a commutative ring, $G$ a finite group, $H$ a subgroup of $G$, and
  $M$ a left $R G$-module. Suppose there exists an $h in End_(R H)(M)$ such that
  $sum_(i=1)^n x_i h x_i^(-1)=1_M$, where $G=union.big_(i=1)^n x_i H$. Show that
  every exact sequence of $R G$-modules
  $ 0 -> X -> Y -> M -> 0 $
  which splits over $R H$ also splits over $R G$. (See also
  §@ss:relative-projectivity.)
] <exc:relative-transfer-splitting>

#exercise[
  Use Theorem~@th:higman-projective-endomorphism-transfer to give another proof
  of Exercise~@exc:trace-surjective-galois-projective.
] <exc:unramified-galois-projectivity-transfer>

#hint([@exc:unramified-galois-projectivity-transfer])[
  Let $s_0 in S$ be such that $T_(L slash K)(s_0)=1$. In
  @th:higman-projective-endomorphism-transfer let $h$ be left multiplication by
  $s_0$ on $S$. Then $sum_(x in G) x h x^(-1)=T_(L slash K)(s_0)=1$, so the
  identity map on $S$ is a projective endomorphism. Therefore $S$ is
  $R G$-projective.
]
