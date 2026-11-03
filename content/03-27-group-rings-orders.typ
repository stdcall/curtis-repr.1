#import "main-defs.typ": *
#import "statements.typ": *

== Group Rings and Maximal Orders <sec:group-rings-maximal-orders>

In this section, $R$ denotes a Dedekind domain with quotient field $K$, and
$Lambda$ is an $R$-order in a f.d. $K$-algebra $A$. We saw in
§@sec:maximal-hereditary-orders that a great deal of detailed information is
available about maximal orders and their ideal theory. We hope to use these
facts to study the representation theory of an arbitrary order $Lambda$, and
when such a maximal overorder exists, begin by embedding $Lambda$ in a maximal
order $Gamma$ in $A$. If we have enough information about the relation between
$Lambda$ and $Gamma$ we can derive significant results about the representations
of $Lambda$. For example, if $Lambda$ is a commutative order in a separable
$K$-algebra $A$, then we can decide whether the number of isomorphism classes of
indecomposable $Lambda$-lattices is finite or not, merely by computing the
minimal number of generators of the $Lambda$-modules $Gamma slash Lambda$ and
$rad lr((Gamma slash Lambda))$ (see §@ss:commutative-orders-finite-type).

In the general case, we may also measure the relation between $Lambda$ and
$Gamma$ by means of the _conductor_
$ (Gamma:Lambda)={x in A:x Gamma subset.eq Lambda}, $
which is the largest right $Gamma$-module contained in $Lambda$. We have already
seen in §@sec:extensions-lattices the importance of the groups
$op("Ext")_Lambda^1 lr((M,N))$, where $M$ and $N$ are $Lambda$-lattices. It will
be shown in @th:central-conductor-ext-annihilator that if $alpha$ lies in the
center of $A$, and is such that
#source(604)
$alpha Gamma subset.eq Lambda$, then
$ alpha dot op("Ext")_Lambda^1 lr((M,N))=0 $
for all lattices $M$ and $N$. This gives some idea of the importance of being
able to determine the conductor $(Gamma:Lambda)$.

Our main result in this section is Jacobinski's explicit formula for the
conductor $(Gamma:R G)$, where $Gamma$ is a maximal $R$-order in $K G$
containing the integral group ring $R G$ of a finite group $G$. This formula
depends on the use of the reduced trace from $K G$ to $K$, and the reader may
wish to review the first half of §@ss:reduced-norms before proceeding.

(A given order $Lambda$ can usually be embedded in more than one maximal order
$Gamma$. Of course, when $A$ is a commutative separable $K$-algebra, there is a
unique maximal $R$-order in $A$, by
@prop:commutative-separable-unique-maximal-order. In the noncommutative case,
however, there are usually many distinct maximal orders in $A$ (see
@exm:maximal-order-constructions[Example (iii)]). In studying a hereditary order
$Lambda$, it is vital to know which maximal orders contain $Lambda$. For further
details about this question, see @bib:Reiner1975[MO (39.23) and (40.8)].)

Our first result gives a simple but useful relation between an integral group
ring $R G$ and any $R$-order in $K G$ containing $R G$.

#proposition[
  Let $G$ be a finite group of order $n$, and suppose that
  $char K divides.not n$. Let $Lambda'$ be any $R$-order containing $R G$. Then
  $ R G subset.eq Lambda' subset.eq n^(-1) dot R G. $
  The group ring $R G$ is a maximal order in $K G$ if and only if $n^(-1) in R$.
] <prop:group-ring-maximality>
#proof[
  Let $T$ be the ordinary trace map from $K G$ to $K$. Using the elements of $G$
  as $K$-basis for $K G$, we have
  $ T(x)=cases(n & quad x=1, 0 & quad x in G-{1}). $
  Now let $lambda in Lambda'$, and write $lambda=sum_(y in G) a_y y$, with each
  $a_y in K$. For any $x in G$ we have $lambda x^(-1) in Lambda'$, so
  $T lr((lambda x^(-1))) in R$ by @prop:order-elements-integral. But
  $ T lr((lambda x^(-1)))=sum_y a_y T lr((y x^(-1)))=n a_x,quad x in G. $
  Thus each $a_x in n^(-1) R$, so $lambda=sum a_x x in n^(-1) dot R G$. This
  establishes the desired inclusion, and shows that $R G$ is maximal whenever
  $n^(-1) in R$.

  On the other hand, let $R G$ be a maximal order, and let
  $ e=n^(-1) sum_(x in G) x. $
  #source(605)
  Then $e$ is a central idempotent of $K G$, and $y e=e$ for all $y in G$. It
  follows at once that $R G+R e$ is also an $R$-order in $K G$, whence
  $e in R G$ (since $R G$ is assumed maximal). But $e in R G$ implies
  $n^(-1) in R$, completing the proof.
]

Our aim is to prove Jacobinski's refinement of this result (see
@th:jacobinski-conductor-formula), which is obtained by using reduced trace
instead of ordinary trace. We begin with the following:

#definition[
  Let $Lambda subset.eq Gamma$ be a pair of rings. We define
  $
    & "left conductor of" Gamma "into" Lambda
      =(Gamma:Lambda)_l={x in Gamma:x Gamma subset.eq Lambda} \
    & quad ="largest right" Gamma "-module in" Lambda, \
    & "right conductor of" Gamma "into" Lambda
      =(Gamma:Lambda)_r={x in Gamma:Gamma x subset.eq Lambda} \
    & quad ="largest left" Gamma "-module in" Lambda.
  $
] <def:left-right-conductor>
#idx("conductor", target: [@def:left-right-conductor])

Now let $Lambda=R G$, where $G$ is a finite group of order $n$, and where we
assume that $char K divides.not n$. Let $Lambda subset.eq Gamma$, where $Gamma$
is a maximal $R$-order in $K G$. We shall compute the conductors of $Gamma$ into
$Lambda$. For this purpose, it is first necessary to introduce some notation.
The group algebra $A=K G$ is a separable $K$-algebra, and we may write
$ A=K G=A_1 plus.o dots plus.o A_t, $ <eq:group-algebra-simple-components>
where the ${A_i}$ are the simple components of $A$. If $K_i$ is the center of
$A_i$, then $K_i$ is a finite extension field of $K$, and we have (by
@cor:maximal-subfield-degree)
$ dim_(K_i) A_i=n_i^2,quad 1<=i<=t, $ <eq:group-algebra-component-degree>
for some integers ${n_i}$. Let $R_i$ denote the integral closure of $R$ in
$K_i$. By @th:maximal-orders-wedderburn-components we may write
$
  Gamma=Gamma_1 plus.o dots plus.o Gamma_t,quad
  "where" Gamma_i "is a maximal" R_i "-order in" A_i,quad 1<=i<=t.
$ <eq:maximal-group-order-components>
For each $i$, let $tr_i$ denote the reduced trace from $A_i$ to $K$. By
@eq:reduced-trace-norm-center-transitivity we have
$ tr_i=T_(K_i slash K) compose tr_(A_i slash K_i), $
<eq:group-component-trace-transitivity>
where $T_(K_i slash K)$ is the ordinary trace from $K_i$ to $K$, and
$tr_(A_i slash K_i)$ is the reduced trace from $A_i$ to $K_i$. Since each $A_i$
is a simple algebra of dimension $n_i^2$ over its center, it follows from
@eq:simple-algebra-trace-norm-reduced-power that the ordinary trace
$T_(A_i slash K)$ is equal to $n_i dot tr_i$. Therefore we obtain
$
  T_(A slash K) lr((x))=sum_(i=1)^t n_i tr_i lr((x_i)),quad
  "where" x=sum x_i,quad x_i in A_i.
$ <eq:group-algebra-ordinary-reduced-trace>

#source(606)
Next, Proposition @prop:reduced-trace-nondegenerate asserts that the reduced
trace form $tr_i:A_i times A_i arrow K$ is a nondegenerate symmetric bilinear
form. We can therefore consider duality relative to this form, as in
§@ss:duals-lattices. With each full left $Gamma_i$-lattice $L$ in $A_i$, we can
associate a dual right $Gamma_i$-lattice $tilde(L)$ defined by
$ tilde(L)={x in A_i:tr_i lr((x L)) subset.eq R}. $
In particular, applying this construction to the two-sided $Gamma_i$-lattice
$Gamma_i$, we obtain a two-sided $Gamma_i$-lattice $tilde(Gamma)_i$ containing
$Gamma_i$, called the _inverse different_#idx("inverse different") of $Gamma_i$
with respect to the reduced trace form $tr_i$. For later use, we remark that, by
@th:maximal-order-ideal-factorization, the set of full two-sided
$Gamma_i$-lattices in $A_i$ is an abelian multiplicative group. Thus we may
write $tilde(Gamma)_i=frak(D)_i^(-1)$, where $frak(D)_i$ is a two-sided ideal of
$Gamma_i$. We call $frak(D)_i$ the _different_#idx("different") of $Gamma_i$
with respect to $tr_i$.

We are now ready to prove:

#theorem(name: [Theorem (Jacobinski @bib:Jacobinski1966)])[
  Let $Gamma$ be a maximal $R$-order containing the group ring $R G$. Keeping
  the notation above, we have
  $
    (Gamma:R G)_l=(Gamma:R G)_r=op("⨁", limits: #true)_(i=1)^t (n slash n_i)
    frak(D)_i^(-1).
  $
] <th:jacobinski-conductor-formula>
#idx(
  "Jacobinski's conductor formula",
  target: [@th:jacobinski-conductor-formula],
)
#proof[
  Let $T:A times A arrow K$ be the ordinary trace form, and let
  $G={x_1,dots,x_n}$. These ${x_i}$ form a $K$-basis of $A$, so by virtue of the
  formula for $T$ given in the proof of @prop:group-ring-maximality, the dual
  basis is precisely ${n^(-1) x_1^(-1),dots,n^(-1) x_n^(-1)}$. Let $Lambda=R G$,
  and let $tilde(Lambda)$ denote the dual of $Lambda$ with respect to this trace
  form $T$, so
  $ tilde(Lambda)={y in A:T lr((y Lambda)) subset.eq R}. $
  Since $Lambda=op("⨁", limits: #true)_1^n R x_i$, we have
  $
    tilde(Lambda)=op("⨁", limits: #true)_(i=1)^n R lr((n^(-1) x_i))=n^(-1)
    Lambda.
  $
  Next, let $M=(Gamma:Lambda)_r$; then $M$ is the largest left $Gamma$-lattice
  in $Lambda$, so its dual $tilde(M)$ (with respect to $T$) is the smallest
  right $Gamma$-lattice containing $tilde(Lambda)$. But then
  $ tilde(M)=tilde(Lambda) dot Gamma=n^(-1) Lambda dot Gamma=n^(-1) Gamma, $
  so
  $ M=tilde(tilde(M))="dual of" n^(-1) Gamma=n tilde(Gamma). $
  On the other hand, we may compute $tilde(Gamma)$ by working in each simple
  component, so that $tilde(Gamma)=plus.o tilde(Gamma)_i$, where
  $tilde(Gamma)_i$ is the inverse different of $Gamma_i$ with respect to the
  trace
  #source(607)
  form $T_(A_i slash K)$. Using @eq:group-algebra-ordinary-reduced-trace, we
  obtain
  $
    tilde(Gamma) & =op("⨁", limits: #true)_(i=1)^t tilde(Gamma)_i
                   =op("⨁", limits: #true)_(i=1)^t n_i^(-1) dot
                   ("dual of" Gamma_i "with respect to" tr_i) \
                 & =op("⨁", limits: #true)_(i=1)^t n_i^(-1) frak(D)_i^(-1).
  $
  Hence we obtain
  $
    (Gamma:Lambda)_r=M=n tilde(Gamma)=op("⨁", limits: #true)_(i=1)^t (n slash
      n_i) frak(D)_i^(-1),
  $
  which establishes the theorem, since a similar argument works for
  $(Gamma:Lambda)_l$.
]

This theorem gives a surprisingly explicit expression for the largest
$Gamma$-ideal inside $Lambda$. The fact that the left and right conductors
coincide is also of interest, and will be needed in
§@ss:projective-endomorphisms. As an illustration of the strength of
Jacobinski's Theorem, we shall deduce a number of important consequences. _For
the rest of this discussion, we restrict our attention to the case where $K$ is
an algebraic number field, and $R=op("alg. int."){K}$._ For each $i$, $1<=i<=t$,
we have
$
  n slash n_i in (n slash n_i) frak(D)_i^(-1) subset.eq (Gamma:Lambda)_r
  subset.eq Lambda,
$
since $frak(D)_i^(-1) supset.eq Gamma_i$. But $Lambda=R G$, so we obtain
$ n_i "divides" n,quad 1<=i<=t. $ <eq:group-component-degree-divisibility>
This result contains significant information about Schur indices and the degrees
of the absolutely irreducible complex representations of $G$, as we shall now
explain.

For each $i$, $1<=i<=t$, we may write
$
  A_i=M_(k_i) lr((D_i)),quad D_i="division algebra with center" K_i,quad
  dim_(K_i) D_i=m_i^2.
$ <eq:group-component-division-index>
We call $m_i$ the _index_#idx("index") of $D_i$, and note that $n_i=m_i k_i$. If
$V_i$ is the simple left $A$-module corresponding to a simple left ideal in
$A_i$, then $m_i$ is called the _Schur index_#idx("Schur index") of $V_i$
relative to $K$ (see Chapter~6 of Volume~II). From
@eq:group-component-degree-divisibility we obtain at once:

#theorem[
  For each $i$, $m_i k_i$ is a divisor of $|G|$. In particular, the Schur
  indices of the simple $K G$-modules are divisors of $|G|$.
] <th:schur-index-divides-group-order>

We also obtain another proof of the basic result
@prop:character-degree-divides-group-order about dimensions of absolutely simple
modules:

#theorem[
  The degrees of the absolutely irreducible complex representations of $G$ are
  divisors of $|G|$.
] <th:jacobinski-irreducible-degree-divisibility>
#source(608)
#proof[
  In the preceding discussion, choose $K$ to be a splitting field for $G$. Then
  for each $i$, $1<=i<=t$, we have
  $ A_i tilde.equiv M_(n_i) lr((K)),quad k_i=n_i,quad m_i=1. $
  The integers ${n_i}$ are precisely the degrees of the absolutely irreducible
  complex representations of $G$, and $n_i divides n$ by
  @th:schur-index-divides-group-order, so the theorem is proved.
]

To conclude this section, let us derive Jacobinski's formula for the central
conductor of the maximal order $Gamma$ into the integral group ring
$Lambda=R G$. We assume throughout that $R=op("alg. int."){K}$. Let $C$ denote
the integral closure of $R$ in the center of $K G$, so we may write
$ C=R_1 plus.o dots plus.o R_t,quad R_i="integral closure of" R "in" K_i. $
Then $C$ is the unique maximal $R$-order in the center of $K G$, and is
contained in $Gamma$ (since otherwise $C Gamma$ is a larger $R$-order in $K G$).
We define the _central conductor_#idx("central conductor")#idx("conductor") of
$Gamma$ into $Lambda$ as follows:
$
  "central conductor"=C inter (Gamma:Lambda)_l={c in C:c Gamma subset.eq
    Lambda}.
$
As a consequence of @th:jacobinski-conductor-formula, we now prove:

#theorem[
  Let $R=op("alg. int."){K}$, $Lambda=R G$, $Gamma$ a maximal $R$-order in $K G$
  containing $Lambda$.
  #enum(
    numbering: "(i)",
    [The central conductor $F$ of $Gamma$ into $Lambda$ is given by
      $
        F=op("⨁", limits: #true)_(i=1)^t (n slash n_i) frak(D)^(-1) lr(
          (R_i
            slash R)
        ),
      $
      where
      $
        frak(D)^(-1) lr((R_i slash R))={x in K_i:T_(K_i slash K) lr((x R_i))
          subset.eq R},
      $
      which is (by definition) the inverse different of $R_i$ relative to $R$
      (see §@ss:dedekind-ideal-theory).],
    [We have
      $
        R inter F=inter.big_(i=1)^t (n slash n_i){K inter frak(D)^(-1) lr(
            (R_i
              slash R)
          )}.
      $],
  )
] <th:jacobinski-central-conductor>
#proof[
  For each $i$, $1<=i<=t$, we set
  $
    frak(d)_i^(-1)={x in A_i:tr_(A_i slash K_i) lr((x Gamma_i)) subset.eq R_i},
  $
  the inverse different of $Gamma_i$ with respect to $tr_(A_i slash K_i)$. For
  convenience of notation,
  #source(609)
  let
  $ delta_i^(-1)=frak(D)^(-1) lr((R_i slash R)), $
  so $delta_i$ is an ideal of $R_i$. Let us begin by deducing from
  @eq:group-component-trace-transitivity that
  $ frak(D)_i^(-1)=frak(d)_i^(-1) delta_i^(-1). $
  Indeed, for $x in A_i$ we have
  $
    x in frak(D)_i^(-1)
    &arrow.l.r tr_i lr((x Gamma_i)) subset.eq R_i
    arrow.l.r T_(K_i slash K) lr((tr_(A_i slash K_i) lr((x Gamma_i))))
    subset.eq R \
    &arrow.l.r T_(K_i slash K) lr((tr_(A_i slash K_i) lr((x R_i Gamma_i))))
    subset.eq R
    arrow.l.r T_(K_i slash K) lr((R_i dot tr_(A_i slash K_i) lr((x Gamma_i))))
    subset.eq R \
    &arrow.l.r tr_(A_i slash K_i) lr((x Gamma_i)) subset.eq delta_i^(-1)
    arrow.l.r tr_(A_i slash K_i) lr((x delta_i Gamma_i)) subset.eq R_i \
    &arrow.l.r x delta_i subset.eq frak(d)_i^(-1)
    arrow.l.r x in frak(d)_i^(-1) delta_i^(-1).
  $
  From the definition of the central conductor $F$, we have
  $
    F=C inter (Gamma:Lambda)_l=op("⨁", limits: #true)_(i=1)^t lr(
      (R_i inter (n
          slash n_i) frak(D)_i^(-1))
    ).
  $
  To prove assertion (i), it therefore must be shown that
  $ R_i inter (n slash n_i) frak(D)_i^(-1)=(n slash n_i) delta_i^(-1) $
  <eq:central-component-conductor-intersection>
  for each $i$, where $delta_i=frak(D) lr((R_i slash R))$. Let $y in R_i$. Then
  $
    y in (n slash n_i) frak(D)_i^(-1)
    &arrow.l.r y in (n slash n_i) frak(d)_i^(-1) delta_i^(-1) \
    &arrow.l.r y delta_i subset.eq (n slash n_i) frak(d)_i^(-1)
    arrow.l.r y delta_i subset.eq (n slash n_i) lr((K_i inter frak(d)_i^(-1))).
  $
  We may write $K_i inter frak(d)_i^(-1)=frak(a)^(-1)$, where $frak(a)$ is an
  ideal in $R_i$. We shall show that $frak(a)=R_i$. If $frak(a)!=R_i$, let $P$
  be a maximal ideal of $R_i$ containing $frak(a)$, and let $frak(p)$ be the
  prime ideal of $Gamma_i$ which corresponds to $P$ (see
  Exercise~@exc:maximal-order-primes-over-base). Then the power of $frak(p)$
  which occurs in the factorization of the different $frak(d)_i$ into the prime
  ideals of $Gamma_i$ is precisely $frak(p)^(e-1)$, where $P Gamma_i=frak(p)^e$
  (see @bib:Reiner1975[MO (25.7)]). Then
  $
    P supset.eq frak(a) arrow.r P^(-1) subset.eq frak(a)^(-1)
    arrow.r P^(-1) subset.eq frak(d)_i^(-1)
    arrow.r P Gamma_i supset.eq frak(d)_i.
  $
  After localizing at $P$, this containment implies that the exponent of
  $frak(p)$ in $frak(d)_i$ is at least $e$, contrary to the cited value $e-1$.
  This proves that $K_i inter frak(d)_i^(-1)=R_i$, and so
  $
    R_i inter (n slash n_i) frak(D)_i^(-1) subset.eq (n slash n_i) delta_i^(-1).
  $
  #source(610)
  To prove the reverse inclusion, we note that
  $
    (n slash n_i) delta_i^(-1) subset.eq (n slash n_i) frak(D)_i^(-1)
    subset.eq Lambda,
  $
  so each element of $(n slash n_i) delta_i^(-1)$ is integral over $R$, and
  therefore lies in $R_i$. This proves
  @eq:central-component-conductor-intersection, and establishes assertion (i).

  Finally, we have just verified that
  $(n slash n_i) delta_i^(-1) subset.eq R_i$. Since $K inter R_i=R$, we obtain
  $
    R inter F=(R inter C) inter (Gamma:Lambda)_l=
    inter.big_(i=1)^t lr((R inter (n slash n_i) delta_i^(-1))).
  $
  But for each $i$,
  $
    R inter (n slash n_i) delta_i^(-1)=K inter (n slash n_i) delta_i^(-1)=(n
      slash n_i) lr((K inter delta_i^(-1))).
  $
  This proves assertion (ii), and the theorem is established.
]
