#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/06-idempotents.typ": *

#heading(level: 2)[
  Idempotents, Indecomposable Modules, and the Krull-Schmidt-Azumaya Theorem.
  Projective Covers and Injective Hulls
] <sec:idempotents-krull-schmidt-projective-covers>

=== Idempotents <ss:idempotents>

Given an arbitrary ring $A$ (with $1$), let
$ A=L_1 plus.o dots plus.o L_n $ <eq:regular-module-ideal-decomposition>
be a direct sum decomposition of $A$ into left ideals ${L_i}$, and set
$ 1=e_1+dots+e_n,e_i in L_i. $
Then for $x in A$, we have
$ x=x e_1+dots+x e_n,"and" x e_i in L_i. $
This shows at once that if $x in L_i$, then $x=x e_i$ and $x e_j=0$ for
$j != i$. Hence we have
$
  L_i=A e_i,e_i^2=e_i,e_i e_j=0 "for" j != i,
  "where" 1 <= i <= n.
$ <eq:orthogonal-idempotent-ideals>
We call ${e_1,dots,e_n}$ a set of _orthogonal idempotents_#idx(
  "orthogonal idempotents",
)#footnote[
  Recall that $e in A$ is _idempotent_ if $e^2=e != 0$.
] of $A$; they are completely determined by the decomposition
@eq:regular-module-ideal-decomposition, although there may be many such
decompositions of $A$. Conversely, it is clear that each set of orthogonal
idempotents ${e_1,dots,e_n}$ such that $sum e_i=1$, gives rise to a direct sum
decomposition $A=op("⨁", limits: #true) A e_i$ into left ideals.

If $e_1=e'+e''$, where $e'$ and $e''$ are orthogonal idempotents, then
$L_1=L_1 e' plus.o L_1 e''$; the sum is direct, since right multiplication by
$e'$ acts as the identity on $L_1 e'$, and annihilates $L_1 e''$. Conversely, if
$L_1=L' plus.o L''$ is a direct sum of left ideals of $A$, then we may write
$e_1=e'+e''$ with $e',e''$ orthogonal idempotents. An idempotent $e in A$ is
called _primitive_#idx("primitive idempotent") if $e$ is not expressible as a
sum of two orthogonal idempotents. We have just shown that $e$ is primitive if
and only if $A e$ is an indecomposable left ideal of $A$. Since the condition of
primitivity is left-right symmetric, it follows that $e$ is primitive if and
only if
#source(142)
$e A$ is an indecomposable right ideal of $A$. Hence if
$ A=op("⨁", limits: #true)_1^n A e_i $
is a decomposition of $A$ into indecomposable left ideals, when the ${e_i}$ are
a set of orthogonal idempotents, then
$ A=op("⨁", limits: #true)_1^n e_i A $
is a decomposition into indecomposable right ideals.

Now let $M$ be a left $A$-module, where $A$ is an arbitrary ring. Let
$ E=End_A M=Hom_A lr((M,M)) $
be the endomorphism ring of $M$. It will be convenient to regard $E$ as a ring
of right operators on $M$, so that $M$ becomes a bimodule
$attach(M, bl: A, br: E)$. We shall imitate the discussion of Morita equivalence
in §@ss:morita-theorems, this time with somewhat different categories, in order
to prove the following result of Dress, which extends earlier work of Fitting:

#proposition[
  Let $attach(M, bl: A, br: E)$ be a bimodule, where $E=End_A M$. Let
  $frak(C)=frak(C)(M)$ be the category of all left $A$-modules which are
  isomorphic to $A$-direct summands of $M^((k))$ for some $k$, with
  $Hom_(frak(C))$ just $Hom_A$. Let $frak(P)$ be the category of all finitely
  generated projective left $E$-modules. Then $frak(P)$ and $frak(C)$ are Morita
  equivalent, that is, there exist covariant functors $F:frak(C) -> frak(P)$ and
  $G:frak(P) -> frak(C)$ such that
  $ G F="id"_(frak(C)),F G="id"_(frak(P)), $
  up to natural isomorphisms. Thus there is a bijection between isomorphism
  classes of objects in $frak(C)$ and such classes in $frak(P)$.

  In particular, there is a one-to-one correspondence between decompositions
  $
    M=op("⨁", limits: #true)_(i=1)^n M_i,
    M_i="nonzero" A"-submodule of" M,
  $
  and decompositions
  $
    E=op("⨁", limits: #true)_(i=1)^n E_i,
    E_i="nonzero left ideal of" E,
  $
  given as follows: starting with the decomposition of $M$, let $pi_i:M -> M_i$
  be the $i$-th projection map. Then $pi_i$ is an idempotent in $E$, and
  #equation-suffix(base: [@prop:morita-summand-equivalence], suffix: "a")[$
    M_i=M pi_i,E_i=E pi_i,M_i=M E_i.
  $] <eq:morita-idempotent-summands>

  #source(143)
  Conversely, given a decomposition of $E$, let ${pi_i}$ be the corresponding
  set of orthogonal idempotents of $E$; then the ${M_i}$ are given by
  @eq:morita-idempotent-summands.
] <prop:morita-summand-equivalence>

#proof(head: emph[Sketch of Proof.])[
  We define functors $F,G$ by
  $
    F=Hom_A lr((attach(M, bl: A, br: E),*)),
    G=(attach(M, bl: A, br: E)) times.o_E *.
  $
  Then (all isomorphisms being natural)
  $
    F(attach(M, bl: A))=Hom_A lr((attach(M, bl: A, br: E),M))
    tilde.equiv E "as left" E"-modules".
  $
  Hence $F(M^((k))) tilde.equiv E^((k))$ for each $k$, whence $F$ maps each
  $A$-direct summand of $M^((k))$ onto an $E$-direct summand of $E^((k))$; this
  proves that $F$ is a functor from $frak(C)$ to $frak(P)$.

  Conversely,
  $
    G(attach(E, bl: E))=(attach(M, bl: A, br: E)) times.o_E (attach(E, bl: E))
    tilde.equiv M "as left" A"-modules",
  $
  so $G(E^((k))) tilde.equiv M^((k))$, and thus $G$ is a functor from $frak(P)$
  to $frak(C)$. Finally,
  $
    G F(attach(M, bl: A)) tilde.equiv G(attach(E, bl: E))
    tilde.equiv attach(M, bl: A),
  $
  whence also $G F(X) tilde.equiv X$ (naturally) for all $X in frak(C)$.
  Likewise
  $
    F G(attach(E, bl: E)) tilde.equiv F(attach(M, bl: A))
    tilde.equiv attach(E, bl: E),
  $
  so also $F G(P) tilde.equiv P$ (naturally) for all $P in frak(P)$. This
  completes the proof that $frak(C)$ is Morita equivalent to $frak(P)$.

  In particular, if $pi:M -> M'$ is the projection of $M$ onto a nonzero
  $A$-direct summand $M'$, then $pi$ is an idempotent in $E$. The object
  $M' in frak(C)$ corresponds to the object
  $ F(M')=Hom_A lr((M,M')) in frak(P). $
  But
  $ Hom_A lr((M,M'))={f in End_A M:f pi=f}=E pi, $
  and further, $M'=M pi=M dot E pi$. The remaining assertions of the proposition
  are now obvious.
]

The preceding result contains the following elementary fact, which can be easily
proved directly:

#corollary[
  A nonzero left $A$-module $M$ is indecomposable if and only if its
  endomorphism ring $End_A M$ has no idempotents except $1$.
] <cor:indecomposable-endomorphism-idempotents>

#source(144)
A direct proof is an immediate consequence of the correspondence between direct
sum decompositions of $M$ and projections in $End_A M$, and will be omitted.

We shall use this result repeatedly in testing for indecomposability, and so we
need some way of testing whether a ring $E$ has a nontrivial idempotent.
Certainly, if $E$ is a local ring, its only idempotent is $1$; for suppose that
$e in E$ is idempotent, $e != 1$. Since $e(1-e)=0$, both $e$ and $1-e$ are
non-units; but then so is their sum, since $E$ is local, which gives a
contradiction. _Under suitable hypotheses_, the converse also holds: if $E$ has
no idempotent except $1$, then $E$ is local. In order to prove this, we shall
investigate the important question of “lifting idempotents”: if $overline(E)$ is
a factor ring of $E$, is every idempotent in $overline(E)$ the image of some
idempotent in $E$?

Changing notation, let $A$ be an arbitrary ring and let $N$ be a two-sided ideal
of $A$ such that $N subset.eq rad A$. Set $overline(A)=A slash N$, and let
$e in A$. We claim that if $e in A$ is idempotent, then so is $overline(e)$;
since $e^2=e$ it is clear that $overline(e)^2=overline(e)$. Further, if
$overline(e)=0$, then $e in N subset.eq rad A$; hence $1-e in u(A)$, so from
$e(1-e)=0$ it follows that $e=0$, a contradiction. This shows that each
decomposition $1=sum e_i$ into orthogonal idempotents in $A$ yields a
decomposition $overline(1)=sum overline(e)_i$ of the same kind in $overline(A)$.
We intend to show that under suitable hypotheses, $overline(e)_i$ is primitive
whenever $e_i$ is primitive, and that each decomposition of $overline(1)$
“lifts” to a decomposition of $1$.

To begin with, we may give $A$ the _$N$-adic topology_#idx("N-adic topology"),
in which a basis for the open neighborhoods of an element $a in A$ is given by
the sets ${a+N^k:k=0,1,2,dots}$. Call $A$ _complete_#idx(
  "complete (in N-adic topology)",
) in the $N$-adic topology if each Cauchy sequence from $A$ (relative to the
$N$-adic topology) converges to a unique element of $A$. There are two important
cases in which $A$ is necessarily complete in the $N$-adic topology:

#proposition[
  Let $N$ be a two-sided ideal of $A$ contained in $rad A$. Then $A$ is complete
  in the $N$-adic topology if either
  #enum(numbering: "(i)", [$A$ is left artinian, or], [$A$ is an $R$-algebra
    which is finitely generated as $R$-module, where $R$ is a complete
    commutative noetherian local ring.])
] <prop:radical-adic-completeness>

#proof[
  In case (i), $N$ is nilpotent by @prop:artinian-radical-nilpotent, so any
  Cauchy sequence (relative to the $N$-adic topology of $A$) must be constant
  from some point on. In case (ii), let $P=rad R$. By
  @prop:finite-algebra-local-base-radical (iv), $N^k subset.eq P A$ for some
  $k$. Hence any Cauchy sequence relative to the $N$-adic topology is also a
  Cauchy sequence in $A$ relative to the $P$-adic topology. But $A$ is complete
  in the $P$-adic topology, by the discussion at the end of §@ss:local-rings. By
  the Krull intersection theorem, each $N^j$ is closed in the $P$-adic topology,
  since $A/N^j$ is a finite $R$-module. This finishes the proof.
]

#remark(numbered: false)[
  The hypotheses of the previous proposition hold whenever $A$ is a f.d. algebra
  over a field, and also whenever $A$ is an $R$-algebra f.g. as
  #source(145)
  $R$-module, where $R$ is a complete discrete valuation ring. These are the two
  situations which will arise most frequently.
]

#proposition[
  Let $N$ be a two-sided ideal in $A$ such that $N subset.eq rad A$. Let $Q$ and
  $Q'$ be f.g. projective left $A$-modules. Then $Q tilde.equiv Q'$ if and only
  if $Q slash N Q tilde.equiv
  Q' slash N Q'$ as $overline(A)$-modules (where $overline(A)=A slash N$).
] <prop:projective-isomorphism-modulo-radical>

#proof(head: [#emph[Proof]#[(Bass).]])[
  One way is clear. Conversely, suppose that
  $Q slash N Q tilde.equiv Q' slash N Q' tilde.equiv X$. Since $Q$ is
  projective, there exists a homomorphism $f:Q -> Q'$ making the diagram
  #projective-quotient-isomorphism-diagram
  commute, where $i$ and $j$ are homomorphisms with kernels $N Q'$ and $N Q$,
  respectively. Let $T=Q' slash f(Q)$, the cokernel of $f$. Then $T$ is finitely
  generated, and it is easily checked from the diagram that $T=N T$. By
  Nakayama's Lemma~@lem:nakayama, we have $T=0$, so $f$ is surjective. Since
  $Q'$ is projective, $ker f$ is a direct summand of $Q$, and is finitely
  generated. Again from the diagram it follows that $ker f=N dot ker f$, and
  hence $ker f=0$ by a second application of Nakayama's Lemma.
]

In particular, left ideals $A e$ generated by idempotents $e$ are f.g.
projective modules to which @prop:projective-isomorphism-modulo-radical applies,
and we shall shortly make use of this fact.

#theorem(name: "Theorem on Lifting Idempotents")[
  Let $N$ be a two-sided ideal of $A$, and set $overline(A)=A slash N$. Suppose
  that $N subset.eq rad A$, and that $A$ is complete in the $N$-adic topology.
  Then the following statements hold.
  #enum(
    numbering: "(i)",
    [For every idempotent $epsilon in overline(A)$ there exists an idempotent
      $e in A$ such that $overline(e)=epsilon$.],
    [$A e_1 tilde.equiv A e_2$ as left $A$-modules if and only if
      $overline(A)overline(e)_1 tilde.equiv
      overline(A)overline(e)_2$, for arbitrary idempotents $e_1,e_2 in A$.],
    [An idempotent $e in A$ is primitive if and only if $overline(e)$ is
      primitive in $overline(A)$.],
  )
] <th:lifting-idempotents>#idx(
  "lifting idempotents",
  target: [@th:lifting-idempotents],
)

#proof[
  (i) We start from the identity in $ZZ[X]$
  $
    1=(X+(1-X))^(2 n)=sum_(j=0)^(2 n) binom(2 n, j)
    X^(2 n-j)(1-X)^j,n=1,2,dots.
  $
  #source(146)
  Let
  $ f_n lr((X))=sum_(j=0)^n binom(2 n, j)X^(2 n-j)(1-X)^j. $
  Then the polynomials $f_n lr((X))$ have the following properties:
  #enum(
    numbering: "(a)",
    [$f_n lr((X)) in ZZ[X]$;],
    [$f_n lr((X)) equiv 0 (mod X^n)$ and
      $f_n lr((X)) equiv 1 (mod (X-1)^n)$],
    [${f_n lr((X))}^2 equiv f_n lr((X)) (mod X^n (1-X)^n)$],
    [$f_n lr((X)) equiv f_(n-1) lr((X))
    (mod X^(n-1)(X-1)^(n-1))$],
    [$f_1 lr((X)) equiv X (mod (X-X^2))$.],
  )
  The proofs of (a)–(e) are immediate and will be omitted. Now let $epsilon$ be
  an idempotent in $overline(A)$, and find $a in A$ such that
  $overline(a)=epsilon$. Then $overline(a)^2-overline(a)=0$, $a^2-a in N$, and
  it follows from (d) that $f_j lr((a)) equiv f_(j-1) lr((a)) (mod N^(j-1))$.
  Because $A$ is complete in the $N$-adic topology,
  $lim_(j -> infinity) f_j lr((a))=e$ exists in $A$. From (c) we have $e^2=e$,
  and from (e), $e equiv a (mod N)$ so that $overline(e)=overline(a)=epsilon$,
  completing the proof of (i).

  (ii) Follows from @prop:projective-isomorphism-modulo-radical.

  (iii) Let $e$ be an idempotent in $A$, and suppose that $overline(e)$ is not
  primitive, so that
  $ overline(e)=epsilon_1+epsilon_2 $
  where $epsilon_1$ and $epsilon_2$ are orthogonal idempotents in $overline(A)$.
  Choose $a in A$ such that $overline(a)=epsilon_1$, and set $b=e a e$. Then
  $overline(b)=overline(e)overline(a)overline(e)=epsilon_1$, and $b e=e b=b$. As
  in the proof of (i), $lim_(j -> infinity) f_j lr((b))=e_1$ exists in $A$, and
  it follows that
  $ overline(e)_1=overline(b)=epsilon_1,"and" e_1 e=e e_1=e_1. $
  Letting $e_2=e-e_1$, we have $e_2^2=e_2 != 0$, and $e_1 e_2=e_2 e_1=0$,
  proving that $e$ is not primitive in $A$. The converse is clear, and (iii) is
  proved.
]

#remark(numbered: false)[
  The preceding argument was used in @bib:CurtisReiner1962[CR Chapter~XI], in a
  less general situation. Other proofs of these results may be found in
  @bib:Reiner1975[MO §~6].
]

#theorem[
  Let $overline(A)=A slash N$, where $N$ is a two-sided ideal of $A$ contained
  in $rad A$. Assume that either
  #enum(numbering: "(i)", [$A$ is left artinian, or], [$A$ is an $R$-algebra,
    finitely generated as $R$-module, where $R$ is a commutative complete local
    noetherian ring.])
  #source(147)
  Then $A$ is complete in the $N$-adic topology, and each decomposition
  $ A=A e_1 plus.o dots plus.o A e_n $
  into indecomposable left ideals ${A e_i}$ of $A$, yields a decomposition
  $
    overline(A)=overline(A)overline(e)_1 plus.o dots plus.o
    overline(A)overline(e)_n
  $
  into indecomposable left ideals ${overline(A)overline(e)_i}$ of $overline(A)$.
  Conversely, each such decomposition of $overline(A)$ comes from a
  decomposition of $A$.

  Furthermore, for $1 <= i,j <= n$, we have
  $
    A e_i tilde.equiv A e_j <=>
    overline(A)overline(e)_i tilde.equiv overline(A)overline(e)_j.
  $
] <th:complete-ring-idempotent-decompositions>

#proof(head: emph[Sketch of Proof.])[
  From Proposition~@prop:radical-adic-completeness, it follows in both cases
  that $A$ is complete in the $N$-adic topology. The proof is then immediate
  from the preceding two results.
]

#corollary[
  Let $N=rad A$, and keep the above notation and hypotheses. Then for each $i$,
  $1 <= i <= n$, the quotient $A e_i slash N e_i$ is a simple left $A$-module,
  and $N e_i$ is the unique maximal $A$-submodule of $A e_i$.
] <cor:indecomposable-projective-top>

#proof[
  By @prop:artinian-semisimple-radical-quotient and
  @prop:finite-algebra-local-base-radical the ring $overline(A)$ is semisimple,
  and so indecomposable $overline(A)$-modules must be simple. Thus
  $overline(A)overline(e)_i$ is a simple $overline(A)$-module, and hence also a
  simple left $A$-module. Since $overline(A)overline(e)_i=A e_i slash N e_i$, it
  follows that $N e_i$ is a maximal submodule of $A e_i$.

  If $X$ is another maximal submodule of $A e_i$, then $X+N e_i=A e_i$.
  Therefore
  $ X+(rad A)A e_i=A e_i, $
  whence $X=A e_i$, by Nakayama's Lemma. This is a contradiction, and shows that
  no such $X$ exists. This completes the proof.
]

The next result plays a crucial role in our future considerations, and explains
to some extent the importance of the Theorem on Lifting
Idempotents~@th:lifting-idempotents. We prove:

#proposition[
  Let $M$ be a nonzero left $A$-module, and let $E=End_A M$ be its endomorphism
  ring. Suppose that either
  #enum(
    numbering: "(i)",
    [The $A$-submodules of $M$ satisfy both chain conditions, or],
    [$M$ is a f.g. $A$-module, where $A$ is an $R$-algebra as in
      @th:complete-ring-idempotent-decompositions (ii).],
  )
  Then $M$ is an indecomposable $A$-module if and only if $E$ is a local ring.
] <prop:indecomposable-local-endomorphism-ring>

#source(148)
#proof[
  We have already seen in @cor:indecomposable-endomorphism-idempotents that $M$
  is indecomposable if and only if $E$ has no idempotents except $1$. The
  remarks following @cor:indecomposable-endomorphism-idempotents show that a
  local ring has no idempotents except $1$, and thus if $E$ is local, then $M$
  is indecomposable. We must prove that, conversely, if $M$ is indecomposable
  then $E$ is local.

  _Case (i)._ Assume $M$ indecomposable and satisfying both chain conditions. To
  prove that $E$ is local, it suffices (by @prop:local-ring-criteria) to show
  that the sum of two non-units in $E$ is a non-unit. For this, we need only
  show that there cannot exist non-units $alpha,beta in E$ for which
  $alpha+beta=1$. If such elements exist, then $beta$ is not nilpotent, since
  otherwise $1-beta$ has inverse $1+beta+beta^2+dots$. Hence the descending
  chain of $A$-submodules of $M$:
  $ M supset.eq M beta supset.eq M beta^2 supset.eq dots $
  must terminate in a nonzero module, say at $M beta^t$. Put
  $gamma=beta^t in E$, so $gamma$ is a surjection of $M beta^t$ onto itself.
  Since $M beta^t$ is a noetherian module, by
  @prop:surjective-noetherian-endomorphism $gamma$ must be an automorphism. If
  $i:M beta^t -> M$ is the inclusion map, we have
  #stable-image-splitting-diagram
  with composite $(i gamma^(-1)) dot gamma$ the identity on $M beta^t$. Hence
  $M beta^t$ is a direct summand of $M$, and therefore $M beta^t=M$ because $M$
  is indecomposable. But then $beta^t$ is an automorphism of $M$, whence $beta$
  is a unit of $E$. This is a contradiction, and completes the proof that $E$ is
  local in case (i).

  _Case (ii)._ Assume $M$ indecomposable, and that the hypotheses (ii) are
  satisfied. Since $E subset.eq End_R M$, which is a finitely generated
  $R$-module by Exercise~@exc:hom-finitely-generated-over-base, it follows that
  $E$ is also a finitely generated $R$-module. Hence by
  @prop:finite-algebra-local-base-radical, $E slash rad E$ is semisimple, and
  idempotents can be lifted from $E slash rad E$ to $E$ by
  @th:lifting-idempotents. If $E slash rad E$ is _not_ a skewfield, then it has
  at least one proper nonzero left ideal, and this ideal is a direct summand of
  the semisimple ring $E slash rad E$. It follows from the discussion at the
  beginning of this section that $E slash rad E$ contains an idempotent
  $overline(e) != overline(1)$. But then by @th:lifting-idempotents there exists
  an idempotent $e in E$ lifting $overline(e)$, and so $e != 1$. But $E$ cannot
  contain any idempotents except $1$, since $M$ is indecomposable. Thus we have
  shown that $E slash rad E$ _must_ be a skewfield. Therefore $E$ is local by
  @prop:local-ring-criteria, and the proposition is proved.
]

A ring $A$ is called _primary_#idx("primary ring") if $A slash rad A$ is a
simple artinian ring. Under suitable hypotheses, every primary ring is a full
matrix ring over a local ring. In fact, we prove now

#proposition[
  If $B$ is a local ring, then for each positive integer $n$, the ring
  $M_n lr((B))$ is primary. Conversely, let $A$ be a primary ring, and assume
  that $A$ is
  #source(149)
  either left artinian or an $R$-algebra as in
  @th:complete-ring-idempotent-decompositions. Then $A tilde.equiv M_n lr((B))$
  for some local ring $B$ and some integer $n$.
] <prop:primary-ring-matrix-local-ring>

#proof[
  Suppose $B$ is a local ring, so $B slash rad B=S$ (say) is a skewfield by
  @prop:local-ring-criteria. From @prop:radical-matrix-ring we know that
  $ rad M_n lr((B))=M_n lr((rad B)). $
  Therefore
  $
    M_n lr((B)) slash rad M_n lr((B)) tilde.equiv
    M_n lr((B slash rad B))=M_n lr((S)).
  $
  But $M_n lr((S))$ is a simple artinian ring by §@ss:morita-theorems, which
  proves that $M_n lr((B))$ is primary.

  Conversely, let $A$ be a primary ring satisfying the given hypotheses, and let
  $N=rad A$. Keep the notation and terminology of
  @th:complete-ring-idempotent-decompositions, so
  $overline(A)=A slash N=op("⨁", limits: #true)
  overline(A)overline(e)_i$. Since $overline(A)$ is a simple artinian ring
  (because $A$ is primary), it follows that the ${overline(A)overline(e)_i}$ are
  mutually isomorphic simple left $overline(A)$-modules. Hence by
  @th:complete-ring-idempotent-decompositions, the ${A e_i}$ are mutually
  isomorphic indecomposable $A$-modules, and thus
  $ A tilde.equiv (A e_1)^((n)) "as left" A"-modules". $
  Therefore#footnote[
    $A^circle.small$ denotes the opposite ring of $A$, having the same elements
    as $A$, but with multiplication reversed.
  ]
  $
    A^circle.small=End_A lr((attach(A, bl: A))) tilde.equiv
    End_A lr(((A e_1)^((n))))=M_n lr((B)),
  $
  where $B=End_A lr((A e_1))$. Since $A e_1$ is indecomposable, $B$ is a local
  ring by @prop:indecomposable-local-endomorphism-ring. Therefore we obtain
  $A tilde.equiv M_n lr((B^circle.small))$. However, if $S$ is a skewfield then
  so is $S^circle.small$. Furthermore, under the anti-isomorphism
  $B -> B^circle.small$, we have $rad B -> rad B^circle.small$ by
  @cor:radical-left-right-symmetry. Thus $B^circle.small$ is local, since
  $
    B^circle.small slash rad B^circle.small tilde.equiv
    (B slash rad B)^circle.small=S^circle.small,
  $
  where $S$ is the skewfield $B slash rad B$. This completes the proof.
]

=== The Krull-Schmidt-Azumaya Theorem <ss:krull-schmidt-azumaya>

Let $A$ be a ring, $M$ a left $A$-module, and $E=End_A M$ its endomorphism ring.
Call $M$ _indecomposable_#idx("indecomposable") if $M != 0$ and $M$ is not
expressible as a direct sum of nonzero $A$-submodules. We saw in
@prop:indecomposable-local-endomorphism-ring that under suitable hypotheses, $M$
is indecomposable if and only if $E$ is a local ring. This is the key fact in
proving the following fundamental result, hereafter abbreviated as the K-S-A
Theorem:

#source(150)
#theorem(name: "Krull-Schmidt-Azumaya Theorem")[
  Let $M$ be a finitely generated left $A$-module, and assume that either:
  #enum(
    numbering: "(i)",
    [The $A$-submodules of $M$ satisfy both chain conditions, or],
    [$A$ is an $R$-algebra, f.g. as $R$-module, where $R$ is a complete
      commutative noetherian local ring (such as, for example, a field or a
      complete discrete valuation ring).],
  )
  Then $M$ is expressible as a finite direct sum of indecomposable submodules.
  Further, if
  $
    M=op("⨁", limits: #true)_(i=1)^r M_i
    =op("⨁", limits: #true)_(j=1)^s N_j
  $ <eq:krull-schmidt-decompositions>
  are two such sums, then $r=s$ and $M_1 tilde.equiv N_(j_1),dots,
  M_r tilde.equiv N_(j_r)$, where ${j_1,dots,j_r}$ is some permutation of
  ${1,dots,r}$. In brief, $M$ is uniquely a finite sum of indecomposables, up to
  isomorphism and order of occurrence of the summands.
] <th:krull-schmidt-azumaya>#idx(
  "Krull-Schmidt-Azumaya Theorem",
  target: [@th:krull-schmidt-azumaya],
)

#proof[
  In both cases (i) and (ii), $M$ is a noetherian module, hence is expressible
  as a finite direct sum of indecomposable submodules. We now prove the
  uniqueness assertion by induction on the integer $r$ in
  @eq:krull-schmidt-decompositions, observing first that the result is obvious
  when $r=1$. Now let $r >= 2$, and let $mu_i:M -> M_i$, and $nu_j:M -> N_j$ be
  the projection maps associated with the decompositions
  @eq:krull-schmidt-decompositions. Then $sum nu_j="id"_M$, whence
  $ sum mu_1 nu_j="identity map on" M_1, $
  and where each map $mu_1 nu_j$ is restricted to $M_1$. However, by
  @prop:indecomposable-local-endomorphism-ring the endomorphism ring $End_A M_1$
  is local, that is, the sum of non-units in this ring is a non-unit. The above
  equation thus implies that some $mu_1 nu_j$ is an automorphism of $M_1$.
  Renumbering the $N_j$'s if need be, we may assume that
  $mu_1 nu_1=phi in Aut_A M_1$. But then in the diagram
  #krull-schmidt-splitting-diagram
  we have $(phi^(-1)mu_1)nu_1="id"_(M_1)$, whence $nu_1 M_1$ is a direct summand
  of $N_1$. Since both $M_1,N_1$ are indecomposable, it follows that $nu_1$ is
  an isomorphism $M_1 tilde.equiv N_1$, and that $phi^(-1)mu_1:N_1 -> M_1$ is
  its inverse.
  $ M'=N_1 plus.o M_2 plus.o dots plus.o M_r. $
  (Note that the sum is direct, since if
  $ n_1+m_2+dots+m_r=0,n_1 in N_1,m_j in M_j, $
  #source(151)
  then applying $mu_1$ we see that $mu_1 lr((n_1))=0$, whence $n_1=0$. But then
  each $m_j=0$, $j=2,dots,r$.) Next, for $x in N_1$ we have
  $ mu_1 lr((x))=x-mu_2 lr((x))-dots-mu_r lr((x)) in M', $
  and so $M_1=mu_1 lr((N_1)) subset M'$. Therefore $M'=M$, so we have
  $
    M=M_1 plus.o M_2 plus.o dots plus.o M_r
    =N_1 plus.o M_2 plus.o dots plus.o M_r.
  $
  Now set $rho=nu_1 mu_1+mu_2+dots+mu_r$; clearly $rho$ defines an
  $A$-automorphism of $M$ which carries $M_1$ onto $N_1$, and each $M_j$ onto
  itself for $j=2,dots,r$. Hence $rho$ induces an $A$-automorphism
  $M slash M_1 tilde.equiv M slash N_1$; but
  $M slash N_1=op("⨁", limits: #true)_(j=2)^s N_j$, so we have
  $op("⨁", limits: #true)_2^r M_i tilde.equiv
  op("⨁", limits: #true)_2^s N_j$. Now use the induction hypothesis to conclude
  that the ${M_i:2 <= i <= r}$ are, up to isomorphism, a rearrangement of the
  ${N_j:2 <= j <= s}$. This completes the proof.
]

#remark(numbered: true)[
  Examination of the preceding proof shows that the uniqueness part of
  Theorem~@th:krull-schmidt-azumaya holds for all direct decompositions as in
  @eq:krull-schmidt-decompositions for which the endomorphism rings of the
  indecomposable summands are local rings (without any hypothesis on the ring
  $A$.)
] <rem:krull-schmidt-local-endomorphisms>

#corollary[
  Let $L,M,N$ be left $A$-modules satisfying the conditions of
  @th:krull-schmidt-azumaya, and suppose that
  $ L plus.o M tilde.equiv L plus.o N. $
  Then $M tilde.equiv N$.
] <cor:krull-schmidt-cancellation>

#proof[
  Write $L=op("⨁", limits: #true) L_i$, $M=op("⨁", limits: #true) M_j$,
  $N=op("⨁", limits: #true) N_k$, direct sums of indecomposables. Then the
  hypothesis implies, by virtue of the K-S-A Theorem, that the ${M_j}$ coincide
  with the ${N_k}$, up to isomorphism and order of occurrence. Hence
  $M tilde.equiv N$ as claimed.
]

#corollary[
  Let $L$ be a direct summand of the $A$-module $M$ given as in
  @th:krull-schmidt-azumaya. Then $L$ is isomorphic to a subsum of
  $op("⨁", limits: #true) M_i$.
] <cor:krull-schmidt-summands>

#proof[
  We may write $M=L plus.o L'$ for some submodule $L'$ of $M$. Now let
  $L=op("⨁", limits: #true) L_k$, $L'=op("⨁", limits: #true) L'_j$ be
  decompositions into indecomposables. By @th:krull-schmidt-azumaya, the modules
  ${L_k} union {L'_j}$ coincide with the ${M_i}$, up to isomorphism. Hence
  $
    L=op("⨁", limits: #true) L_k tilde.equiv
    M_(i_1) plus.o dots plus.o M_(i_t),
  $
  for some subset ${i_1,dots,i_t}$ of ${1,dots,r}$.
]

We remark that K-S-A Theorem need not hold for algebras over a local ring $R$
which is not complete. (See §@sec:krull-schmidt-discrete-valuations.)
#source(152)

The K-S-A Theorem has many important consequences. Let us give one immediately.
For a ring $A$, we have denoted by $frak(P)(A)$ the category of all finitely
generated projective left $A$-modules. We now prove

#proposition[
  Let $A$ be a ring which is either left artinian, or else is an $R$-algebra
  over a complete local ring $R$ as in
  @th:complete-ring-idempotent-decompositions (ii). Let $N$ be any two-sided
  ideal of $A$ contained in $rad A$, and set $overline(A)=A slash N$. For each
  $A$-module $X$, let $overline(X)=X slash N X$ be the corresponding
  $overline(A)$-module. Let
  $ A=A e_1 plus.o dots plus.o A e_n $
  be a decomposition of $A$ into indecomposable left ideals, numbered so that
  $A e_1,dots,A e_m$ are a full set of non-isomorphic modules among the
  ${A e_i}$. Then
  #enum(
    numbering: "(i)",
    [For each $P in frak(P)(A)$, there exist non-negative integers ${r_i}$ such
      that
      $ P tilde.equiv product_(i=1)^m (A e_i)^((r_i)). $
      <eq:projective-indecomposable-multiplicities>],
    [If ${r_i}$ and ${s_i}$ are non-negative integers, then
      $
        product_(i=1)^m (A e_i)^((r_i)) tilde.equiv
        product_(i=1)^m (A e_i)^((s_i))
        "if and only if" r_i=s_i "for each" i.
      $],
    [For each $Y in frak(P)(overline(A))$, there exist non-negative integers
      ${r_i}$ such that
      $
        Y tilde.equiv product_(i=1)^m
        (overline(A)overline(e)_i)^((r_i)),
      $
      <eq:quotient-projective-indecomposable-multiplicities>
      and the ${r_i}$ are uniquely determined by the isomorphism class of $Y$.],
    [The isomorphism classes in $frak(P)(A)$ correspond bijectively with those
      in $frak(P)(overline(A))$, the correspondence being given by mapping the
      class of $P in frak(P)(A)$ onto the class of
      $overline(P) in frak(P)(overline(A))$.],
  )
] <prop:projective-isomorphism-classes-quotient>

#proof[
  The hypotheses on $A$ imply that the K-S-A Theorem, and its corollaries, hold
  for $A$-modules and also for $overline(A)$-modules. Each $P in frak(P)(A)$ is
  isomorphic to a direct summand of $A^((k))$ for some $k$. But
  $
    A^((k)) tilde.equiv product_(i=1)^n (A e_i)^((k))
    tilde.equiv product_(i=1)^m (A e_i)^((k_i)),
  $
  for some positive integers ${k_i}$. It follows at once from
  @cor:krull-schmidt-summands that @eq:projective-indecomposable-multiplicities
  holds for some integers ${r_i}$ with $0 <= r_i <= k_i$ for each $i$. This
  proves the first assertion in the proposition. Assertion (ii) is a direct
  consequence of the K-S-A Theorem.

  #source(153)
  Next, it follows from @th:complete-ring-idempotent-decompositions that the
  formula $overline(A)=op("⨁", limits: #true)_(i=1)^n
  overline(A)overline(e)_i$ gives a decomposition of $overline(A)$ into
  indecomposable left ideals, and furthermore that
  $overline(A)overline(e)_1,dots,overline(A)overline(e)_m$ are a full set of
  non-isomorphic modules among the ${overline(A)overline(e)_i}$. We conclude,
  just as above, that every $Y in frak(P)(overline(A))$ is isomorphic to a
  direct sum of copies of the ${overline(A)overline(e)_i:1 <= i <= m}$, and that
  the number of summands of each type is uniquely determined by the isomorphism
  class of $Y$.

  It is now clear that the bijection, whose existence is asserted in (iv), is
  given by the correspondence
  $
    product_(i=1)^m (A e_i)^((r_i)) <->
    product_(i=1)^m (overline(A)overline(e)_i)^((r_i)),
  $
  where the ${r_i}$ are non-negative integers.
]

=== Projective Covers <ss:projective-covers>

Let $A$ be a ring, and let $M,N$ be left $A$-modules. A map
$f in Hom_A lr((M,N))$ is called _essential_#idx("essential surjection") if $f$
is surjective, and if for each sequence of $A$-modules
$X arrow.r^g M arrow.r^f N$ such that $f g$ is surjective, the map $g$ is also
surjective. In other words, a surjection $f:M -> N$ is essential if no proper
submodule of $M$ is mapped onto $N$ by $f$.

A _projective cover_#idx("projective cover") of a module $M$ is a diagram
$P arrow.r^f M$ with $P$ projective and $f$ essential.

#proposition[
  Projective covers are unique up to isomorphism, assuming there are any. In
  other words, given two projective covers $P arrow.r^f M$ and
  $P' arrow.r^(f') M$, there exists an isomorphism $theta:P tilde.equiv P'$ such
  that $f=f'theta$.
] <prop:projective-cover-uniqueness>

#proof[
  Consider the diagram
  #projective-cover-uniqueness-diagram
  There exists a homomorphism $theta$ with $f=f'theta$, since $P$ is projective
  and $f'$ is a surjection. Then $theta$ is surjective, since $f'theta$ is
  surjective and $f'$ is essential. Since $P'$ is projective, there is a
  splitting map $phi:P' -> P$ such that $theta phi="id"_(P')$. Then
  $f phi=f'theta phi=f'$, whence $phi$ is surjective since $f phi$ is surjective
  and $f$ is essential. Hence both $phi$ and $theta$ are isomorphisms.
]

Some modules need not have projective covers. For example, the $ZZ$-module
$ZZ slash (2 ZZ)$ has none; for let $f:P -> ZZ slash (2 ZZ)$ be a projective
cover, with $P$ $ZZ$-projective. Then $P$ is $ZZ$-free, and $3 P$ is a proper
submodule of $P$ for which $f(3 P)=ZZ slash (2 ZZ)$.

#source(154)
The next result shows how projective covers may be determined in some cases. We
begin with:

#lemma[
  Let $f:X -> M$ be a surjection of f.g. $A$-modules. If
  $ ker f subset.eq (rad A)X, $
  then $f$ is essential.
] <lem:radical-kernel-essential-surjection>

#proof[
  Let $Y subset.eq X$ be a submodule such that $f(Y)=M$. Then
  $ X=Y+ker f=Y+(rad A)X. $
  Thus $X=Y$ by Nakayama's Lemma, which proves that $f$ is essential.
]

#corollary[
  Let $P$ be a f.g. projective $A$-module, and let $J$ be any two-sided ideal of
  $A$ contained in $rad A$. Then the natural map $P -> P slash J P$ gives a
  projective cover of the $A$-module $P slash J P$.
] <cor:projective-cover-radical-quotient>

#proof[
  The surjection $P -> P slash J P$ is essential, by
  @lem:radical-kernel-essential-surjection.
]

We shall call the ring $A$ _semiperfect_#idx("semiperfect ring") if
$A slash rad A$ is a semisimple artinian ring and every idempotent in
$A slash rad A$ is the image of an idempotent in $A$. It follows from
@prop:artinian-semisimple-radical-quotient, @prop:radical-adic-completeness and
@th:lifting-idempotents that left artinian rings are always semiperfect; by
@prop:finite-algebra-local-base-radical, @prop:radical-adic-completeness and
@th:lifting-idempotents, so are $R$-algebras of the type described in
@prop:radical-adic-completeness (ii). If we set $N=rad A$ in
@th:complete-ring-idempotent-decompositions, then the proof of
@th:complete-ring-idempotent-decompositions carries over equally well to the
case where $A$ is any semiperfect ring. In particular, let
$overline(A)=A slash rad A$. Keeping the notation of
@th:complete-ring-idempotent-decompositions, the decomposition
$overline(A)=op("⨁", limits: #true) overline(A)overline(e)_i$ gives a
decomposition of $overline(A)$ into simple left $overline(A)$-modules, and thus
every simple left $overline(A)$-module is (up to isomorphism) of the form
$overline(A)overline(e)_i$. Using this, we prove:

#theorem[
  Let $A$ be a semiperfect ring, and set $N=rad A$, $overline(A)=A slash N$.
  Then every f.g. left $A$-module $X$ has a projective cover. Specifically,
  there exists a f.g. projective $A$-module $P$ such that
  $P slash N P tilde.equiv X slash N X$ as $overline(A)$-modules, and this
  isomorphism lifts to a surjection $P -> X$ giving a projective cover of $X$.
] <th:semiperfect-projective-covers>

#proof[
  Set $overline(X)=X slash N X$, a f.g. $overline(A)$-module. Since
  $overline(A)$ is semisimple, it follows from the discussion that $overline(X)$
  is (up to $overline(A)$-isomorphism) a direct sum of copies of the
  $overline(A)$-modules ${overline(A)overline(e)_i}$. For each $i$, $A e_i$ is a
  projective $A$-module such that
  $A e_i slash N(A e_i)=overline(A)overline(e)_i$. Hence there exists a f.g.
  projective $A$-module $P$ such that#footnote[
    This same type of argument also occurred in the proof of
    @prop:projective-isomorphism-classes-quotient.
  ]
  $
    P slash N P tilde.equiv X slash N X "as"
    overline(A)"-modules".
  $
  This isomorphism is also an $A$-isomorphism, of course.

  #source(155)
  Now consider the diagram
  #numbered-block(projective-cover-lifting-diagram)
  <eq:projective-cover-lifting>
  where $h$ is the isomorphism given above. Since $P$ is projective, there
  exists an $A$-homomorphism $f:P -> X$ making the diagram commute. For each
  $x in X$, there exists an element $p in P$ for which
  $overline(x)=h(overline(p))$ in $overline(X)$. This shows that
  $ f(P)+N X=X, $
  whence $f(P)=X$ by Nakayama's Lemma. Furthermore, it is easily seen that
  $ker f subset.eq N P$, since $h$ is injective. Thus we have obtained a
  surjection $f:P -> X$ for which $ker f subset.eq N P$, and so $f$ gives a
  projective cover of $X$ by @lem:radical-kernel-essential-surjection.
]

#corollary[
  Let $A$ be a semiperfect ring, and consider only finitely generated
  $A$-modules. Let $N=rad A$.
  #enum(
    numbering: "(i)",
    [Let $f:P -> X$ be a surjection, with $P$ projective. Then $f$ gives a
      projective cover of $X$ if and only if $ker f subset.eq N dot P$.],
    [For each $A$-module $X$, the modules $X$ and $X slash N X$ have the same
      projective cover as $A$-modules.],
    [Projective covers are additive, that is, if $f_i:P_i -> X_i$,
      $1 <= i <= k$, are projective covers, then so is
      $ product_1^k f_i:product_1^k P_i -> product_1^k X_i. $],
  )
] <cor:semiperfect-projective-cover-properties>

#proof[
  (i) Given a surjection $f:P -> X$ with $ker f subset.eq N dot P$, we have
  already remarked in @lem:radical-kernel-essential-surjection that $f$ gives a
  projective cover of $X$. Conversely, starting with a projective cover
  $f:P -> X$, we know by @prop:projective-cover-uniqueness that $P$ is unique up
  to isomorphism. Hence by the proof of @th:semiperfect-projective-covers, there
  is a commutative diagram @eq:projective-cover-lifting, with $h$ an
  isomorphism. This implies at once that $ker f subset.eq N dot P$, as claimed.

  (ii) Let $Y=X slash N X$, viewed as $A$-module. Then
  $X slash N X tilde.equiv Y slash N Y$, so by
  @th:semiperfect-projective-covers, $X$ and $Y$ have the same projective cover.

  (iii) This is obvious from the fact that
  $
    (product P_i) slash N dot (product P_i)
    tilde.equiv product (P_i slash N P_i)
    tilde.equiv product (X_i slash N X_i).
  $
]

#source(156)
#remarks(numbered: true)[
  #enum(
    numbering: "(i)",
    [The converse of Theorem~@th:semiperfect-projective-covers also holds: if
      every f.g. left $A$-module has a projective cover, then the ring $A$ is
      semiperfect. See @bib:Anderson1973[Anderson–Fuller (1973), Th.~27.6,
        p.~304] for a proof of this result. Other interesting results on
      semiperfect rings are given in this reference (see
      @bib:Anderson1973[§~27]), as well as a discussion of perfect rings (see
      @bib:Anderson1973[§~28]).],
    [The results of Theorem~@th:complete-ring-idempotent-decompositions can be
      interpreted naturally in terms of projective covers. It follows at once
      from @cor:projective-cover-radical-quotient that the natural map
      $A e_i -> overline(A)overline(e)_i$ gives a projective cover of the
      $A$-module $overline(A)overline(e)_i$. By the uniqueness of projective
      covers (@prop:projective-cover-uniqueness), we conclude immediately that
      $
        A e_i tilde.equiv A e_j "if and only if"
        overline(A)overline(e)_i tilde.equiv
        overline(A)overline(e)_j,
      $
      using the notation of @th:complete-ring-idempotent-decompositions. (Of
      course we are using the fact that two $overline(A)$-modules are
      $overline(A)$-isomorphic if and only if they are $A$-isomorphic when
      viewed as $A$-modules.)],
    [Gruenberg–Roggenkamp~@bib:Gruenberg1975 discuss the question as to whether
      augmentation ideals of group rings have projective covers. Let $G$ be a
      finite group, and let
      $ ZZ'={a/b:a,b in ZZ,(b,abs(G))=1}. $
      The _augmentation ideal_#idx("augmentation ideal") $I'$ of $ZZ' G$ is by
      definition $op("⨁", limits: #true) ZZ'(x-1)$, with $x$ ranging over all
      elements of $G-{1}$. They show that $I'$ has a projective $ZZ' G$-cover if
      and only if $G$ is a $p$-group (for some prime $p$) or else $G$ is cyclic.
      They also deal with this problem for the more general case in which $ZZ'$
      is replaced by some semilocal ring of integers in an algebraic number
      field. @bib:Gruenberg1970[Gruenberg (1970), Prop.~3, p.~254] showed that
      _every_ f.g. $ZZ' G$-module has a projective cover if and only if $G$ is a
      $p$-group for some prime $p$.],
  )
] <rem:semiperfect-projective-cover-context>

=== Injective Hulls <ss:injective-hulls>

Let $M,N$ be $A$-modules. An _essential monomorphism_#idx(
  "essential monomorphism",
)#footnote[
  In @bib:CurtisReiner1962[CR pp.~389–390], we refer to $N$ as a _related
  extension_#idx("related extension") of its submodule $f(M)$.
] $f:M -> N$ is a monomorphism such that for each sequence of $A$-modules
$ M arrow.r^f N arrow.r^g Y "with" g f "monic", $
the map $g$ is necessarily monic. Thus, a monomorphism $f:M -> N$ is essential
if and only if for each nonzero submodule $N'$ of $N$, the intersection
$N' inter f(M)$ is nonzero.

An _injective hull_#idx("injective hull") (or _injective envelope_#idx(
  "injective envelope",
)) of a module $M$ is a diagram $0 -> M arrow.r^f E$ with $f$ an essential
monomorphism and $E$ an injective module.

#source(157)
As shown in @bib:CurtisReiner1962[CR (57.13)], every module $M$ has an injective
hull [Eckmann-Schopf Theorem], which is uniquely determined up to isomorphism.
For example, $QQ$ is the injective hull of the $ZZ$-module $ZZ$.

Other references for this topic are @bib:Anderson1973[Anderson–Fuller (1973),
  pp.~72–75, pp.~206–209] and @bib:Behrens1972[Behrens (1972), pp.~179–182].

#proposition[
  Injective hulls are additive.
] <prop:injective-hulls-additive>

#proof[
  Let $0 -> M_i -> E_i$, $i=1,2$, be sequences of $A$-modules, where $E_i$ is
  the injective hull of $M_i$, and view $M_i$ as submodule of $E_i$. We claim
  that $E_1 plus.dot E_2$ is the injective hull of $M_1 plus.dot M_2$. Clearly
  $E_1 plus.dot E_2$ is injective, so we need only show that the map
  $M_1 plus.dot M_2 subset E_1 plus.dot E_2$ is essential, that is, for each
  nonzero submodule $Y$ of $E_1 plus.dot E_2$, the intersection
  $Y inter (M_1 plus.dot M_2) != 0$. Let $(e_1,e_2) in Y$ be nonzero; then (say
  $e_1 != 0$) $A e_1$ is a nonzero submodule of $E_1$, hence meets $M_1$. Thus
  there exists an $a in A$ with $a e_1=m_1 in M_1$, $m_1 != 0$. But
  $a(e_1,e_2) in Y$, so now $Y$ contains $(m_1,e'_2)$. If $e'_2=0$, then
  $(m_1,e'_2) in (M_1 plus.dot M_2) inter Y$, and $Y$ meets $M_1 plus.dot M_2$.
  If $e'_2 != 0$, then $A e'_2 inter M_2 != 0$, so there exists an element
  $b in A$ with $b e'_2=m_2 in M_2$, $m_2 != 0$. But then
  $ b(m_1,e'_2)=(b m_1,m_2) in (M_1 plus.dot M_2) inter Y $
  so again $Y$ meets $M_1 plus.dot M_2$. This completes the proof that
  $ E(M_1 plus.dot M_2) tilde.equiv E(M_1) plus.dot E(M_2), $
  if $E(quad)$ denotes injective hull.
]

Now let $A$ be a left artinian ring such that the left regular module
$attach(A, bl: A)$ is $A$-injective; we call $A$ (left) _self-injective_#idx(
  "self-injective",
), or _quasi-Frobenius_#idx("quasi-Frobenius"). As shown in
@bib:CurtisReiner1962[CR §~58, remarks following (58.5)], such a ring $A$ is
necessarily right artinian. Further (@bib:CurtisReiner1962[CR Exercise~58.5]),
$A_A$ is an injective right $A$-module. Thus the condition that $A$ be
quasi-Frobenius is left-right symmetric, and “left q-F” = “right q-F”.

#remarks(numbered: true)[
  #enum(
    numbering: "(i)",
    [The group algebra $K G$ of a finite group $G$ over an arbitrary field $K$
      is always self-injective (see @prop:group-algebra-symmetric and
      @prop:frobenius-algebra-properties (iii), and also
      Exercise~@exc:group-algebra-injective).],
    [Let $A$ be any artinian self-injective ring, and set $N=rad A$. Define
      $ r(N)="right annihilator of" N={a in A:N dot a=0}, $
      $ l(N)="left annihilator of" N={a in A:a dot N=0}. $
      Then (@bib:CurtisReiner1962[CR (58.12)] or @bib:Behrens1972[Behrens
        (1972), pp.~182–184])
      $ r(N)=l(N)="left socle of" A="right socle of" A, $
      #source(158)
      where the _socle_#idx("socle") of a module is the sum of its simple
      submodules. For the case of Frobenius algebras, see
      @prop:frobenius-algebra-properties.],
    [Let $A$ be an artinian self-injective ring. If $e$ is a primitive
      idempotent of $A$, then $A e$ has a unique simple submodule, given by
      $l(N)e$. Thus (see @bib:CurtisReiner1962[CR (58.12)]),
      $ "soc" A=op("⨁", limits: #true) l(N)e_i, $
      where $1_A=sum e_i$ is the decomposition of $1_A$ into primitive
      idempotents. Furthermore,
      $
        l(N)e tilde.equiv
        "dual of the simple right" A"-module" e A slash e N
        =Hom_A lr((e A slash e N,A)).
      $
      We have
      $
        A e_i tilde.equiv A e_j <=> A e_i slash N e_i tilde.equiv
        A e_j slash N e_j <=> l(N)e_i tilde.equiv l(N)e_j.
      $
      (Note: $N e$ is the unique maximal submodule of $A e$ (see
      @cor:indecomposable-projective-top), and $"soc" A$ denotes the socle of
      $A$.) (See @prop:frobenius-algebra-properties (ii) for the case of
      Frobenius algebras.)],
  )
] <rem:artinian-self-injective-socles>

#proposition[
  Let $P$ be any f.g. projective left $A$-module. Then
  $ ("soc" A)P="soc" P. $
] <prop:projective-module-socle>

#proof[
  Since $N dot "soc" A=0$ we have $N(("soc" A)P)=0$, so $("soc" A)P$ is a
  semisimple $A$-module, hence lies in $"soc" P$. We must prove equality. Write
  $P$ as a direct sum $product A e_i$, where the ${e_i}$ are primitive
  idempotents, and there may be repetitions. Then $"soc" P=product "soc" A e_i$,
  so it suffices to prove that
  $ ("soc" A) dot A e="soc" A e $
  for each primitive idempotent $e$. By
  @rem:artinian-self-injective-socles(iii), $"soc" A e$ is simple so we need
  only show that $("soc" A)A e != 0$ (because the previous remarks already imply
  that $("soc" A)A e subset.eq
  "soc" A e$). But
  $ ("soc" A)A e supset.eq l(N)e dot A e supset.eq l(N)e != 0. $
  This completes the proof.
]

#theorem(name: "Theorem", title: [E. L. Green])[
  Let $M$ be a f.g. left $A$-module, where $A$ is an artinian self-injective
  ring. Then
  $
    ("soc" A)M != 0 "if and only if" M
    "has a nonzero projective and injective direct summand".
  $
] <th:green-projective-summand-socle>

#source(159)
#proof[
  If $P$ is a nonzero projective $A$-module which is a direct summand of $M$,
  then $("soc" A)M supset.eq ("soc" A)P="soc" P != 0$, by
  @prop:projective-module-socle.

  Suppose conversely that $("soc" A)M != 0$, and let $f:P -> M$ be a projective
  cover of $M$. Then $f(("soc" A)P)=("soc" A)M != 0$, so there exists a
  primitive idempotent $e in A$ with $f(("soc" A) dot A e) != 0$, that is,
  $f("soc" A e) != 0$. We have a commutative diagram
  #projective-socle-injection-diagram
  with $f'$ nonzero (and hence an injection, since $"soc" A e$ is simple). But
  $ker f$ is a submodule of $A e$, and if $ker f != 0$, then $ker f$ would
  contain the unique simple submodule $"soc" A e$ of $A e$.

  This would imply that $f$ vanishes on $"soc" A e$, a contradiction since $f'$
  is the restriction of $f$ to $"soc" A e$. Hence $ker f=0$, so $A e -> M$ is an
  injection. But $A e$ is injective (because $A$ is self-injective), and
  therefore $A e$ is a direct summand of $M$, as desired.
]

The following theorem generalizes earlier results of
Alperin–Janusz~@bib:Alperin1973 and Heller~@bib:Heller1961b.

#theorem[
  Let $A$ be an artinian self-injective ring, and let
  $ 0 -> N arrow.r^f X arrow.r^g M -> 0 $
  be an exact sequence of f.g. $A$-modules, with $X$ projective. Then the
  following conditions are equivalent:
  #enum(
    numbering: "(i)",
    [$M$ is indecomposable, non-projective, and $g:X -> M$ is a projective cover
      of $M$.],
    [$N$ is indecomposable, non-injective, and $f:N -> X$ is an injective hull
      of $N$.],
  )
] <th:projective-cover-injective-hull-correspondence>

#proof[
  Since $A$ is quasi-Frobenius, $X$ is also injective. We prove that
  (i)$arrow.r.double$(ii), so assume (i). If $N$ were injective, the sequence
  would split, whence $M$ would be projective. Thus $N$ is not injective. Now
  $g:X -> M$ is a projective cover, whence by
  @cor:semiperfect-projective-cover-properties (i) we have
  $ N subset.eq J dot X,"where" J=rad A, $
  and where we are viewing $f$ as an inclusion map.

  #source(160)
  Next, by @th:green-projective-summand-socle we have $("soc" A)M=0$, since
  otherwise $M$ would have a projective direct summand. Consequently,
  $ g(("soc" A)X)=("soc" A)g(X)=0. $
  But $("soc" A)X="soc" X$ by @prop:projective-module-socle. Therefore
  $g("soc" X)=0$, so $"soc" X subset.eq N$. Hence $"soc" X subset.eq "soc" N$,
  whence $"soc" X="soc" N$. Thus there is a commutative diagram
  #socle-injective-hull-diagram
  where the vertical maps are inclusions. Any nonzero submodule $Y$ of $X$ meets
  $"soc" X$, hence meets $"soc" N$, hence meets $N$. This shows that the
  inclusion $N subset.eq X$ gives an injective hull of $N$.

  Finally, if $N=N_1 plus.o N_2$, and $X_i$ is an injective hull of $N_i$,
  $i=1,2$, there is a commutative diagram
  #injective-hull-decomposition-diagram
  where $M_i=X_i slash N_i$, in which $alpha,beta$ are isomorphisms. Hence
  $gamma$ is an isomorphism, so $M$ decomposes unless (say) $M_1=0$. But then
  $N_1=X_1$, while we know already that $N_1 subset.eq J X_1$ because
  $N subset.eq J X$; this gives $X_1=J X_1$, whence $X_1=0$ and $N_1=0$.
  Therefore $N$ is indecomposable, as claimed.

  The proof that (ii)$arrow.r.double$(i) is similar, and we omit it.
]

#exercises-heading

#exercise[
  Let $L,M$ be left $A$-modules satisfying the conditions of
  @th:krull-schmidt-azumaya. Show that if $L^((k)) tilde.equiv M^((k))$ for some
  positive integer $k$, then $L tilde.equiv M$.
] <exc:krull-schmidt-power-cancellation>

#exercise[
  Let $A$ be a f.d. $K$-algebra, where $K$ is a field, and let $M$ be a f.g.
  left $A$-module. For $E$ a field containing $K$, set
  $ A^E=E times.o_K A,M^E=E times.o_K M, $
  so $M^E$ is a module over the $E$-algebra $A^E$. Let $L$ be another f.g. left
  $A$-module. Prove that if $dim_K lr((E))$ is finite, then
  $
    L^E tilde.equiv M^E "as" A^E"-modules" <=>
    L tilde.equiv M "as" A"-modules".
  $
  <eq:finite-extension-module-isomorphism>

  #hint([@exc:finite-extension-module-isomorphism])[
    The map $a -> 1 times.o a$, $a in A$, embeds $A$ into $A^E$. Each
    $A^E$-module $X$ gives rise to an $A$-module $X|_A$ by restriction of
    operators. If $n=dim_K lr((E))$, then
    $ M^E|_A tilde.equiv M^((n)). $
    Hence $L^E tilde.equiv M^E$ implies $L^((n)) tilde.equiv M^((n))$, whence
    $L tilde.equiv M$ by Exercise~@exc:krull-schmidt-power-cancellation.
  ]
] <exc:finite-extension-module-isomorphism>

#source(161)
#exercise[
  (Generalization) Let $A$ be an $R$-algebra f.g./$R$, where $R$ is a complete
  local ring as in @th:krull-schmidt-azumaya. Let $R'$ be a commutative ring
  containing $R$, and suppose that $R'$ has a free $R$-basis ${x_1,dots,x_n}$
  with $x_1=1$. Let $M$ be any f.g. left $A$-module, and set
  $
    A'=R' times.o_R A,M'=R' times.o_R M
    tilde.equiv A' times.o_A M.
  $
  Let $L$ be another f.g. left $A$-module. Prove that
  $
    L' tilde.equiv M' "as" A'"-modules" <=>
    L tilde.equiv M "as" A"-modules".
  $

  #hint([@exc:free-base-extension-module-isomorphism])[
    $L'|_A tilde.equiv L^((n))$ as above.
  ]
] <exc:free-base-extension-module-isomorphism>

#exercise[
  Let $A$ be a left $K$-algebra, $L$ and $M$ f.g. $A$-modules, where
  $dim_K lr((A))$ is finite. Assume that $dim_K lr((L))=dim_K lr((M))=n$, and
  let $X_1,dots,X_r$ be a $K$-basis for $Hom_A lr((L,M))$. Put
  $ f(t_1,dots,t_r)=det(t_1 X_1+dots+t_r X_r), $
  where the ${t_i}$ are indeterminates over $K$. Show that $L tilde.equiv M$ as
  $A$-modules if and only if there exist elements ${alpha_i}$ in $K$ such that
  $f(alpha_1,dots,alpha_r) != 0$.
] <exc:isomorphism-determinant-polynomial>

#exercise[
  Keep the above notation, and suppose that the polynomial $f(t_1,dots,t_r)$ is
  not the zero polynomial. Show that if $"card" K > n$, then there exist
  elements ${alpha_i} in K$ with $f(alpha_1,dots,alpha_r) != 0$.

  #hint([@exc:nonzero-polynomial-large-field])[
    $f(t_1,dots,t_r)$ is homogeneous of degree $n$. Use induction on $r$ to show
    that $f$ cannot vanish on all $r$-tuples from $K$.
  ]
] <exc:nonzero-polynomial-large-field>

#exercise[
  (*Noether-Deuring Theorem*). Let $A$ be a f.d. $K$-algebra, where $K$ is a
  field, and let $L$ and $M$ be f.g. left $A$-modules. Let $E$ be any field
  containing $K$. Prove that if $L^E tilde.equiv M^E$ as left $A^E$-modules,
  then $L tilde.equiv M$ as left $A$-modules, and conversely.

  #hint([@exc:noether-deuring])[
    Suppose that $L^E tilde.equiv M^E$; then
    $
      dim_K lr((L))=dim_E lr((L^E))=dim_E lr((M^E))
      =dim_K lr((M))=n ("say").
    $
    Let the ${X_i}$ be as in Exercise~@exc:isomorphism-determinant-polynomial.
    By Exercise~@exc:hom-field-extension, these ${X_i}$ are also an $E$-basis
    for $Hom_(A^E) lr((L^E,M^E))$, so by
    Exercise~@exc:isomorphism-determinant-polynomial there exist elements
    ${beta_i}$ in $E$ for which $f(beta_1,dots,beta_r) != 0$. Hence
    $f(t_1,dots,t_r)$ is not the zero polynomial. If $"card" K > n$, then there
    exist ${alpha_i}$ in $K$ with $f(alpha_1,dots,alpha_r) != 0$, whence
    $L tilde.equiv M$. If $"card" K <= n$, let $F$ be a finite extension of $K$
    with $"card" F > n$. Then there exist elements ${gamma_i} in F$ with
    $f(gamma_1,dots,gamma_r) != 0$, whence
    $F times.o_K L tilde.equiv F times.o_K M$ by the preceding step. But then
    $L tilde.equiv M$ by Exercise~@exc:finite-extension-module-isomorphism.
  ] (See also §@ss:extension-ground-ring-local-theory for algebras over
  valuation rings.)
] <exc:noether-deuring>#idx(
  "Noether-Deuring Theorem",
  target: [@exc:noether-deuring],
)

#exercise[
  Does the Noether-Deuring Theorem remain valid if we assume that $L$ and $M$
  are left $A$-modules of finite $K$-dimension, but drop the hypothesis that
  $dim_K lr((A))$ be finite?

  #hint([@exc:noether-deuring-infinite-algebra])[
    See Exercise~@exc:hom-field-extension-finite-modules.
  ]
] <exc:noether-deuring-infinite-algebra>

#exercise[
  Let $A$ be an $R$-algebra as in @prop:radical-adic-completeness, and set
  $overline(A)=A slash P A$, where $P=rad R$. Show that if $e in A$ is an
  idempotent for which $overline(e)$ lies in the center of $overline(A)$, then
  $e$ lies in the center of $A$.

  #source(162)
  #hint([@exc:central-idempotent-lifting])[
    Consider the “Pierce decomposition”#idx("Pierce decomposition")
    $
      A=e A e plus.o e A(1-e) plus.o (1-e)A e
      plus.o (1-e)A(1-e)
    $
    of $A$ into $R$-submodules. Passing to $overline(A)$, we obtain a
    corresponding decomposition of $overline(A)$. But
    $overline(e)overline(A)(overline(1)-overline(e))=0$, so $e A(1-e)$ is an
    $R$-direct summand of $A$ such that $e A(1-e) slash P dot e A(1-e)=0$. Hence
    $e A(1-e)=0$, and likewise $(1-e)A e=0$. Therefore
    $ A=e A e plus.o (1-e)A(1-e), $
    so each $a in A$ commutes with $e$. (This result is due to Dade.)
  ]
] <exc:central-idempotent-lifting>

#exercise[
  Let $A$ be a local ring, $M$ any f.g. projective left $A$-module. Prove that
  $M$ is a free $A$-module.

  #hint([@exc:projective-local-free])[
    Let bars denote reduction modulo $rad A$. Then $overline(A)$ is a skewfield,
    and $overline(M)$ is a left $overline(A)$-module. (Further, if $M != 0$ then
    $overline(M) != 0$ by Nakayama's Lemma.) Thus
    $overline(M) tilde.equiv overline(A)^((k))$ for some $k$. But then
    $M tilde.equiv A^((k))$ by @prop:projective-isomorphism-modulo-radical.
  ]
] <exc:projective-local-free>

#exercise[
  Let $A$ be a semiperfect ring with radical $N$, and let $I subset.eq N$,
  $I="two-sided ideal of" A$. Let $X$ be any f.g. projective left
  $(A slash I)$-module. Show that there exists a f.g. projective left $A$-module
  $P$ such that $P slash I P tilde.equiv X$, and that this isomorphism lifts to
  a projective cover $P -> X$ of $X$ viewed as $A$-module.

  #hint([@exc:projective-module-lifting-ideal])[
    By @th:semiperfect-projective-covers, there is an $A$-projective cover
    $f:P -> X$. This yields a commutative diagram
    #projective-module-lifting-diagram
    where $f$ induces $g$ and $h$, and where $h$ is an isomorphism. But $I X=0$,
    so $X slash I X$ is $(A slash I)$-projective. Therefore
    $ P slash I P tilde.equiv (X slash I X) plus.o Y $
    for some $(A slash I)$-module $Y$. This gives
    $ P slash N P tilde.equiv (X slash N X) plus.o (Y slash N Y), $
    whence $Y slash N Y=0$, so $Y=0$.
  ]
] <exc:projective-module-lifting-ideal>

#exercise[
  (*Hensel's Lemma*). Let $R$ be a complete commutative local noetherian ring
  (such as, for example, a complete discrete valuation ring), and let
  $overline(R)=R slash rad R$ be its residue class field. Let $f(X) in R[X]$ be
  a monic polynomial, and let $overline(f)$ denote its image in
  $overline(R)[X]$. Prove that every factorization of $overline(f)$ into
  pairwise relatively prime monic polynomials ${phi_i}$ in $overline(R)[X]$
  lifts to a factorization of $f(X)$ in $R[X]$.

  #hint([@exc:hensel-factorization])[
    Set $A=R[X] slash (f(X))$, an $R$-algebra which is $R$-free on $"deg" f$
    generators. Then
    #source(163)
    $overline(A)=A slash (rad R)A=overline(R)[X] slash (overline(f)(X))$. If
    $overline(f)=product_(i=1)^m phi_i$, $phi_i in overline(R)[X]$, then there
    is a decomposition of $overline(A)$ into left ideals:
    $
      overline(A) tilde.equiv product_1^m
      overline(R)[X] slash (phi_i lr((X))).
    $
    Correspondingly, we may write $overline(1)=sum_1^m epsilon_i$, with the
    ${epsilon_i}$ idempotents in $overline(A)$, and where $epsilon_i$ generates
    the $i$-th summand. By @th:complete-ring-idempotent-decompositions, there is
    a corresponding decomposition of $A$, given by
    $A=op("⨁", limits: #true) A e_i$, where $overline(e)_i=epsilon_i$. Then
    $A e_i tilde.equiv R[X] slash (g_i lr((X)))$, for some monic
    $g_i lr((X)) in R[X]$ such that $g_i lr((X)) divides f(X)$, and
    $overline(g)_i=phi_i$. Thus $f=product g_i$ is the desired factorization of
    $f$.
  ]
] <exc:hensel-factorization>#idx(
  "Hensel's Lemma",
  target: [@exc:hensel-factorization],
)

#exercise[
  Let $A$ be a ring, and $M$ an artinian left $A$-module. Denote by $"soc" M$
  the _socle_ of $M$, that is, the sum of all simple submodules of $M$. Show
  that $M$ and $"soc" M$ have the same injective hull.

  #hint([@exc:artinian-module-socle-injective-hull])[
    Let $0 -> M -> E$ be exact, where $E$ is an injective hull of $M$. Then also
    $0 -> "soc" M -> E$ is exact. If $X$ is a nonzero submodule of $E$, then
    $X inter M != 0$ since $E$ is an injective hull of $M$. But $X inter M$ is a
    nonzero submodule of the artinian module $M$, and hence contains a simple
    submodule $S$. Then $X inter "soc" M supset.eq S$, which proves that $E$ is
    also an injective hull of $"soc" M$.
  ]
] <exc:artinian-module-socle-injective-hull>

#exercise[
  Let the ring $A$ be either left artinian, or else an $R$-algebra as in
  @prop:radical-adic-completeness. Let $P$ be a f.g. projective $A$-module. Show
  that if $P$ is indecomposable (as $A$-module), then every nonzero factor
  module of $P$ is also indecomposable.

  #hint([@exc:indecomposable-projective-quotients])[
    Let $N=rad A$; then $P$ has a unique maximal submodule, namely $N dot P$. If
    $f:P -> X$ is surjective, where $X != 0$, then $ker f subset.eq N dot P$.
    Hence $f$ gives a projective cover of $X$. But if $X$ decomposes, so does
    its projective cover by @cor:semiperfect-projective-cover-properties (iii).
  ]
] <exc:indecomposable-projective-quotients>

#exercise[
  Let $A$ be an arbitrary ring, and let
  $ 1=e_1+dots+e_n=f_1+dots+f_n $
  be two decompositions of $1_A$ into a sum of orthogonal idempotents. Suppose
  that $A e_i tilde.equiv A f_i$ as left $A$-modules, $1 <= i <= n$. Show that
  there exists a unit $u in A$ such that
  $ u f_i u^(-1)=e_i "for each" i. $

  #hint([@exc:conjugate-idempotent-decompositions])[
    Let $phi$ be the automorphism of the left $A$-module $A$ which maps each
    $A e_i$ isomorphically onto $A f_i$. Then $phi=u_r$ for some unit $u in A$,
    and
    $ A e_i dot u=A f_i,A f_i dot u^(-1)=A e_i,1 <= i <= n. $
    Then
    $
      1=sum_(i=1)^n u f_i u^(-1),u f_i u^(-1) in A e_i
      "for each" i.
    $
    Hence $u f_i u^(-1)=e_i$ for each $i$.
  ]
] <exc:conjugate-idempotent-decompositions>

#source(164)
#exercise[
  Let $e$ and $f$ be idempotents in a semisimple ring $A$, and suppose that
  $A e tilde.equiv A f$. Show that $e=u f u^(-1)$ for some unit $u in A$.

  #hint([@exc:semisimple-isomorphic-idempotents-conjugate])[
    The left $A$-isomorphism
    $ A e plus.o A(1-e) tilde.equiv A f plus.o A(1-f) $
    shows that if $A e tilde.equiv A f$, then also $A(1-e) tilde.equiv A(1-f)$.
  ]
] <exc:semisimple-isomorphic-idempotents-conjugate>

#exercise[
  Let $R$ be a d.v.r. with maximal ideal $P$ and quotient field $K$, and let $A$
  be a split semisimple $K$-algebra. Let $Lambda$ be an $R$-order in $A$, that
  is, an $R$-subalgebra of $A$ such that $K Lambda=A$ and $Lambda$ is f.g./$R$
  as module. Let $overline(Lambda)=Lambda slash P Lambda$. Show that every
  idempotent $epsilon$ of $overline(Lambda)$ lifts to an idempotent $e_0$ of
  $Lambda$, and that if $epsilon$ is central so is $e_0$.

  #hint([@exc:split-order-idempotent-lifting])[
    Let $hat(quad)$ denote $P$-adic completions. Then
    $hat(Lambda) slash P hat(Lambda) tilde.equiv overline(Lambda)$, and
    $epsilon$ lifts to an idempotent $e in hat(Lambda)$. The hypothesis on $A$
    implies that every f.g. left $hat(Lambda)$-module is the completion of some
    f.g. left $Lambda$-module. Therefore
    $hat(Lambda)e tilde.equiv hat(Lambda)e_1$ for some idempotent
    $e_1 in Lambda$. But then $e=u e_1 u^(-1)$ for some invertible element
    $u in hat(A)$ (see
    Exercise~@exc:semisimple-isomorphic-idempotents-conjugate). Choose $v in A$
    close to $u$ in the $P$-adic topology on $hat(A)$; then $v^(-1)$ exists in
    $A$, and is close to $u^(-1)$. Set $e_0=v e_1 v^(-1) in A$, so $e_0$ is
    idempotent and close to $e$. Since ${P^n hat(Lambda):n=0,1,2,dots}$ is a
    fundamental system of neighborhoods of $0$ in $hat(Lambda)$, it follows that
    $e_0 in hat(Lambda)$ and $overline(e)_0=overline(e)=epsilon$. Then
    $e_0 in A inter hat(Lambda)$, so $e_0 in Lambda$. If $epsilon$ is central,
    so is $e_0$, by Exercise~@exc:central-idempotent-lifting.
  ]
] <exc:split-order-idempotent-lifting>
