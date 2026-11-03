#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/25-extensions-lattices.typ": extension-equivalence-diagram

== Extensions of Lattices <sec:extensions-lattices>

Throughout this section, let $R$ be a commutative ring, and let $Lambda$ be an
$R$-algebra. Our main interest is in the case where $R$ is a Dedekind domain
with quotient field $K$, and $Lambda$ is an $R$-order in a f.d. $K$-algebra $A$.
In this situation, let $L$ be some full $Lambda$-lattice in a f.g. left
$A$-module $V$, so $V=K dot L$. We hope to use our knowledge of $V$ and its
submodules to obtain information about $L$. If we start with an $A$-composition
series for $V$ (see Exercise~@exc:order-lattice-composition-series) and
intersect its terms with $L$, we obtain a strictly decreasing chain of
$Lambda$-sublattices of $L$. In particular, suppose $V$ contains a nonzero
proper $A$-submodule $W$. Setting $M=L inter W$, it follows from
@cor:full-order-lattice-existence that $M$ is a full $Lambda$-lattice in $W$,
and that the factor module $L slash M$ is (isomorphic to) a full
$Lambda$-lattice in $V slash W$. Thus, the $A$-exact sequence
$ 0 -> W -> V -> V slash W -> 0 $
#source(561)
gives rise to an exact sequence of $Lambda$-lattices#footnote[
  The fact that $N$ is a $Lambda$-lattice, rather than an arbitrary f.g.
  $Lambda$-module, will be extremely important in our later discussion.
]:
$ 0 -> M -> L -> N -> 0, "where" N=L slash M. $
The sequence is necessarily $R$-split since $N$ is $R$-projective, and thus
$L=M plus.o N$ as $R$-modules, though this need not be a $Lambda$-isomorphism.

In practice, our aim is to construct the $Lambda$-module $L$ from the pair of
$Lambda$-modules $M$ and $N$. We shall discuss this question in terms of the
$R$-module $op("Ext")_Lambda^1 lr((N,M))$, whose elements correspond to
equivalence classes of extensions of $N$ by $M$ (see §@ss:ext-tor, and
especially the paragraphs following @prop:ext-finite-generation). Then we shall
treat the same question from the standpoint of derivations, and shall later
sketch a matrix approach to such calculations. For the most part, $R$ may be any
commutative ring. The restriction to Dedekind domains is needed mainly in
@prop:extension-torsion, @cor:extension-primary-decomposition,
@th:extension-localization-group-order and @cor:projective-prime-divisors.

Let $Lambda$ be an $R$-algebra, where $R$ is any commutative ring. Recall that a
$Lambda$-lattice is a left $Lambda$-module which is f.g. and projective as
$R$-module. Later we shall restrict our attention to $Lambda$-lattices, but for
the time being we work with $Lambda$-modules. Given a pair of $Lambda$-modules
$M$ and $N$, an _extension of $N$ by $M$_ #idx("extension of modules") is a
$Lambda$-exact sequence
$ 0 -> M -> X -> N -> 0. $ <eq:lattice-extension>
(Often, the module $X$ itself is called an extension of $N$ by $M$). As noted
earlier, if $N$ is a $Lambda$-lattice, the sequence @eq:lattice-extension is
$R$-split, and $X=M plus.o N$ as $R$-modules. Hence if $M$ and $N$ are
$Lambda$-lattices, then so is $X$.

Now let
$ xi_i:0 -> M -> X_i -> N -> 0, i=1,2, $
be a pair of extensions of $N$ by $M$. As in §@ss:ext-tor, we call these
extensions _equivalent_ if there exists a commutative diagram
#extension-equivalence-diagram(named: true)
(The $Lambda$-homomorphism $phi$ occurring here is necessarily an isomorphism.)
These equivalence classes of extensions then form an $R$-module
$op("Ext")_Lambda^1 lr((N,M))$. We caution the reader that there exist cases
where $X_1 tilde.equiv X_2$ even though $xi_1 != xi_2$ in
$op("Ext")_Lambda^1 lr((N,M))$.

#source(562)
We have described in §@ss:ext-tor one method of calculating
$op("Ext")_Lambda^1 lr((N,M))$, which goes as follows. Let us start with an
exact sequence of $Lambda$-lattices
$ 0 -> Q arrow.r^i P -> N -> 0, P "projective". $
Then
$
  op("Ext")_Lambda^1 lr((N,M)) tilde.equiv
  Hom_Lambda lr((Q,M)) slash i^* lr({Hom_Lambda lr((P,M))}),
$
<eq:extension-projective-presentation>
and we have given this isomorphism explicitly in the remarks following
@eq:extension-connecting-hom. We shall give below some examples illustrating how
to use @eq:extension-projective-presentation to calculate $op("Ext")(N, M)$, but
before doing so, let us derive a number of basic facts about such Ext groups.

Suppose for the moment that $Lambda$ is an $R$-order in a f.d. $K$-algebra $A$,
where $R$ is a Dedekind domain with quotient field $K$.

It follows as a special case of @prop:ext-finite-generation that for any pair of
$Lambda$-lattices $M$ and $N$, the group $op("Ext")_Lambda^1 lr((N,M))$ is a
f.g. $R$-module. (Indeed, it is also a f.g. $Lambda$-module whenever $Lambda$ is
commutative.) Let $S$ be any multiplicative subset of $R$; by
@cor:ext-tor-localization we have
$
  S^(-1) R times.o_R op("Ext")_Lambda^1 lr((N,M)) tilde.equiv
  op("Ext")_(S^(-1) Lambda)^1 lr((S^(-1) N,S^(-1) M))
$
<eq:extension-localization>
as $S^(-1) R$-modules. For the special case where $S=R-{0}$, this gives
$
  K times.o_R op("Ext")_Lambda^1 lr((N,M)) tilde.equiv op("Ext")_A^1 lr(
    (K N,K
      M)
  ).
$
<eq:extension-quotient-field>
We use this to show:

#proposition[
  Let $M$ and $N$ be $Lambda$-lattices, where $Lambda$ is an $R$-order in a
  semisimple f.d. $K$-algebra $A$. Then $op("Ext")_Lambda^1 lr((N,M))$ is a f.g.
  torsion $R$-module, that is, each element thereof is annihilated by some
  nonzero element of $R$.
] <prop:extension-torsion>
#proof[
  We have already remarked that $op("Ext")_Lambda^1 lr((N,M))$ is f.g./$R$.
  Next, since $A$ is semisimple, every $A$-module is projective, so the right
  hand side of @eq:extension-quotient-field is zero. But then
  $op("Ext")_Lambda^1 lr((N,M))$ is an $R$-torsion $R$-module, by
  §@ss:localization.
]

#corollary[
  Keep the above hypotheses, let $P$ range over all maximal ideals of $R$, and
  let the subscript $P$ denote localization at $P$. Then
  $
    op("Ext")_Lambda^1 lr((N,M)) tilde.equiv
    plus.o.big_P op("Ext")_(Lambda_P)^1 lr((N_P,M_P)),
  $
  and $op("Ext")_(Lambda_P)^1 lr((N_P,M_P))=0$ a.e.#footnote[
    “a.e.” means “almost everywhere”, that is, for all but a finite number of
    $P$'s.
  ] (See also @prop:extension-localization-nonmaximal-primes.)
] <cor:extension-primary-decomposition>
#idx("deLeeuw's Theorem", target: [@cor:extension-primary-decomposition])

#source(563)
#proof[
  For each $P$, we have
  $
    R_P times.o_R op("Ext")_Lambda^1 lr((N,M)) tilde.equiv
    op("Ext")_(Lambda_P)^1 lr((N_P,M_P))
  $
  by @eq:extension-localization. Since $op("Ext")_Lambda^1 lr((N,M))$ is a f.g.
  torsion $R$-module, the desired result follows at once from the Primary
  Decomposition Theorem~@th:primary-decomposition-dedekind. The result is due to
  deLeeuw~@bib:DeLeeuw1953; see also Nunke~@bib:Nunke1959,
  Reiner~@bib:Reiner1959.
]
#idx("deLeeuw's Theorem")

Returning to the case where $R$ is any commutative ring and $Lambda$ is an
$R$-algebra, we proceed to interpret $op("Ext")_Lambda^1 lr((N,M))$ in terms of
derivations. This will yield additional information about Ext, and will give
another method for calculating it. Let us begin with some definitions. Let $T$
be a $(Lambda,Lambda)$-bimodule, and suppose that $T$ is _centralized by
$R$_#idx("centralize"), that is,
$ a t=t a "for all" a in R,t in T. $
A _derivation_#idx("derivation") $F:Lambda -> T$ is an $R$-homomorphism
satisfying
$
  F_(lambda' lambda)=lambda' F_lambda+F_(lambda') lambda
  "for all" lambda,lambda' in Lambda.
$ <eq:bimodule-derivation>
Let $"Der"(Lambda,T)$ be the $R$-module consisting of all derivations from
$Lambda$ into $T$. For each $theta in T$, the map
$ lambda mapsto theta lambda-lambda theta,lambda in Lambda, $
<eq:inner-bimodule-derivation>
is a derivation, called an _inner_ or _principal derivation_. #idx(
  "derivation",
  "inner",
)#idx("derivation", "principal")
#idx("inner derivation")
The set of all inner derivations is then an $R$-submodule of $"Der"(Lambda,T)$.
We now define
$ H^1 lr((Lambda,T))="Der"(Lambda,T) slash "inner derivations". $
<eq:bimodule-first-cohomology>
Then $H^1 lr((Lambda,T))$ is an $R$-module, called the _first cohomology
group_#idx("first cohomology group")#idx("cohomology group") of $Lambda$ with
respect to $T$.

Now let $M$ and $N$ be left $Lambda$-modules. As in §@ss:homomorphisms,
$Hom_R lr((N,M))$ has a natural structure as a $(Lambda,Lambda)$-bimodule
centralized by $R$. Explicitly, we have
$
  (lambda f)n=lambda dot f(n), (f lambda)n=f(lambda n)
  "for all" lambda in Lambda,n in N,f in Hom_R lr((N,M)).
$
We shall establish

#proposition[
  There exists an $R$-isomorphism
  $ op("Ext")_Lambda^1 lr((N,M)) tilde.equiv H^1 lr((Lambda,Hom_R lr((N,M)))) $
  whenever $N$ is a $Lambda$-lattice, and $M$ any $Lambda$-module.
] <prop:extensions-bimodule-cohomology>

Before proving @prop:extensions-bimodule-cohomology, we require some further
discussion of derivations. Suppose we are given an extension
@eq:lattice-extension in which $N$ is any $R$-lattice, and let
#source(564)
us view $M$ as a submodule of $X$. Since $N$ is $R$-projective, the sequence
$ 0 -> M -> X arrow.r^f N -> 0 $
is $R$-split. Thus by @prop:split-short-exact-sequence there exists an
$R$-homomorphism $h:N -> X$ such that $f compose h=1$ on $N$. For each
$lambda in Lambda$, let
$ F_lambda (n)=h(lambda n)-lambda h(n),n in N. $
Since $f$ is a $Lambda$-homomorphism, we have $f(F_lambda (n))=0$ for each $n$,
so $F_lambda (n) in M$. The functions $F_lambda:N -> M$ evidently measure the
extent to which the map $h:N -> X$ fails to be a $Lambda$-homomorphism. Clearly
the map
$
  F:Lambda -> Hom_R lr((N,M)),"defined by" lambda mapsto F_lambda,
  lambda in Lambda,
$
is an $R$-homomorphism. In fact, $F$ is a derivation because for all
$lambda,lambda' in Lambda$ we have (for all $n in N$):
$
  F_(lambda lambda')(n) & =h((lambda lambda')n)-(lambda lambda')h(n)
                          =h(lambda(lambda' n))-lambda(lambda' h(n)) \
                        & =F_lambda (lambda' n)+lambda h(lambda'
                            n)-lambda(lambda' h(n))
                          =F_lambda (lambda' n)+lambda F_(lambda')(n),
$
using the fact that $M$ and $N$ are $Lambda$-modules.

It will be somewhat more convenient for us to work with ordered pairs. Here we
replace the preceding derivation $F$ by $-F$. We may write $X=M plus.o N$ as
$R$-modules, where $M$ is viewed as a $Lambda$-submodule of $X$. Each $x in X$
may then be uniquely expressed as an ordered pair $(m,n)$ from $M plus.o N$. The
$Lambda$-action on $X$ defining the extension is given by
$
  lambda(m, 0)=(lambda m,0),lambda(0, n)=(F_lambda (n),lambda n)
  "for all" m in M,n in N,lambda in Lambda,
$ <eq:extension-derivation-action>
for some element $F_lambda (n)$ in $M$. Here, $lambda m$ is computed inside the
$Lambda$-module $M$, and $lambda n$ inside the $Lambda$-lattice
$N tilde.equiv X slash M$. The map $lambda mapsto F_lambda$, $lambda in
Lambda$, gives an $R$-homomorphism
$ F:Lambda -> Hom_R lr((N,M)). $
Then the condition
$
  (lambda lambda')(m,n)=lambda(lambda'(m,n))
  "for all" lambda,lambda' in Lambda,m in M,n in N,
$
is satisfied if and only if @eq:bimodule-derivation holds true, that is, if and
only if $F$ is a derivation from $Lambda$ into the $(Lambda,Lambda)$-bimodule
$Hom_R lr((N,M))$. Conversely, each derivation $F$ allows us to make
$M plus.o N$ into a $Lambda$-module, with the action of $Lambda$ given by
@eq:extension-derivation-action; this module is then an extension of $N$ by $M$.

We must still determine the effect on the derivation $F$ if we use a different
$R$-splitting $N -> X$ of @eq:lattice-extension. We must also decide under which
conditions
#source(565)
another extension $0 -> M -> X' -> N -> 0$, with derivation $F'$, is equivalent
to the original extension in @eq:lattice-extension. Both questions can be
answered by the same calculation, as follows: the two extensions are equivalent
if and only if there is a commutative diagram
#extension-equivalence-diagram(named: false)
in which $phi:X tilde.equiv X'$ is a $Lambda$-isomorphism. The map $phi$ must
then be given by
$ phi(m, n)=(m+theta(n),n) "for all" m in M,n in N, $
where $theta in Hom_R lr((N,M))$. For each $lambda in Lambda$, we then have
$
  phi lambda(m, n) & =phi(lambda m+F_lambda (n), lambda n)
                     =(lambda m+F_lambda (n)+theta(lambda n),lambda n), \
  lambda phi(m, n) & =lambda(m+theta(n), n)
                     =(lambda m+F'_lambda (n)+lambda theta(n),lambda n).
$
Therefore
$ F'_lambda=F_lambda+theta lambda-lambda theta "for all" lambda in Lambda, $
so $F'-F$ is an inner derivation. The process is reversible, and it follows
readily that change of $R$-splitting of @eq:lattice-extension changes the
derivation $F$ by adding an inner derivation. Likewise, two derivations $F$ and
$F'$ yield equivalent extensions if and only if $F'-F$ is inner. We have
therefore established the isomorphism asserted in
@prop:extensions-bimodule-cohomology. Note that it holds when $N$ is any
$Lambda$-lattice and $M$ an arbitrary $Lambda$-module. However,
@prop:extensions-bimodule-cohomology need not be valid when both $M$ and $N$ are
arbitrary $Lambda$-modules.

We shall now prove a fundamental result, which may be regarded as a
generalization of Maschke's Theorem~@th:maschke, and is in fact a special case
of Proposition~@prop:group-order-annihilates-tate:
#idx("Maschke's Theorem")

#theorem[
  Let $G$ be a finite group, and let $Lambda=R G$ be its group ring over a
  commutative ring $R$. Let $T$ be any $(Lambda,Lambda)$-bimodule centralized by
  the elements of $R$. Then
  $ |G| H^1 lr((Lambda,T))=0. $
  In particular,
  $
    |G| dot op("Ext")_(R G)^1 lr((N,M))=0
  $ <eq:group-order-annihilates-extensions>
  for every $R G$-lattice $N$ and $R G$-module $M$.
] <th:group-order-annihilates-bimodule-cohomology>

#source(566)
#proof[
  Let $F:Lambda -> T$ be a derivation. Then for all $x,y in G$ we have
  $ F_(x y)=x F_y+F_x y. $ <eq:group-ring-derivation>
  Multiplying on the right by $y^(-1)$, and summing over all $y in G$, we obtain
  $ sum_y F_(x y)y^(-1)=x dot S+|G| dot F_x "for all" x in G, $
  where $S=sum_y F_y dot y^(-1)$. But
  $ sum_y F_(x y)y^(-1)=sum_y F_(x y)(x y)^(-1) dot x=S x. $
  Therefore
  $ |G| F_x=S x-x S "for all" x in G. $
  Since $F$ is $R$-linear, we then obtain
  $ |G| F_lambda=S lambda-lambda S "for all" lambda in Lambda, $
  so $|G| dot F$ is an inner derivation, and the proof is complete. (For the
  connection between this theorem and @prop:group-order-annihilates-tate, see
  Exercise~@exc:group-cohomology-annihilation-derivation.)
]

A number of important refinements of @eq:group-order-annihilates-extensions will
be given later; see especially §@sec:annihilator-ext.

We are now in a position to sharpen the results of
@cor:extension-primary-decomposition in the special case where $Lambda$ is an
integral group ring. The following result will be used repeatedly in later
sections:

#theorem[
  Let $R$ be a Dedekind domain, $G$ a finite group of order $n$, and suppose
  that $n!=0$ in $R$. Let $M$ and $N$ be a pair of $R G$-lattices. Then $n$
  annihilates $op("Ext")_(R G)^1 lr((N,M))$, and there is an $R$-isomorphism
  $
    op("Ext")_(R G)^1 lr((N,M)) tilde.equiv
    plus.o.big_(P ∋ n) op("Ext")_(R_P G)^1 lr((N_P,M_P)),
  $
  the direct sum extending over all maximal ideals $P$ of $R$ which contain $n$.
  (There are finitely many such $P$'s.)
] <th:extension-localization-group-order>
#proof[
  Write Ext instead of $op("Ext")_(R G)^1$, etc., for brevity. Then
  $n dot op("Ext")(N, M)=0$ by @eq:group-order-annihilates-extensions. Hence
  $[op("Ext")(N, M)]_P=0$ whenever $P$ does not contain $n$, by
  Exercise~@exc:localization-zero-annihilator. The above isomorphism thus
  follows from @cor:extension-primary-decomposition and its proof.
]

#corollary[
  Keep the above notation. An $R G$-lattice $N$ is $R G$-projective if and only
  if $N_P$ is $R_P G$-projective for each $P$ containing $|G|$.
] <cor:projective-prime-divisors>

#source(567)
#remarks(numbered: false)[
  #enum(
    numbering: "(i)",
    [Compare this result with @prop:projectivity-localization.],
    [In the special case where $R=K$, @th:extension-localization-group-order
      says that if $char K divides.not |G|$, then
      $op("Ext")_(K G)^1 lr((N,M))=0$ for each pair of f.g. left $K G$-modules
      $M$ and $N$. Thus every short exact sequence of f.g. $K G$-modules must
      split, which implies that the group algebra $K G$ is semisimple. Hence we
      obtain Maschke's Theorem as a special case of
      @th:extension-localization-group-order. This is hardly surprising,
      however, since @th:group-order-annihilates-bimodule-cohomology is proved
      by exactly the same calculation occurring in the proof of Maschke's
      Theorem~@th:maschke.],
  )
]

We shall now describe another approach to the calculation of Ext of a pair of
$Lambda$-lattices, which does not use any of the machinery of homological
algebra, but is instead based on the isomorphism
@prop:extensions-bimodule-cohomology. We restrict our attention to the case
where $R$ is a Dedekind domain with quotient field $K$, and $Lambda$ is an
$R$-order in a f.d. semisimple $K$-algebra $A$. Set
$ T=Hom_R lr((N,M)), K T=Hom_K lr((K N,K M)). $
Then $T$ is a $(Lambda,Lambda)$-bimodule, and is an $R$-lattice. The injection
$T -> K times.o_R T$ allows us to write $K times.o_R T$ as $K T$, and the above
expression for $K T$ is then a consequence of @prop:localization-hom-ext. Thus,
$T$ is a full $R$-lattice in the $(A,A)$-bimodule $K T$. Since $A$ is
semisimple, we have (using @prop:extensions-bimodule-cohomology)
$ 0=op("Ext")_A^1 lr((K N,K M))=H^1 lr((A,K T)). $
Thus, every derivation $F:Lambda -> T$ extends to an inner derivation
$F^*:A -> K T$, that is, there exists an element $theta in K T$ such that
$ F^*(a)=a theta-theta a "for all" a in A. $
(We write $F^*(a)$ instead of $F_a^*$ for convenience of notation.) It follows
that
$ F(lambda)=lambda theta-theta lambda "for all" lambda in Lambda. $
<eq:extension-inner-rational-derivation>
The condition $F(lambda)N subset.eq M$ for all $lambda in Lambda$ may be written
thus:
$ (lambda theta-theta lambda)N subset.eq M "for all" lambda in Lambda. $
<eq:extension-integrality-condition>
Conversely, starting with any $theta in K T$ satisfying
@eq:extension-integrality-condition, formula
@eq:extension-inner-rational-derivation defines a derivation $F:Lambda -> T$.
Furthermore, $F$ is inner if and only if there exists an element $theta_0 in T$
such that
$
  lambda theta-theta lambda=lambda theta_0-theta_0 lambda
  "for all" lambda in Lambda,
$
that is, if and only if $theta-theta_0 in Hom_A lr((K N,K M))$.

Let us set
$
  Omega={theta in Hom_K lr((K N,K M)):
    (lambda theta-theta lambda)N subset.eq M "for all" lambda in Lambda},
$
#source(568)
and let
$ Omega_0=Hom_R lr((N,M))+Hom_A lr((K N,K M)). $
We have thus established $R$-isomorphisms
$
  Omega slash Omega_0 tilde.equiv H^1 lr(
    (Lambda,Hom_R lr((N,M)))
  ) tilde.equiv op("Ext")_Lambda^1 lr((N,M)),
$ <eq:extensions-integrality-quotient>
the first of which is induced by the map which carries each $theta in Omega$
onto the derivation $F$ defined by @eq:extension-inner-rational-derivation.

In practice, to calculate $Omega$ we must find all elements $theta in K T$ for
which condition @eq:extension-integrality-condition is satisfied. In verifying
@eq:extension-integrality-condition, it obviously suffices to let $lambda$ range
over a set of $R$-generators for $Lambda$. Further, it is easily verified that
if @eq:extension-integrality-condition holds for $lambda$ and $lambda'$, it also
holds for $lambda lambda'$. This leads to the following simpler description of
$Omega$, in the special case where $Lambda$ is an integral group ring $R G$, and
$G=chevron.l g_1,...,g_n chevron.r$:
$
  Omega={theta in Hom_K lr((K N,K M)):
    (g_i theta-theta g_i)N subset.eq M,1<=i<=n}.
$
<eq:extension-integrality-generators>
We shall illustrate the calculation of $op("Ext")_(R G)^1 lr((N,M))$ by means of
@eq:extensions-integrality-quotient and @eq:extension-integrality-generators, in
Example~@exm:dihedral-lattice-extensions below.

Next, let us give a matrix formulation of the problem of calculating extensions
of lattices. We consider here the case where $R$ is a P.I.D. with quotient field
$K$, and $Lambda$ is an $R$-order in a f.d. $K$-algebra $A$. Every
$Lambda$-lattice then has a finite $R$-basis. In particular, let
$0 -> M -> L -> N -> 0$ be a short exact sequence of $Lambda$-lattices, and
choose $R$-bases so that
$
  L=plus.o.big_(i=1)^d R x_i,
  M=plus.o.big_(i=1)^k R x_i,
  N=L slash M=plus.o.big_(i=k+1)^d R overline(x)_i,
$
where $overline(x)_i$ is the image of $x_i$ in $L slash M$. For each
$lambda in Lambda$, we write
$
  lambda x_j=sum_(i=1)^d a_(i j) x_i,
  a_(i j) in R,1<=j<=d,
$
and let $bold(upright(L))(lambda)=(a_(i j))_(1<=i,j<=d)$. Thus $L$ affords the
matrix representation $bold(upright(L))$ of $Lambda$, and we find at once that
$
  bold(upright(L))(lambda)=mat(
    bold(upright(M))(lambda), bold(upright(T))(lambda);
    0, bold(upright(N))(lambda)
  ),lambda in Lambda,
$
<eq:extension-block-representation>
where $M$ and $N$ afford the representations $bold(upright(M))$ and
$bold(upright(N))$, respectively. The identity
$
  bold(upright(L))(lambda lambda')=
  bold(upright(L))(lambda)bold(upright(L))(lambda')
  "for all" lambda,lambda' in Lambda
$
#source(569)
yields the condition
$
  bold(upright(T))(lambda lambda')=
  bold(upright(M))(lambda)bold(upright(T))(lambda')+
  bold(upright(T))(lambda)bold(upright(N))(lambda')
  "for all" lambda,lambda' in Lambda.
$
It follows at once that $bold(upright(T))$ is a derivation from $Lambda$ into
the bimodule of $k times (d-k)$ matrices over $R$. The element
$lambda in Lambda$ acts from the left on this bimodule as multiplication by
$bold(upright(M))(lambda)$, and on the right as $bold(upright(N))(lambda)$.
(This derivation $bold(upright(T))$ is also called a _binding system_ #idx(
  "binding system",
) for the pair of matrix representations $bold(upright(M))$ and
$bold(upright(N))$; see @bib:CurtisReiner1962[CR (73.14)], for instance.)

Suppose now that
$
  mat(bold(upright(M)), bold(upright(T)); 0, bold(upright(N)))
  "and" mat(bold(upright(M)), bold(upright(T))'; 0, bold(upright(N)))
$
are a pair of $R$-representations of $Lambda$. The matrix analogue of
equivalence of extensions is as follows: the two matrix representations above
are called _equivalent_#footnote[
  Some authors refer to this as “strong equivalence”.
] if there exists a matrix $bold(upright(C))$ with entries in $R$, such that
$
  mat(
    bold(upright(M))(lambda), bold(upright(T))'(lambda);
    0, bold(upright(N))(lambda)
  )=
  mat(bold(upright(I)), bold(upright(C)); 0, bold(upright(I)))^(-1)
  mat(
    bold(upright(M))(lambda), bold(upright(T))(lambda);
    0, bold(upright(N))(lambda)
  )mat(bold(upright(I)), bold(upright(C)); 0, bold(upright(I)))
$
for each $lambda in Lambda$. This gives
$
  bold(upright(T))'(lambda)=bold(upright(T))(lambda)
  +bold(upright(M))(lambda)bold(upright(C))-bold(upright(C))
  bold(upright(N))(lambda)
  "for all" lambda in Lambda,
$ <eq:equivalent-binding-systems>
so $bold(upright(T))'-bold(upright(T))$ is an inner derivation.

#example[
  Let $Lambda=ZZ G$, $A=QQ G$, where
  $ G=chevron.l a,b:a^4=1,b^2=1,b a b^(-1)=a^(-1) chevron.r, $
  the dihedral group of order $8$. Let $bold(upright(M))$ be the
  $ZZ$-representation of $G$ defined by
  $
    bold(upright(M))(a)=mat(0, 1; -1, 0),
    bold(upright(M))(b)=mat(0, 1; 1, 0).
  $
  Thus, $bold(upright(M))$ is the representation $bold(upright(M))_1$ of
  Example~@exm:dihedral-integral-inequivalent-representations. Let
  $bold(upright(N))$ denote the representation $bold(upright(M))_2$ of that
  example, so we have
  $
    bold(upright(N))(a)=mat(0, 1; -1, 0),
    bold(upright(N))(b)=mat(1, 0; 0, -1).
  $
  Let $M=ZZ plus.o ZZ$ be the $ZZ G$-module affording $bold(upright(M))$, and
  let $N=ZZ plus.o ZZ$ afford $bold(upright(N))$. We
  #source(570)
  shall calculate $op("Ext")_(ZZ G)^1 lr((N,M))$ by using
  @eq:extensions-integrality-quotient and @eq:extension-integrality-generators.
  We have
  $
    Omega & ={bold(upright(X)) in M_2 lr((QQ)):
              bold(upright(M))(g)bold(upright(X))-bold(upright(X))
              bold(upright(N))(g) in M_2 lr((ZZ))
              "for" g=a,b} \
          & ={mat(alpha, beta; gamma, delta) in M_2 lr((QQ)):
              alpha-gamma,delta-alpha,beta+delta in ZZ}.
  $
  Next, to find $Omega_0$ we note first that
  $
    Hom_(QQ G) lr((QQ N,QQ M)) & ={bold(upright(X)) in M_2 lr((QQ)):
                                   bold(upright(M))(g)bold(upright(X))
                                   -bold(upright(X)) bold(upright(N))(g)=0
                                   "for" g=a,b} \
                               & ={mat(alpha, beta; gamma, delta) in M_2
                                   lr((QQ)):
                                   alpha-gamma=delta-alpha=beta+gamma=0} \
                               & ={alpha bold(upright(P)):alpha in QQ},"where"
                                 bold(upright(P))=mat(
                                   1, -1;
                                   1, 1
                                 ).
  $
  Thus
  $ Omega_0=M_2 lr((ZZ))+{alpha bold(upright(P)):alpha in QQ}. $
  We may now calculate $Omega slash Omega_0$; let
  $bold(upright(X))=mat(alpha, beta; gamma, delta) in Omega$. Then working
  modulo $Omega_0$, we have
  $
    bold(upright(X)) equiv mat(alpha, beta; gamma, delta)-alpha bold(upright(P))
    =mat(0, alpha+beta; gamma-alpha, delta-alpha) equiv 0,
  $
  the last step because $alpha-gamma$, $delta-alpha$ and $alpha+beta$ all lie in
  $ZZ$. This shows that
  $ op("Ext")_(ZZ G)^1 lr((N,M))=0. $
  On the other hand, we may calculate $op("Ext")_(ZZ G)^1 lr((M,M))$ in the same
  way, obtaining for this case
  $
    Omega={mat(alpha, beta; gamma, delta) in M_2 lr((QQ)):
      beta plus.minus gamma,alpha-delta in ZZ}, \
    Omega_0=M_2 lr((ZZ))+{alpha bold(upright(I)):alpha in QQ}.
  $
  If $bold(upright(X))=mat(alpha, beta; gamma, delta) in Omega$, then mod
  $Omega_0$ we obtain
  $
    bold(upright(X)) equiv mat(alpha-delta, beta; gamma, 0) equiv mat(
      0, beta;
      gamma, 0
    ),
  $
  and $beta plus.minus gamma in ZZ$. Hence $Omega slash Omega_0$ is a
  $ZZ$-module with $2$ elements, generated by
  $ bold(upright(X))=mat(delim: "[", 0, -1/2; 1/2, 0). $
  #source(571)
  The derivation $bold(upright(T))$ corresponding to $bold(upright(X))$ is given
  by
  $
    bold(upright(T))(g)=bold(upright(M))(g)bold(upright(X))-bold(upright(X))
    bold(upright(M))(g),g in G,
  $
  and we obtain
  $
    bold(upright(T))(a)=mat(0, 0; 0, 0),
    bold(upright(T))(b)=mat(1, 0; 0, -1).
  $
  Thus
  $
    g mapsto mat(
      bold(upright(M))(g), bold(upright(T))(g);
      0, bold(upright(M))(g)
    ),g in G,
  $
  gives a $ZZ$-representation of $G$ which is a nonsplit extension of the factor
  representation $bold(upright(M))$ (lower right hand corner) by the
  sub-representation $bold(upright(M))$ (upper left hand corner).
] <exm:dihedral-lattice-extensions>

(For another matrix calculation, see
Exercise~@exc:cyclic-disjoint-block-extension.)

A further comment on matrix representations may be useful. Let $Lambda$ be an
$R$-order in a f.d. $K$-algebra $A$, where $R$ is a P.I.D. with quotient field
$K$. Let $M$ be a $Lambda$-lattice, and let
$ M=M_0 supset M_1 supset ... supset M_n=0 $
be a chain of sublattices, such that each $M_(i-1) slash M_i$ is a
$Lambda$-lattice (see Exercise~@exc:order-lattice-composition-series). Choose an
$R$-basis for $M$ so that the first batch of elements form a basis for
$M_(n-1)$, the first two batches a basis for $M_(n-2)$, and so on. Relative to
this basis, $M$ affords a matrix representation
$
  bold(upright(M))(lambda)=mat(
    delim: "[",
    bold(upright(U))_11(lambda), bold(upright(U))_12(lambda), dots,
    bold(upright(U))_(1 n)(lambda);
    0, bold(upright(U))_22(lambda), dots, bold(upright(U))_(2 n)(lambda);
    dots, dots, dots, dots;
    0, 0, dots, bold(upright(U))_(n n)(lambda)
  ),lambda in Lambda.
$
<eq:successive-extension-matrix>
Here, $bold(upright(U))_(i i)$ is the $R$-representation of $Lambda$ afforded by
the $R$-composition factor#idx("R-composition factors")
$M_(n-i) slash M_(n-i+1)$ of $M$. For each $i$, $bold(upright(U))_(i,i+1)$ is a
derivation of $Lambda$ relative to the pair $bold(upright(U))_(i i)$,
$bold(upright(U))_(i+1,i+1)$. However, $bold(upright(U))_13$,
$bold(upright(U))_14$, $...$, $bold(upright(U))_24$, $...$, are not derivations
(generally speaking), and their calculation is precisely the problem of finding
successive extensions of modules. There is no neat solution to this problem in
most cases. (See Exercise~@exc:successive-block-derivation.)

We shall conclude this section with an example in which we use the homological
algebra approach in @eq:extension-projective-presentation to calculate Ext of a
pair of $ZZ G$-lattices, where $G$ is a finite cyclic group of order $g$. The
result plays a key role in the later discussion of integral group
representations. For each positive integer $n$,
#source(572)
let $omega_n$ be a primitive $n$-th root of $1$ over $QQ$. Then (see
@prop:cyclotomic-integers) we put
$ K_n=QQ(omega_n),R_n=ZZ[omega_n]="alg. int." lr({K_n}). $
Now $"min.pol."_QQ lr((omega_n))=Phi_n (x)$, the cyclotomic polynomial of order
$n$ and degree $phi(n)$, where $phi$ is the Euler $phi$-function. Hence we have
$R_n tilde.equiv ZZ[x] slash (Phi_n (x))$. We shall identify the group ring
$ZZ G$ with the ring
$ Lambda=ZZ[x] slash (x^g-1), $
by identifying $x$ with a generator of $G$. Since
$ x^g-1=product_(n divides g) Phi_n (x), $
it follows that there is a ring isomorphism
$ R_n tilde.equiv Lambda slash Phi_n (x)Lambda "whenever" n "divides" g. $
<eq:cyclotomic-group-lattice>
For each divisor $n$ of $g$, the surjection $Lambda -> R_n$ permits us to view
every $R_n$-module as a $Lambda$-module. In particular, $R_n$ is itself a left
$Lambda$-lattice. Our aim here is to calculate
$op("Ext")_(ZZ G)^1 lr((R_n,R_m))$ when $m$ and $n$ divide $g$. The result
stated below is due to Diederichsen~@bib:Diederichsen1940; we shall give the
simplified proof by Reiner~@bib:Reiner1979b. Calculations of this nature may
also be found in Berman-Gudivok~@bib:Berman1964a; see also
Berman~@bib:Berman1964.

#theorem[
  Let $G$ be a cyclic group of order $g$, and let $m$ and $n$ be divisors of
  $g$. Let $R_n="alg. int." lr({K_n})$, where $K_n$ is the cyclotomic field
  $QQ(omega_n)$, with $omega_n$ a primitive $n$-th root of $1$ over $QQ$. Define
  $R_m$ analogously, and view $R_m$ and $R_n$ as $ZZ G$-lattices. Then
  #enum(
    numbering: "(i)",
    [$op("Ext")_(ZZ G)^1 lr((R_n,R_m))=0$ unless $m slash n=p^t$ for some prime
      $p$ and some nonzero integer $t$, possibly negative.],
    [If $m slash n=p^t$ for some prime $p$ and some nonzero $t in ZZ$, then
      there is a $ZZ G$-isomorphism#footnote[
        Diederichsen proved that $op("Ext")(R_n, R_m)$ is isomorphic to the
        direct sum of $phi(l)$ copies of $ZZ slash p ZZ$, where $l=min(m, n)$.
        The stated isomorphism is a stronger result, and implies that of
        Diederichsen, since $R_l$ has a free $ZZ$-basis of $phi(l)$ elements.
      ]
      $
        op("Ext")_(ZZ G)^1 lr((R_n,R_m)) tilde.equiv R_l slash p R_l,
        "where" l=min(m, n).
      $],
  )
] <th:diederichsen-cyclotomic-extensions>
#idx("Diederichsen's Theorem", target: [@th:diederichsen-cyclotomic-extensions])

#proof[
  _Step 1._ Let $Lambda$ be an arbitrary ring, and let $a in Lambda$,
  $overline(Lambda)=Lambda slash Lambda a$, so $overline(Lambda)$ is a left
  $Lambda$-module. Put
  $ J="ann"_Lambda (a)={b in Lambda:b a=0}. $
  #source(573)
  For each left $Lambda$-module $M$, let
  $ M'={m in M:J m=0}. $
  Then we have
  $ op("Ext")_Lambda^1 lr((overline(Lambda),M)) tilde.equiv M' slash a M, $
  <eq:principal-quotient-extensions>
  by Exercise~@exc:principal-quotient-ext.

  _Step 2._ Now let $Lambda=ZZ G$, where $G$ is cyclic of order $g$, and let
  $n divides g$. We show at once that
  $ op("Ext")_(ZZ G)^1 lr((R_n,R_n))=0. $
  Let $Phi_n$ be the cyclotomic polynomial of order $n$, where we write $Phi_n$
  instead of $Phi_n (x)$ for convenience. Consider any $ZZ G$-exact sequence
  $ 0 -> R_n -> M -> R_n -> 0 $
  in which $M$ is a $ZZ G$-module. Then $Phi_n dot M subset.eq R_n$, so
  $Phi_n^2 dot M=0$; clearly also $(x^g-1)M=0$. Since $Phi_n$ is irreducible and
  $x^g-1$ has no repeated factors, their G.C.D. in $QQ[x]$ is $Phi_n$. It
  follows that there exists polynomials $p(x),q(x) in ZZ[x]$, and a nonzero
  $alpha in ZZ$, such that
  $ alpha Phi_n=p(x)Phi_n^2+q(x)(x^g-1). $
  Then $alpha Phi_n M=0$, and so $Phi_n M=0$ because $M$ is $ZZ$-torsionfree.
  Therefore $M$ may be viewed as an $R_n$-module. But then the sequence is
  $R_n$-split by @prop:projective-module-criteria, and so the sequence is also
  $ZZ G$-split. This completes the proof that
  $op("Ext")_(ZZ G)^1 lr((R_n,R_n))=0$.

  _Step 3._ We assume that $m!=n$ from now on, and write Ext in place of
  $op("Ext")_(ZZ G)^1$ for brevity. Let $Psi_n (x) in ZZ[x]$ be defined by the
  equation $Phi_n Psi_n=x^g-1$. Then $Psi_n dot ZZ G$ is the annihilator of
  $Phi_n$ in $ZZ G$. Since $Phi_m$ is a factor of $Psi_n$, it follows that
  $Psi_n dot R_m=0$. Applying @eq:principal-quotient-extensions with
  $Lambda=Lambda$, $a=Phi_n$, $M=R_m$, we obtain
  $ op("Ext")(R_n, R_m) tilde.equiv R_m slash Phi_n (x)R_m. $
  Using @eq:cyclotomic-group-lattice, this becomes
  $ op("Ext")(R_n, R_m) tilde.equiv ZZ[x] slash (Phi_n,Phi_m) "if" m!=n. $
  <eq:cyclotomic-extension-polynomial-quotient>
  This implies that $op("Ext")(R_n, R_m) tilde.equiv op("Ext")(R_m, R_n)$. We
  could have predicted this in advance by a general argument about
  contragredients of $ZZ G$-lattices (see
  Exercise~@exc:contragredient-exact-split).

  #source(574)
  It is rather complicated to compute $op("Ext")(R_n, R_m)$ directly from
  @eq:cyclotomic-extension-polynomial-quotient, and indeed Diederichsen's proof
  involves intricate (though elementary) manipulations with roots of unity.
  Instead, we use @th:extension-localization-group-order to express
  $op("Ext")(R_n, R_m)$ as a direct sum of its $p$-primary components, with $p$
  ranging over all rational primes dividing $g$. We have
  $
    op("Ext")_(ZZ G)^1 lr((R_n,R_m)) tilde.equiv
    plus.o.big_(p divides g) op("Ext")_(ZZ_p G)^1 lr(((R_n)_p,(R_m)_p)),
  $
  <eq:cyclotomic-extension-primary-components>
  where the subscript $p$ denotes localization at $p$. From
  @eq:cyclotomic-extension-polynomial-quotient we obtain
  $
    op("Ext")_(ZZ_p G)^1 lr(((R_n)_p,(R_m)_p)) tilde.equiv
    ZZ_p[x] slash (Phi_n,Phi_m).
  $ <eq:cyclotomic-extension-local-quotient>

  Before proceeding to the next step, we make some comments about the
  isomorphisms occurring in @th:diederichsen-cyclotomic-extensions(ii),
  @eq:cyclotomic-extension-polynomial-quotient–@eq:cyclotomic-extension-local-quotient.
  Since the ring $ZZ G$ is commutative, the remarks following
  @rem:ext-long-exact-sequence show that each of the modules
  $op("Ext")_(ZZ G)^1$, $Hom_(ZZ G)$, etc., may be viewed in a natural manner as
  a $ZZ G$-module. (An analogous statement holds with $ZZ$ replaced by $ZZ_p$.)
  But then it is easily verified that
  @th:diederichsen-cyclotomic-extensions(ii),
  @eq:cyclotomic-extension-polynomial-quotient and
  @eq:cyclotomic-extension-primary-components give $ZZ G$-isomorphisms, while
  @eq:cyclotomic-extension-local-quotient is a $ZZ_p G$-isomorphism. This fact
  will play a crucial role in Step 5 below.

  _Step 4._ Keep $p$ fixed, and write $m=p^a r$, $n=p^b s$, where
  $p divides.not r s$. Let $overline(ZZ)=ZZ slash p ZZ$, and let bars denote
  images mod $p$. By @eq:prime-power-cyclotomic-reduction we have
  $
    overline(Phi)_m=(overline(Phi)_r)^(phi(p^a)),
    overline(Phi)_n=(overline(Phi)_s)^(phi(p^b)) "in" overline(ZZ)[x].
  $
  <eq:cyclotomic-reduction-prime-parts>
  Using this fact, we now show that for $m!=n$,
  $
    op("Ext")_(ZZ_p G)^1 lr(((R_n)_p,(R_m)_p))=0
    "except when" m slash n=p^t "for some nonzero" t in ZZ.
  $
  <eq:cyclotomic-local-ext-vanishing>
  If $m slash n$ is not a power of $p$, then $r!=s$. Hence
  $(overline(Phi)_r,overline(Phi)_s)=1$ in $overline(ZZ)[x]$, since every zero
  of $overline(Phi)_r$ is a primitive $r$-th root of $1$ over $overline(ZZ)$,
  while every zero of $overline(Phi)_s$ is a primitive $s$-th root of $1$ (see
  @eq:cyclotomic-polynomial-roots). Hence $(overline(Phi)_m,overline(Phi)_n)=1$
  in $overline(ZZ)[x]$ by @eq:cyclotomic-reduction-prime-parts. Now let $Omega$
  be the _resultant_#idx("resultant") of $Phi_m$ and $Phi_n$ in $ZZ[x]$; by
  definition,
  $ Omega=product_(j,k)(alpha_j-beta_k) in ZZ, $
  where $alpha_j$ ranges over the zeros of $Phi_m$, and $beta_k$ ranges over the
  zeros of $Phi_n$. Since $Phi_m$ and $Phi_n$ are monic polynomials in $ZZ[x]$,
  each $alpha_j$ and $beta_k$ is an algebraic integer, whence so is $Omega$. On
  the other hand, $Omega$ is unchanged by all automorphisms in the Galois group
  of the splitting field of $Phi_m dot Phi_n$ over $QQ$, and therefore
  $Omega in QQ$. Thus $Omega in ZZ$ as claimed above.

  #source(575)
  Let bars denote images in the splitting field of
  $overline(Phi)_m overline(Phi)_n$ over $overline(ZZ)$; then we have
  $
    overline(Omega)=product_(j,k)(overline(alpha)_j-overline(beta)_k) in
    overline(ZZ).
  $
  Since $(overline(Phi)_m,overline(Phi)_n)=1$, each of the above factors
  $overline(alpha)_j-overline(beta)_k$ is nonzero, so $overline(Omega)!=0$.
  Therefore $Omega$ is a unit in the localization $ZZ_p$. On the other hand (see
  van der Waerden~@bib:VanDerWaerden1964), the resultant $Omega$ lies in the
  ideal $(Phi_m,Phi_n)$ of $ZZ[x]$. Hence in $ZZ_p[x]$ we have
  $(Phi_m,Phi_n)=ZZ_p[x]$, and @eq:cyclotomic-local-ext-vanishing is then an
  immediate consequence of @eq:cyclotomic-extension-local-quotient.

  _Step 5._ Suppose finally that $m!=n$ but $m slash n=p^t$ for some nonzero
  $t in ZZ$. Then we have $m=p^a s$, $n=p^b s$, where $p divides.not s$. By
  @eq:cyclotomic-extension-polynomial-quotient, there is no loss of generality
  in assuming that $m<n$, so $a<b$. We show first that $p$ lies in the ideal
  $(Phi_n,Phi_m)$ of $ZZ[x]$. Put
  $ y=x^(s p^(b-1)) in G. $
  Since $x$ acts as $omega_m$ on $R_m$, it follows that $y$ acts as $1$ on
  $R_m$. On the other hand, $x$ acts as $omega_n$ on $R_n$, so $y$ acts on $R_n$
  as multiplication by a primitive $p$-th root of $1$. Therefore
  $1+y+y^2+...+y^(p-1)$ annihilates $R_n$.

  Now $op("Ext")_(ZZ G)^1 lr((R_n,R_m))$ is a $ZZ G$-bimodule, since $ZZ G$ is
  commutative (see the last paragraph of Step 3). The right action of $ZZ G$ on
  $op("Ext")(R_n, R_m)$ arises from the left action of $ZZ G$ on the first
  variable $R_n$, since Ext is contravariant in the first variable (see
  Remark~@rem:ext-properties(iv)). Likewise, the left action of $ZZ G$ on
  $op("Ext")(R_n, R_m)$ arises from the left action of $ZZ G$ on the second
  variable $R_m$, since Ext is covariant in the second variable. Further, the
  two actions of $ZZ G$ on Ext are identical: $y xi=xi y$ for all $y in ZZ G$,
  $xi in op("Ext")$. This is clear from the fact that for any pair of
  $ZZ G$-modules $M$ and $N$, the two actions of $ZZ G$ on
  $Hom_(ZZ G) lr((M,N))$ coincide.

  By the preceding remarks, we see that $1+y+...+y^(p-1)$ acts on
  $op("Ext")(R_n, R_m)$ as the zero map (from the right), and as multiplication
  by $p$ (from the left). Therefore $p dot op("Ext")(R_n, R_m)=0$, and so
  $p in (Phi_n,Phi_m)$ by @eq:cyclotomic-extension-polynomial-quotient. But then
  $
    op("Ext")(R_n, R_m) tilde.equiv ZZ[x] slash (Phi_n,Phi_m,p)
    tilde.equiv overline(ZZ)[x] slash (overline(Phi)_n,overline(Phi)_m).
  $
  But when $m<n$ and $r=s$, $overline(Phi)_n$ is a power of $overline(Phi)_m$ by
  @eq:cyclotomic-reduction-prime-parts. Thus we obtain
  $
    op("Ext")(R_n, R_m) tilde.equiv overline(ZZ)[x] slash (overline(Phi)_m)
    tilde.equiv ZZ[x] slash (p,Phi_m (x)) tilde.equiv R_m slash p R_m.
  $
  The same argument holds with $ZZ$ replaced by $ZZ_p$, since
  $ZZ_p slash p ZZ_p tilde.equiv overline(ZZ)$. We have thus established
  assertion (ii) of our theorem, as well as the fact that
  $
    op("Ext")_(ZZ_p G)^1 lr(((R_n)_p,(R_m)_p)) tilde.equiv
    R_l slash p R_l,l=min(m, n),
  $
  if $m slash n=p^t$ for nonzero $t in ZZ$.

  #source(576)
  We are now ready to finish the proof of our theorem. Step 2 shows that
  $op("Ext")(R_n, R_n)=0$, so now let $m!=n$. We consider the quotients
  $m slash n$ and $n slash m$; if neither one is a prime power, then
  $op("Ext")(R_n, R_m)=0$ by @eq:cyclotomic-extension-primary-components and
  @eq:cyclotomic-local-ext-vanishing. On the other hand, if $m slash n=p^t$ for
  some prime $p$ and some nonzero $t in ZZ$, then we have already proved the
  desired result (ii) in Step 5. This completes the proof of the theorem.
]

For some other calculations of Ext, see
§@ss:dihedral-metacyclic-integral-representations.

#exercises-heading

Throughout these exercises, $R$ is a commutative ring and $G$ an arbitrary
group.

#exercise[
  Let $M$ and $N$ be $R G$-modules. Make $Hom_R lr((N,M))$ into a left
  $R G$-module by defining
  $ x * f=x f x^(-1) "for all" x in G,f in Hom_R lr((N,M)), $
  and extending the action to all of $R G$ by linearity. Show that the
  $G$-trivial submodule of $Hom_R lr((N,M))$ is precisely $Hom_(R G) lr((N,M))$.
  #hint([@exc:hom-conjugation-invariants])[
    See the proof of @prop:invariants-induction-hom.
  ]
] <exc:hom-conjugation-invariants>

#exercise[
  Let $Lambda=R G$, and let $T$ be a $(Lambda,Lambda)$-bimodule centralized by
  $R$. Turn $T$ into a left $Lambda$-module, denoted by $T'$, by specifying that
  for $x in G$ and $t in T$,
  $ x * t ("computed in" T')=x t x^(-1) ("computed in" T), $
  and extending to a $Lambda$-action on $T'$ by linearity. Show that each
  derivation $F:Lambda -> T$ yields a derivation $F':Lambda -> T'$ (in the sense
  of @eq:derivation-condition), by setting
  $ F'_x=F_x dot x^(-1),x in G, $
  and extending by linearity. Prove that the map $F mapsto F'$ gives an
  $R$-isomorphism $"Der"(Lambda,T) tilde.equiv "Der"(Lambda,T')$, and that
  $ H^1 lr((R G,T)) tilde.equiv H^1 lr((G,T')). $
] <exc:bimodule-group-derivation-comparison>

#exercise[
  When $G$ is a finite group, deduce
  @th:group-order-annihilates-bimodule-cohomology from
  @prop:group-order-annihilates-tate by using the preceding exercise.
] <exc:group-cohomology-annihilation-derivation>

#exercise[
  Let $M$ be an $R G$-module whose $G$-trivial submodule is $0$. Show that if
  $G$ is a finite group, then
  $ lr((sum_(x in G) x))M=0. $
] <exc:norm-zero-without-invariants>

#exercise[
  (Diederichsen~@bib:Diederichsen1940). Let $H triangle.l G$, where $G$ is a
  finite group. Let $N$ be an $R G$-lattice on which $H$ acts trivially. Let $M$
  be any $R G$-module whose $H$-trivial submodule
  #source(577)
  $"inv"_H M$ is $0$ (see §@ss:contragredient-modules). Show that
  $ |H| dot op("Ext")_(R G)^1 lr((N,M))=0 $
  if $R$ is an integral domain of characteristic $0$.

  #hint([@exc:diederichsen-extension-annihilator])[
    Use @prop:extensions-bimodule-cohomology, and let $F:G -> Hom_R lr((N,M))$
    be a derivation. We must prove that $|H| F$ is inner. Deduce from
    @eq:group-ring-derivation that #named-equation(name: [(\*)])[
      $ F_x=F_(x y)(x y)^(-1)x-x F_y y^(-1),forall x,y in G. $
    ] <eq:subgroup-derivation-average-identity>
    Sum over $x in H$; use Exercise~@exc:norm-zero-without-invariants, and the
    hypothesis that $N$ is $H$-trivial, to obtain
    $
      sum_(x in H) F_x x^(-1)=sum_(z in H y) F_z z^(-1)=T
      ("say"),"for all" y in G.
    $
    Thus $T$ is independent of $y$, and
    $ T=sum_(z in y H) F_z z^(-1) "for all" y in G, $
    since $y H=H y$. Keep $x in G$ fixed, and sum
    @eq:subgroup-derivation-average-identity over $y in H$. This gives
    $
      |H| dot F_x=sum_(y in H) F_(x y)(x y)^(-1)x
      -x sum_(y in H) F_y y^(-1)=T x-x T,
    $
    so $|H| dot F$ is an inner derivation.

    A fancier proof uses the _Hochschild-Serre-Lyndon spectral sequence_, #idx(
      "Hochschild-Serre-Lyndon spectral sequence",
    )#idx("spectral sequence") which we now describe. Let $H triangle.l G$,
    $overline(G)=G slash H$, and let $X$ be any $R G$-module. Then $"inv"_H X$
    is naturally an $R[overline(G)]$-module. The low-degree part of the spectral
    sequence gives the following five-term exact sequence (see
    Babakhanian~@bib:Babakhanian1972, p. 193 or Rotman~@bib:Rotman1979, p. 355):
    $
      0 -> H^1 lr((overline(G),"inv"_H X)) -> H^1 lr((G,X))
      -> "inv"_(overline(G)) H^1 lr((H,X)) ->
      H^2 lr((overline(G),"inv"_H X)) -> H^2 lr((G,X)).
    $
    (There is a natural action of $overline(G)$ on $H^1 lr((H,X))$, so
    $"inv"_(overline(G)) H^1 lr((H,X))$ is meaningful.)

    If now $"inv"_H X=0$, then $H^1 lr((G,X))$ is embedded in the
    $overline(G)$-trivial submodule of $H^1 lr((H,X))$, whence
    $ |H| H^1 lr((G,X))=0. $
    In the case above, take $X=Hom_R lr((N,M))$, so
    $"inv"_H X=Hom_(R H) lr((N,M))$. Show that the latter is $0$ because $N$ is
    $H$-trivial, while $"inv"_H M=0$. Thus $|H| H^1 lr((G,Hom_R lr((N,M))))=0$,
    and now use Exercise~@exc:bimodule-group-derivation-comparison and
    @prop:extensions-bimodule-cohomology.
  ]
] <exc:diederichsen-extension-annihilator>

#exercise[
  Let $G$ be a finite group of order $n$, acting trivially on $ZZ$. Put
  $ sigma=sum_(x in G) x in ZZ G, $
  and let $J=ZZ G slash ZZ sigma=$ left $ZZ G$-lattice. Prove that
  $ op("Ext")_(ZZ G)^1 lr((J,ZZ)) tilde.equiv ZZ slash n ZZ. $
  #source(578)
  #hint([@exc:augmentation-quotient-extension])[
    $0 -> ZZ arrow.r^sigma ZZ G -> J -> 0$ is $ZZ G$-exact. Now use
    @eq:extension-projective-presentation.
  ]
] <exc:augmentation-quotient-extension>

#exercise[
  Let $Lambda$ be an arbitrary ring, let $a in Lambda$, and set
  $overline(Lambda)=Lambda slash Lambda a=$ left $Lambda$-module. Put
  $ T="ann"_Lambda a={b in Lambda:b a=0}. $
  For each left $Lambda$-module $M$, define
  $ M'={m in M:T dot m=0}. $
  Prove that
  $ op("Ext")_Lambda^1 lr((overline(Lambda),M)) tilde.equiv M' slash a M $
  as additive groups.

  #hint([@exc:principal-quotient-ext])[
    From the exact sequence $0 -> Lambda a arrow.r^i Lambda -> overline(Lambda)
    -> 0$, where $i$ is the inclusion map, we obtain
    $
      op("Ext")^1 lr((overline(Lambda),M)) tilde.equiv
      Hom(Lambda a, M) slash i^* lr({Hom(Lambda, M)}),
    $
    where we omit the subscript $Lambda$ from Ext and Hom for convenience. Each
    $f in Hom(Lambda a, M)$ is determined by the image $f(a) in M$, which may be
    chosen arbitrarily in $M$, subject to the condition that
    $ ("ann"_Lambda a) dot f(a)=0. $
    Thus $Hom(Lambda a, M) tilde.equiv M'$. Since $Hom(Lambda, M) tilde.equiv M$
    by @eq:hom-regular-module, we obtain
    $ i^* lr({Hom(Lambda, M)}) tilde.equiv a M, $
    and the result is proved.
  ]
] <exc:principal-quotient-ext>

#exercise[
  Let $G$ be a finite group of order $n$, $R$ an integral domain of
  characteristic $0$, and let $M$ and $N$ be $R G$-lattices. Let
  $F:G -> Hom_R lr((N,M))$ be a derivation such that $F=0$ (mod $n$), that is,
  $ F_x in n dot Hom_R lr((N,M)) "for all" x in G. $
  Show that $F$ is an inner derivation.
  #hint([@exc:divisible-derivation-inner])[
    Put $F_1=n^(-1) F$, and show that $F_1$ is a derivation. Then use
    @th:group-order-annihilates-bimodule-cohomology.
  ]
] <exc:divisible-derivation-inner>

#exercise[
  In terms of the notation @eq:successive-extension-matrix, show that
  $ mat(delim: "[", bold(upright(U))_13; bold(upright(U))_23) $
  is a derivation of $Lambda$ relative to the pair
  $
    mat(
      delim: "[", bold(upright(U))_11, bold(upright(U))_12;
      0, bold(upright(U))_22
    ), mat(delim: "[", bold(upright(U))_33).
  $
  Generalize!
] <exc:successive-block-derivation>

#source(579)
#exercise[
  Let $G=chevron.l x chevron.r$ be a cyclic group of order $g$, and $K$ any
  field. Let $M$ and $N$ be f.g. left $K G$-modules such that
  $Hom_(K G) lr((N,M))=0$, and let $m=dim_K M$, $n=dim_K N$. Suppose that $M$
  and $N$ afford the matrix representations $bold(upright(M))$ and
  $bold(upright(N))$, respectively. Show that for every $m times n$ matrix
  $bold(upright(T))$ over $K$, the map
  $
    x mapsto mat(
      bold(upright(M))(x), bold(upright(T));
      0, bold(upright(N))(x)
    )
  $
  defines a $K$-representation of $G$.

  #hint([@exc:cyclic-disjoint-block-extension])[
    It suffices to show that
    $bold(upright(T))=bold(upright(M))(x)bold(upright(W))-bold(upright(W))
    bold(upright(N))(x)$
    for some $bold(upright(W)) in K^(m times n)$, since then
    $
      mat(bold(upright(M))(x), bold(upright(T)); 0, bold(upright(N))(x))=
      mat(bold(upright(I)), bold(upright(W)); 0, bold(upright(I)))^(-1)
      mat(bold(upright(M))(x), 0; 0, bold(upright(N))(x))mat(
        bold(upright(I)),
        bold(upright(W)); 0, bold(upright(I))
      ).
    $
    Consider the $K$-endomorphism $phi$ of $K^(m times n)$ defined by
    $
      phi(bold(upright(W)))=bold(upright(M))(x)bold(upright(W))-bold(upright(W))
      bold(upright(N))(x),bold(upright(W)) in K^(m times n).
    $
    Then $phi(bold(upright(W)))=0$ if and only if
    $bold(upright(W)) in Hom_(K G) lr((N,M))$, whence $phi$ is an injection.
    Hence $phi$ is surjective, so every $bold(upright(T)) in K^(m times n)$ lies
    in $"im"(phi)$.
  ]
] <exc:cyclic-disjoint-block-extension>

#exercise[
  Let $Lambda$ be an $R$-order in a $K$-algebra $A$, and let $U,V$ be f.g. left
  $A$-modules. Let $e in Lambda$ be a central idempotent of $A$ such that $e$
  acts as $1$ on each composition factor of $U$, and $e$ annihilates each
  composition factor of $V$. Show that $op("Ext")_Lambda^1 lr((M,N))=0$ for each
  pair of $Lambda$-lattices $M,N$ such that $K M=U$, $K N=V$.

  #hint([@exc:central-idempotent-separates-extensions])[
    By Exercise~@exc:idempotent-annihilates-composition-factors, $e V=0$ and
    $(e-1)U=0$. Thus $e$ acts as $1$ on $M$ and as $0$ on $N$. Since $e$ is
    central in $Lambda$, $e$ acts on $op("Ext")_Lambda^1 lr((M,N))$ by its
    action on $M$ or on $N$, and these two actions of $e$ are identical. Thus
    $op("Ext")_Lambda^1 lr((M,N))=0$.
  ]
] <exc:central-idempotent-separates-extensions>

#exercise[
  Let $E=G times H$ be a direct product of finite groups, $R$ a Dedekind domain,
  and $T$ a nonzero $R H$-lattice. Given any $R G$-lattice $M$, we may form the
  outer tensor product $M \# T=M times.o_R T$, an $R E$-lattice. Show that for
  any $R G$-lattices $M$ and $N$, there is a monomorphism
  $ op("Ext")_(R G)^1 lr((M,N)) -> op("Ext")_(R E)^1 lr((M \# T,N \# T)), $
  obtained by applying $* \# T$ to exact sequences of $R G$-lattices.

  #hint([@exc:outer-tensor-extension-injection])[
    The result is due to Reiner~@bib:Reiner1967. It suffices to prove the result
    with $R_P$ in place of $R$, where $P$ ranges over the maximal ideals of $R$.
    Changing notation, let $R$ be a P.I.D. and let $T=plus.o.big_1^n R t_i$.
    Given an exact sequence of $R G$-lattices $0 -> N -> X arrow.r^mu M -> 0$,
    suppose that
    $ 0 -> N \# T -> X \# T arrow.r^(mu times.o 1) M \# T -> 0 $
    is $R E$-split, and let $rho:M \# T -> X \# T$ split $mu times.o 1$. Write
    $
      rho(m times.o t_i)=sum_(j=1)^n f_(j i)(m) times.o t_j,
      m in M,1<=i<=n,
    $
    #source(580)
    where each $f_(i j) in Hom_(R G) lr((M,X))$. Then for each $i$,
    $(mu times.o 1)rho(m times.o t_i)=m times.o t_i$ implies that
    $mu f_(i i)=1_M$, so $f_(i i)$ splits $mu$.
  ]
] <exc:outer-tensor-extension-injection>

#exercise[
  Let $R$ be a Dedekind domain, $G_1$ and $G_2$ arbitrary groups, and let $M_i$
  and $M'_i$ be $R G_i$-lattices, $i=1,2$. Set $Gamma_i=R G_i$, $Gamma=R G$,
  where $G=G_1 times G_2$. Prove that
  $
    Hom_Gamma lr((M_1 \# M_2,M'_1 \# M'_2))
    tilde.equiv Hom_(Gamma_1) lr((M_1,M'_1)) times.o_R
    Hom_(Gamma_2) lr((M_2,M'_2)).
  $
  If $G_1$ and $G_2$ are finite, put
  $ E_i^r=op("Ext")_(Gamma_i)^r lr((M_i,M'_i)), i=1,2, r>=0. $
  Show that there is a natural short exact sequence of $R$-modules
  $
    0 -> (E_1^0 times.o_R E_2^1) plus.o (E_1^1 times.o_R E_2^0)
    -> op("Ext")_Gamma^1 lr((M_1 \# M_2,M'_1 \# M'_2)) \
    -> op("Tor")_1^R lr((E_1^1,E_2^1)) -> 0,
  $
  which splits noncanonically. Compare Jones~@bib:Jones1963b.

  #hint([@exc:outer-tensor-ext-kunneth])[
    For the Hom formula, put $U_i=Hom_R lr((M_i,M'_i))$. Finite projectivity
    gives
    $
      Hom_R lr((M_1 times.o_R M_2,M'_1 times.o_R M'_2))
      tilde.equiv U_1 times.o_R U_2.
    $
    Taking $G_1$-invariants commutes with tensoring by the finite projective
    module $U_2$. The invariant submodule $U_1^(G_1)$ is finite torsionfree,
    hence projective over $R$, so taking $G_2$-invariants gives the asserted Hom
    formula, without any finiteness assumption on the groups.

    Now assume that both groups are finite, and let $X^i$ be a projective
    resolution of $M_i$ with finitely generated free $Gamma_i$-terms. Such
    resolutions exist since $Gamma_i$ is noetherian. Let $times.o$ denote
    $times.o_R$. The total complex $X^1 \# X^2$, with
    $ (X^1 \# X^2)_m=sum_(j+k=m) X_j^1 \# X_k^2, $
    has differential $d_1 times.o 1+(-1)^j times.o d_2$ on $X_j^1 \# X_k^2$. Its
    terms are $Gamma$-free, and, for $m>0$,
    $ H_m lr((X^1 times.o X^2))=op("Tor")_R^m lr((M_1,M_2))=0. $
    It is therefore a projective resolution of $M_1 \# M_2$. Finite generation
    of the free terms gives an isomorphism of cochain complexes
    $
      Hom_Gamma lr((X^1 \# X^2,M'_1 \# M'_2)) tilde.equiv
      Hom_(Gamma_1) lr((X^1,M'_1)) times.o
      Hom_(Gamma_2) lr((X^2,M'_2)).
    $
    Write $C_i=Hom_(Gamma_i) lr((X^i,M'_i))$. Their terms are finite projective
    $R$-modules. Their boundary modules are also projective, since $R$ is
    Dedekind. Splitting the surjections onto boundaries reduces the
    cohomological Künneth argument to two-term projective presentations, and
    gives a natural exact sequence
    $
      0 -> sum_(j+k=m) H^j lr((C_1)) times.o H^k lr((C_2))
      -> H^m lr((C_1 times.o C_2)) \
      -> sum_(j+k=m+1) op("Tor")_1^R
      lr((H^j lr((C_1)),H^k lr((C_2)))) -> 0,
    $
    split noncanonically as $R$-modules.
    #source(581)
    Take $m=1$. Since $H^0 lr((C_i))=E_i^0$ is finite torsionfree and thus
    projective, the Tor terms involving $H^0$ vanish; the only remaining term is
    $op("Tor")_1^R lr((E_1^1,E_2^1))$. This proves the asserted short exact
    sequence.
  ]
  #ed-note[
    The printed Ext formula omits a Tor term, and its hint uses the homological
    Tor degree for cochain complexes. The corrected argument above restricts the
    Ext assertion to finite groups. For example, with $R=ZZ$, $G_1=G_2=C_2$,
    $M_i=ZZ$ trivial and $M'_i=ZZ$ sign, the printed right hand side is zero but
    the product Ext group is $ZZ slash 2 ZZ$. The Hom assertion retains the
    original arbitrary-group scope.
  ]
] <exc:outer-tensor-ext-kunneth>
