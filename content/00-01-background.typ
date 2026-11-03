#import "main-defs.typ": *
#import "statements.typ": *

== Background Material on Algebras and Groups <sec:background-algebras-groups>
#heading(level: 3)[
  Algebras over Commutative Rings. Integral Closure
] <ss:algebras-integral-closure>

#source(23)
We presuppose familiarity with the basic concepts of rings and modules. Each
ring $A$ under consideration is assumed to have an identity element (usually
denoted by $1_A$ or $1$), which acts as the identity operator on each
$A$-module. We abbreviate “finitely generated” as “f.g.,”#idx(
  "f. g. = finitely generated",
) and write $M$ is f.g./$A$ to indicate that $M$ is a finitely generated
$A$-module.

#definition[
  A ring $A$ is said to be an _algebra over a commutative ring_ $R$, or an
  _$R$-algebra_, if there exists a homomorphism $psi: R -> c(A)$ from $R$ into
  the center $c(A)$ of $A$, such that $psi(1_R) = 1_A$.
] <def:algebra-over-commutative-ring>
#idx(
  "algebra (over a ring)",
  target: [@def:algebra-over-commutative-ring],
)

#examples[
  #enum(
    numbering: "(i)",
    [Every ring is a $ZZ$-algebra.],
    [If $G$ is a group, the _group ring_#idx(
        "group ring",
      ) $R G$ is the set of all formal finite sums
      $ {sum_(x in G) alpha_x x: alpha_x in R}, $
      with addition and multiplication defined by
      $
        (sum alpha_x x) + (sum beta_x x) = sum (alpha_x + beta_x)x,
        (sum alpha_x x)(sum beta_y y) = sum_(x,y) alpha_x beta_y x y.
      $
      This group ring $R G$ is an $R$-algebra by virtue of the embedding
      $R -> R G$, given by $alpha -> alpha dot 1_G$, $alpha in R$, where $1_G$
      is the identity element of $G$.

      In the special case where we start with a field $K$, we may form the group
      ring $K G$, which is usually called the _group algebra_#idx(
        "group algebra",
      ) of $G$ relative to $K$. As shown in @bib:CurtisReiner1962[CR §~10], the
      study of matrix representations of $G$ over $K$ is essentially equivalent
      to the study of $K G$-modules. This point of view will be fundamental
      throughout our discussion of representations of groups in
      Chapters~@ch:group-representations-character-theory
      and~@ch:modular-representations.

      #source(24)
      When $R$ is a ring of integers, we often call $R G$ an _integral group
      ring_#idx(
        "group ring",
      )#idx(
        "integral group ring",
      ). This concept is important in our discussion of cohomology of groups in
      §@ss:cohomology-groups, where we make use of the integral group ring
      $ZZ G$. It also plays a basic role in
      Chapters~@ch:integral-representations
      and~@ch:local-global-integral-representations on integral representations
      of groups.],
    [The ring $M_n lr((R))$ of all $n times n$ matrices over $R$ is an
      $R$-algebra.],
    [Given any inclusion $R subset.eq S$ of commutative rings, $S$ is an $R$
      algebra.],
  )
] <exm:algebras>

Let $psi: R -> c(A)$ be a homomorphism as in @def:algebra-over-commutative-ring.
We can then define a composition $R times A -> A$ by
$ (r,a) -> r a = psi(r)a, quad r in R, a in A. $
Under this composition, $A$ becomes a left $R$-module with the additional
property that
$ r(a b) = (r a)b = a(r b), quad a,b in A, r in R. $
Conversely, let $A$ be a ring which is a left $R$-module satisfying the above,
over a commutative ring $R$. Then the map $psi: R -> A$ defined by
$psi(r) = r dot 1_A$, $r in R$, has the property that $psi(r) in c(A)$ for all
$r in R$, and $psi(1_R) = 1_A$; thus the conditions in
Definition~@def:algebra-over-commutative-ring are satisfied.

An _$R$-subalgebra_ $B$ of an $R$-algebra $A$ is a subring $B$ containing $1_A$
such that $B$ is an $R$-submodule of $A$.

Let $psi: R -> c(A)$ define the structure of an $R$-algebra, and let $M$ be a
left $A$-module. Then $M$ becomes a left $R$-module with composition given by
$ r m = psi(r)m, quad r in R, m in M, $
and satisfies the condition
$ r(a m) = (r a)m = a(r m), quad r in R, a in A, m in M. $
Clearly, $A$-submodules of $M$ are also $R$-submodules. In particular, left or
right ideals in $A$ are $R$-submodules of $A$.

In case $A$ and $A'$ are $R$-algebras, a homomorphism of rings $f: A -> A'$ is
called a _homomorphism of $R$-algebras_ provided that $f$ preserves the
$R$-module structure on $A$ and $A'$, that is, $f(r a) = r f(a)$, $r in R$,
$a in A$. A homomorphism of $R$-algebras $A -> M_n lr((R))$ (see @exm:algebras
(iii)) is called an _$R$-representation_ of $A$. If $M$ and $M'$ are
$A$-modules, and $A$ is an $R$-algebra, an $A$-homomorphism $f: M -> M'$ is
automatically a homomorphism of $R$-modules because, if $psi: R -> c(A)$ defines
the $R$-structure on $A$, we have
$ f(r m) = f(psi(r)m) = psi(r)f(m) = r f(m), $
for all $r in R$, $m in M$.

#source(25)
It is understood that discussions of rings and modules (in
§§@sec:hom-tensor-projective-injective-flat and~@sec:semisimple-rings-modules,
for example) carry over to $R$-algebras and modules without further explanation.

Let $A$ be an $R$-algebra, for a commutative ring $R$. We shall define the
important concept of integral dependence of elements of $A$ over $R$. A nonzero
polynomial $f(X) in R[X]$ is _monic_#idx(
  "monic",
) if its leading coefficient is $1$. An element $alpha in A$ is _integrally
dependent on_ $R$#idx(
  "integral dependence",
), or _integral over_ $R$#idx(
  "integral",
), if there exists a monic polynomial $f(X) in R[X]$ such that $f(alpha) = 0$.

#lemma[
  Let $A$ be an $R$-algebra, and let $alpha in A$. The following conditions are
  equivalent:
  #enum(
    numbering: "(i)",
    [$alpha$ is integral over $R$.],
    [$R[alpha]$ is f.g./$R$.],
    [There exists an $R$-subalgebra $B$ of $A$ such that $alpha in B$ and $B$ is
      a f.g. $R$-submodule of $A$.],
  )
] <lem:integrality-finite-module>
The proof is left as an exercise (or see @bib:Reiner1975[MO (1.10)]).

#corollary[
  Let $alpha,beta in A$ be integral over $R$, and suppose that
  $alpha beta = beta alpha$. Then $alpha plus.minus beta$ and $alpha beta$ are
  also integral over $R$.
] <cor:commuting-integral-elements>

#corollary[
  Let $A$ be a commutative $R$-algebra. The set of all $R$-integral elements of
  $A$ forms an $R$-subalgebra of $A$.
] <cor:integral-elements-subalgebra>

#remark(numbered: false)[
  It is easy to see that when $A$ is not commutative, sums and products of
  integral elements are not necessarily integral.
]

#example(numbered: false)[
  The _algebraic integers_#idx(
    "algebraic integer = alg. int.",
  ) of an algebraic number field $L$ are the elements of $L$ which are integral
  over $ZZ$. By @cor:integral-elements-subalgebra, they form a $ZZ$-subalgebra
  of $L$, hereafter denoted by alg. int. ${L}$.
]

#definition[
  Let $A$ be an $R$-algebra. The _integral closure_ of $R$ in $A$ is the set of
  all $R$-integral elements in $A$. The ring $R$ is said to be _integrally
  closed in_ $A$ if the integral closure of $R$ in $A$ coincides with the
  $R$-subalgebra $R dot 1_A$. An integral domain $R$ is _integrally closed_#idx(
    "integrally closed",
  ) if it is integrally closed in its quotient field.
] <def:integral-closure>
#idx(
  "integral closure",
  target: [@def:integral-closure],
)

Some examples of integrally closed integral domains are:
#enum(
  numbering: "(a)",
  [P.I.D.'s (principal ideal domains)],
  [U.F.D.'s (unique factorization domains)],
  [Dedekind domains (see §@sec:dedekind-domains).],
  [#source(26)
    Let $R$ be an integral domain with quotient field $K$, and let $K'$ be an
    algebraic extension field of $K$. The integral closure $R'$ of $R$ in $K'$
    is an integrally closed domain with quotient field $K'$.],
  [Let $S$ be a multiplicative subset of an integrally closed domain $R$. Then
    the ring of quotients $S^(-1) R$ is integrally closed (see
    §@sec:dedekind-domains).],
  [Let $R$ be a U.F.D. Then the polynomial ring $R[X_1, dots, X_n]$ in
    indeterminates ${X_1, dots, X_n}$ is a U.F.D., and is integrally closed by
    b).],
)

Let $R = ZZ + ZZ(2 i)$, a domain with quotient field $QQ(i)$ (viewed as a
subfield of the complex field $CC$, where $i^2 = -1$). Then $i$ is integral over
$R$, but $i in.not R$, so $R$ is not integrally closed. The integral closure of
$R$ in $QQ(i)$ is the ring of Gaussian integers#idx(
  "Gaussian integers",
) $ZZ + ZZ i$ in $QQ(i)$.

A basic factorization property of polynomials over integrally closed domains is
due to Gauss.

#lemma(name: "Gauss's Lemma")[
  Let $R$ be an integrally closed domain with quotient field $K$, and let
  $f(X) in R[X]$ be a monic polynomial which factors in $K[X]$:
  $ f(X) = g(X)h(X), $
  with $g(X)$ and $h(X)$ monic polynomials in $K[X]$. Then $g(X)$ and $h(X)$ lie
  in $R[X]$.
] <lem:gauss-integrally-closed>
#idx(
  "Gauss' Lemma",
  target: [@lem:gauss-integrally-closed],
)

Now let $R$ be an integral domain with quotient field $K$, and $A$ a f.d.
$K$-algebra. For each $alpha in A$, the _minimal polynomial_#idx(
  "minimal polynomial = min. pol.",
) of $alpha$ over $K$, denoted by
$ "min. pol."_K lr((alpha)), $
is the monic polynomial $f(X) in K[X]$ of least degree, if one exists, such that
$f(alpha) = 0$. Because $dim_K A$ is finite, every element $alpha in A$ has a
minimal polynomial, and $"min. pol."_K lr((alpha))$ is uniquely determined by
$alpha$. Moreover, the existence of a division algorithm in $K[X]$ implies that
if $h(X) in K[X]$ is such that $h(alpha) = 0$, then $"min. pol."_K lr((alpha))$
divides $h(X)$ in $K[X]$. A basic criterion for integral dependence in finite
dimensional $K$-algebras is the following:

#proposition[
  Let $R$ be an integrally closed domain with quotient field $K$, and let $A$ be
  a finite dimensional $K$-algebra. An element $alpha in A$ is integral over $R$
  if and only if $"min. pol."_K lr((alpha)) in R[X]$.
] <prop:minimal-polynomial-integrality>
The proof is straightforward, using Gauss's Lemma~@lem:gauss-integrally-closed
(see @bib:Reiner1975[MO (1.14)]).

We recall that for $alpha in A$, the _characteristic polynomial_#idx(
  "characteristic polynomial = char. pol.",
)
$ "char. pol."_(A slash K) lr((alpha)) $
#source(27)
is the characteristic polynomial of the $K$-linear map $a -> alpha a$, $a in A$.
From linear algebra, we know that $"min. pol."_K lr((alpha))$ and
$"char. pol."_(A slash K) lr((alpha))$ have the same irreducible factors in
$K[X]$, apart from multiplicities, and that $"min. pol."_K lr((alpha))$ divides
$"char. pol."_(A slash K) lr((alpha))$ in $K[X]$. Keeping the notation of
@prop:minimal-polynomial-integrality and again using Gauss's Lemma, we thus
obtain:

#proposition[
  Let $R$ be integrally closed. An element $alpha in A$ is integral over $R$ if
  and only if $"char. pol."_(A slash K) lr((alpha)) in R[X]$.
] <prop:characteristic-polynomial-integrality>

#remark(numbered: false)[
  For $alpha in A$, $"char. pol."_(A slash K) lr((alpha))$ depends not only on
  $alpha$, but on the choice of the algebra $A$ containing $alpha$. On the other
  hand, if $alpha in A subset B$, where $B$ is another finite dimensional
  $K$-algebra, then $"min. pol."_K lr((alpha))$ is the same whether we regard
  $alpha$ as an element of $A$ or $B$.
]

Now let ${v_1, dots, v_m}$ be a $K$-basis of $A$, and let $alpha in A$. Then we
have
$
  alpha v_j = sum_(i=1)^m a_(i j) v_i, quad
  "with" a_(i j) in K, quad 1 <= j <= m.
$
Let $X$ be an indeterminate over $K$. Then,
$
  "char. pol."_(A slash K) lr((alpha)) & = det(delta_(i j) X - a_(i j)) \
                                       & = X^m - T_(A slash K) lr((alpha))
                                         X^(m-1)
                                         + dots
                                         + (-1)^m N_(A slash K) lr((alpha)).
$ <eq:characteristic-polynomial-trace-norm>
We call $T_(A slash K)$ the _trace map_#idx(
  "trace map",
) (from $A$ to $K$), and $N_(A slash K)$ the _norm map_#idx(
  "norm",
). Evidently, $T_(A slash K) lr((alpha))$ is the sum, and
$N_(A slash K) lr((alpha))$ the product, of the eigenvalues of the matrix
$(a_(i j))$; $T_(A slash K) lr((alpha))$ and $N_(A slash K) lr((alpha))$ are
also the trace and determinant, respectively, of the linear transformation
$v -> alpha v$, $v in A$. From properties of the trace and determinant, and the
fact that the map $alpha -> (a_(i j))$ defines a homomorphism of $K$-algebras,
it follows that
$
  cases(
    T_(A slash K) lr((a alpha + b beta)) =
    a T_(A slash K) lr((alpha)) + b T_(A slash K) lr((beta))\, quad
    T_(A slash K) lr((alpha beta)) = T_(A slash K) lr((beta alpha)),
    N_(A slash K) lr((alpha beta)) =
    N_(A slash K) lr((alpha)) N_(A slash K) lr((beta))\, quad
    N_(A slash K) lr((a alpha)) = a^(dim_K A) N_(A slash K) lr((alpha)),
  )
$ <eq:trace-norm-identities>
for all $a,b in K$, $alpha,beta in A$.

More generally, let $V$ be any f.d. $K$-space, and let $f in "End"_K V$.
Choosing a $K$-basis for $V$, we may represent $f$ by a matrix $bold(f)$ over
$K$. We define
$ "Tr"(f,V) = "trace of" bold(f), $
and clearly this trace $"Tr"(f,V)$ is independent of the choice of $K$-basis of
$V$. If $V$ is a left $A$-module, where $A$ is a $K$-algebra, then each $x in A$
defines a $K$-linear map $x_l: V -> V$, where
$ x_l lr((v)) = x v, quad v in V. $

#source(28)
We then write
$ "Tr"(x,V) "or" "Tr"(x_l,V) $
for the trace of $x_l$ acting on $V$. The analogues of the formulas in
@eq:trace-norm-identities remain true for this situation.

Each $K$-algebra $A$ may be viewed as a left $A$-module, called the _left
regular $A$-module_#idx(
  "regular module",
) $attach(A, bl: A)$. The map $x -> x_l$, $x in A$, is called the _left regular
representation_#idx(
  "regular representation",
) of $A$, and represents each $x in A$ by a $K$-linear transformation
$x_l in "End"_K A$. Clearly
$ T_(A slash K) lr((x)) = "Tr"(x, attach(A, bl: A)) quad "for" x in A. $

=== Background from Group Theory <ss:background-group-theory>

We assume the reader has an understanding of basic group theory. In this
subsection, we review definitions, notation, and elementary facts from three
topics in group theory with which we shall frequently be concerned. These are:
homomorphisms and group extensions, actions of groups on sets, and presentations
of groups in terms of generators and relations. For proofs, and further
discussion, the reader may consult @bib:CurtisReiner1962[CR §§~1–7], and
introductory material in Hall~@bib:Hall1959, Huppert~@bib:Huppert1967, or
Gorenstein~@bib:Gorenstein1968.

#theorem(name: "Fundamental Theorem on Homomorphisms")[
  #enum(
    numbering: "(i)",
    [Let $G$ be a group, and $H$ a normal subgroup of $G$. The cosets of $H$ in
      $G$ form a group $G slash H$, and there is a natural epimorphism of groups
      $pi: G -> G slash H$, given by $pi(x) = x H$, $x in G$.],
    [Let $phi: G -> overline(G)$ be a homomorphism of groups, and set
      $
        "im" phi = {phi(x): x in G}, quad
        "ker" phi = {x in G: phi(x) = 1}.
      $
      Then $"im" phi <= overline(G)$ and $"ker" phi lt.closed.eq G$. Moreover,
      there exists a factorization
      $ phi = tilde(phi) compose pi, $
      where $pi: G -> G slash "ker" phi$ is the natural epimorphism in (i)
      above, and where $tilde(phi): G slash "ker" phi -> "im" phi$ is the
      isomorphism given by $tilde(phi) lr((x dot "ker" phi)) = phi(x)$, for all
      $x in G$.],
    [Let $phi: G -> overline(G)$ be an epimorphism of groups. There is a
      bijection between the family of all subgroups $overline(H) <=
      overline(G)$, and the family of all subgroups $H$ of $G$ such that
      $H >= "ker" phi$. The bijection is given by $H -> phi(H) =
      overline(H)$, and $overline(H) -> phi^(-1) lr((overline(H))) = H$, for
      subgroups $H <= G$ such that $H >= "ker" phi$, and subgroups
      $overline(H) <= overline(G)$. We have
      $overline(H) lt.closed.eq overline(G)$ if and only if
      $phi^(-1) lr((overline(H))) lt.closed.eq G$, and if this occurs, then
      $
        G slash phi^(-1) lr((overline(H))) tilde.equiv
        overline(G) slash overline(H).
      $],
  )
] <th:fundamental-homomorphisms>

#source(29)
The preceding result is the first step towards analyzing groups in terms of
normal subgroups and homomorphic images.

#definition[
  A group $G$ is an _extension_ of a group $H$ with kernel $N$ if there exists
  an epimorphism $phi: G -> H$ such that $N = "ker" phi$.
] <def:group-extension>
#idx(
  "extension of groups",
  target: [@def:group-extension],
)

Extensions can be described using the language of exact sequences (see
§§@sec:hom-tensor-projective-injective-flat and~@sec:ext-tor-cohomology for
further discussion.) Thus, $G$ is an extension of $H$ with kernel $N$ if and
only if there exists an exact sequence of groups
$ 1 -> N arrow.r^psi G arrow.r^phi H -> 1. $
Exactness means that $psi: N -> G$ is injective, $phi$ is surjective, and
$"im" psi = "ker" phi$; then we have $H tilde.equiv G slash psi(N)$, by
@th:fundamental-homomorphisms.

The simplest type of extension is, of course, a direct product $G = H times N$.
A more general case, of great importance in practice, is that where $G$ is a
split extension of $H$, defined as follows:

#definition[
  An extension $phi: G -> H$ is _split_ if there exists a homomorphism
  $lambda: H -> G$ such that $phi compose lambda = "id"_H$; such a map $lambda$
  is sometimes called a _splitting map_.
] <def:split-extension>
#idx(
  "split extension of groups",
  target: [@def:split-extension],
)

#proposition[
  An extension $phi: G -> H$ with kernel $N$ is split if and only if there
  exists a subgroup $H_1$ of $G$ such that $G = H_1 N$ and $H_1 inter N = 1$.
] <prop:split-extension-complement>

In case $G = H_1 N$ as in @prop:split-extension-complement, we call $G$ a
_semidirect product_#idx(
  "semidirect product",
) of the normal subgroup $N$ and the subgroup $H_1$, and use the notation
$ G = N times.r H_1 $
when this occurs.

Thus, semidirect products are the same as split extensions. For example, one of
the non-abelian groups of order $8$ is a split extension (the dihedral group)
while the other is a nonsplit extension (the quaternion group). In both cases,
the normal subgroup $N$ and the quotient $G slash N$ are the same, but the
groups are not isomorphic.

Groups which cannot be analyzed in terms of extensions are the _simple groups_,
that is, groups having no proper non-trivial normal subgroups. These are the
basic objects from which other groups are constructed. The classification of
finite simple groups has been, for many years, the central problem in finite
group theory, and has stimulated much of the current research in character
theory.

#source(30)
#definition[
  A _normal series of length_ $s$ of a group $G$ is a chain of subgroups
  $ G = G_1 >= G_2 >= dots >= G_s >= G_(s+1) = 1, $
  such that $G_(i+1) lt.closed.eq G_i$, for $1 <= i <= s$. The _factors_ of the
  normal series are the groups ${G_i slash G_(i+1): 1 <= i <= s}$. In case the
  factors are simple and non-trivial, the normal series above is called a
  _composition series_#idx(
    "composition series",
  ) for $G$.
] <def:normal-composition-series>
#idx(
  "normal series",
  target: [@def:normal-composition-series],
)

#theorem(name: "Jordan–Hölder Theorem")[
  Let $G$ have two composition series
  $
    G = G_1 >= dots >= G_(s+1) = 1, quad
    G = H_1 >= dots >= H_(t+1) = 1,
  $
  of lengths $s$ and $t$, respectively. Then $s = t$, and there exists a
  permutation $sigma$ of ${1, dots, s}$ such that
  $G_i slash G_(i+1) tilde.equiv H_(sigma(i)) slash H_(sigma(i)+1)$,
  $1 <= i <= s$.
] <th:jordan-holder>
#idx(
  "Jordan-Holder Theorem",
  target: [@th:jordan-holder],
)

#examples(numbered: false, name: "Examples of Normal Series")[
  #enum(
    numbering: "(i)",
    [The _derived series_#idx(
        "derived series",
      ): The _derived subgroup_#idx(
        "derived group",
      )#idx(
        "group",
        "derived",
      ) $G'$ (or _commutator subgroup_) of a group $G$ is the subgroup generated
      by all commutators ${(a,b) = a b a^(-1) b^(-1): a,b in G}$. Then $G'$ is
      the smallest normal subgroup of $G$ such that the quotient group is
      abelian. The _derived series_ of $G$ is the normal series
      $ G >= G^((1)) >= G^((2)) >= dots, $
      where $G^((i))$ is the derived subgroup of $G^((i-1))$, for each $i$.],
    [The _lower central series_#idx(
        "lower central series",
      ) of $G$ is
      $ G = G_1 >= G_2 >= G_3 >= dots, $
      where $G_i$ is the subgroup $[G_(i-1),G]$ generated by all commutators
      ${(x,y): x in G_(i-1), y in G}$.],
    [The _upper central series_#idx(
        "upper central series",
      ) of $G$ is
      $ 1 <= Z_1 <= Z_2 <= dots, $
      where $Z_1$ is the center $Z(G)$ of $G$, $Z_2$ is the subgroup of $G$
      containing $Z_1$ such that $Z_2 slash Z_1 = Z(G slash Z_1)$, and so on.],
  )
] <exm:normal-series>

We recall that a group $G$ is _solvable_#idx(
  "group",
  "solvable",
)#idx(
  "solvable group",
) if some term $G^((i))$ in the derived series coincides with the trivial
subgroup $1$. A group $G$ is _nilpotent_#idx(
  "group",
  "nilpotent",
)#idx(
  "nilpotent group",
) if $G_m = 1$ for some term $G_m$ in the lower central series, or equivalently,
if $Z_n = G$ for some term $Z_n$ in the upper central series. A finite group is
solvable if and only if it has a composition series whose factors are cyclic of
prime order. A finite group $G$ is
#source(31)
_supersolvable_#idx(
  "group",
  "supersolvable",
)#idx(
  "supersolvable group",
) if $G$ is solvable, and in addition, $G$ has a composition series
$ G >= G_1 >= dots >= G_(s+1) = 1 $
in which all of the subgroups ${G_i}$ are normal subgroups of $G$.

We now turn to arithmetical considerations. Let $p$ be a prime. An element $x$
of a finite group $G$ is a _$p$-element_#idx(
  "p-element, Π-element",
) if the order of $x$ is a power of $p$, and a _$p'$-element_#idx(
  "p′-element, Π′-element",
) (or a _$p$-regular element_) if the order of $x$ is prime to $p$. The identity
element is the only element of $G$ which is simultaneously a $p$-element and a
$p'$-element. The primary decomposition of the cyclic group
$chevron.l x chevron.r$ shows that for each prime $p$, there exists a
factorization
$ x = x' x'', $
with $x'$ a $p'$-element and $x''$ a $p$-element, and $x' x'' = x'' x'$. The
factors $x'$ and $x''$ are called the _$p'$-part_ (or _$p$-regular part_) of
$x$, and the _$p$-part_ of $x$, respectively; the elements $x'$ and $x''$ are
uniquely determined by the above properties.

The order of a finite group $G$ is denoted by $|G|$, and the index of a subgroup
$H$ by $|G:H|$. A group $G$ whose order is a power of a prime $p$ is called a
_$p$-group_, while a group whose order is not divisible by $p$ is called a
_$p'$-group_. We assume the reader is familiar with the existence and properties
of the Sylow $p$-subgroups of a finite group (see @bib:CurtisReiner1962[CR
  §~6]).

A group $G$ is _$p$-solvable_#idx(
  "group",
  "p-solvable",
)#idx(
  "p-solvable group",
), for a prime $p$, if $G$ has a normal series such that each factor is either a
$p$-group or a $p'$-group. We have inclusions
$
  {p "-groups"} subset.eq {vec(delim: #none, "nilpotent", "groups")}
  subset.eq {vec(delim: #none, "supersolvable", "groups")}
  subset.eq {vec(delim: #none, "solvable", "groups")}
  subset.eq {vec(delim: #none, p "-solvable", "groups")},
$
with strict inclusions at each stage.

A group $G$ has a _normal $p$-complement_#idx(
  "normal p-complement",
) if there exists a normal subgroup $H lt.closed.eq G$ such that
$ G = H times.r S, $
for some Sylow $p$-subgroup $S$ of $G$. A group having a normal $p$-complement
is clearly $p$-solvable, but is not necessarily solvable. For Burnside's Theorem
on normal $p$-complements, see @th:burnside-normal-p-complement below.

The symmetric groups ${S_n}$#idx(
  "group",
  "symmetric",
) and alternating groups ${A_n}$ are solvable for $n <= 4$, and not solvable for
$n >= 5$.

Nilpotent groups are easily shown to have the property that each proper subgroup
is properly contained in its normalizer. From this it follows that finite
nilpotent groups are direct products of their Sylow subgroups
(@bib:CurtisReiner1962[CR (6.12)]).

We next consider groups acting on sets. Using this approach, many problems in
group theory can be translated into the more concrete language of permutation
groups.

#source(32)
#definition[
  A _$G$-set_ $Omega$ is a triple consisting of a group $G$, a set $Omega$, and
  a map from $G times Omega$ to $Omega$ (notation: $(x,w) -> x w$, $x in G$,
  $w in Omega$) such that
  $ 1 w = w, quad x(y w) = (x y)w, quad x,y in G, w in Omega. $
  The map $G times Omega -> Omega$ is called the _action of_ $G$ _on_ $Omega$,
  and we shall say that $G$ _acts on_ $Omega$. Two $G$-sets $Omega$ and $Omega'$
  are _isomorphic_ (notation: $Omega tilde.equiv Omega'$) if there exists a
  bijection $f: Omega -> Omega'$ such that $f(x w) = x f(w)$ for all
  $w in Omega$, $x in G$.
] <def:g-set>
#idx(
  "G-set",
  target: [@def:g-set],
)

Let $Omega$ be a $G$-set. For each $x in G$, the _left multiplication_
$x_l: Omega -> Omega$ is the map defined by $x_l w = x w$, $w in Omega$. These
maps have the properties:
$ 1_l = "id"_Omega, quad (x y)_l = x_l y_l, quad x,y in G, $
by the definition of $G$-sets. It follows that the map defined by $x -> x_l$,
$x in G$, is a homomorphism from $G$ into the group of permutations of $Omega$.

Let $Omega$ be a finite $G$-set, and let $R$ be any commutative ring. Let $M$ be
a free $R$-module with basis ${m_w: w in Omega}$, where the basis elements are
symbols corresponding bijectively to the elements of $Omega$. Each element
$x in G$ defines an $R$-linear map $T(x): M -> M$, where $T(x)m_w = m_(x w)$,
for $w in Omega$. As in the case of left multiplications, it follows that
$T(1) = 1_M$, and $T(x y) = T(x)T(y)$, for $x,y in G$. Thus we have a
homomorphism $T$ from $G$ into the group of $R$-automorphisms of $M$.

The maps $x -> x_l$ and $x -> T(x)$, associated with a fixed $G$-set $Omega$,
are called _permutation representations_#idx(
  "permutation representation",
) of $G$ defined by the $G$-set $Omega$. For the case where $G$ acts on the
_permutation module_ $M$ defined above, the trace function,
$ x -> "Tr"(x,M) in R, quad x in G, $
is called the _permutation character_#idx(
  "permutation character",
) associated with the $G$-set $Omega$.

For each $G$-set $Omega$, there is an equivalence relation $tilde.op$ on
$Omega$, defined by $v tilde.op w$ if $w = x v$ for some $x in G$, where
$v,w in Omega$. The equivalence classes are called the _$G$-orbits_#idx(
  "orbit",
), or simply _orbits_, of the action of $G$ on $Omega$. A $G$-set is called
_transitive_#idx(
  "transitive",
) if there is only one orbit.

#definition[
  Let $Omega$ be a $G$-set, and let $w in Omega$. The _stabilizer_ of $w$ in $G$
  (notation: $"Stab"_G w$) is defined by
  $ "Stab"_G w = {x in G: x w = w}. $
] <def:stabilizer>
#idx(
  "stabilizer",
  target: [@def:stabilizer],
)

We note that $"Stab"_G w$ is a subgroup of $G$, for each $w in Omega$. If $H$ is
any subgroup of $G$, the left cosets $G slash H = {y H: y in G}$ form a
transitive $G$-set, with the action of $G$ defined by
$ (x,y H) -> x y H, quad x in G, y H in G slash H. $

#source(33)
In this case, $H = "Stab"_G H$, since $H = {x in G: x H = H}$.

The $G$-sets of the form $G slash H$ are characterized in the following:

#proposition[
  Let $Omega$ be a $G$-set. Then the following statements hold:
  #enum(
    numbering: "(i)",
    [Let $Omega$ be transitive, and let $w,w' in Omega$. Set $H = "Stab"_G w$
      and $H' = "Stab"_G w'$. Then $w' = x w$ for some $x in G$, and
      $H' = x H x^(-1)$. For each element $w in Omega$, there is an isomorphism
      of $G$-sets
      $ Omega tilde.equiv G slash H, quad "where" H = "Stab"_G w. $],
    [Let $Omega$ be transitive, and assume that both $G$ and $Omega$ are finite.
      Then $|Omega| = |G: "Stab"_G w|$ for each $w in Omega$. In particular,
      $|Omega|$ divides $|G|$.],
    [Let $Omega$ be finite, but not necessarily transitive, and let
      ${Omega_i: i in I}$ be the $G$-orbits in $Omega$. Then we have
      $ |Omega| = sum_(i in I) |Omega_i|, $
      and
      $
        |Omega_i| = |G: "Stab"_G w_i|, quad
        "for any" w_i in Omega_i, i in I.
      $],
  )
] <prop:orbits-stabilizers>

We now recall some familiar examples of $G$-sets.

#examples[
  #enum(
    numbering: "(i)",
    [Let $H <= G$. Then $H$ acts on $G$ by left multiplication $(h,x) -> h x$,
      and by right multiplication $(x,h) -> x h$, for $x in G$, $h in H$. The
      $H$-orbits are the _right cosets_#idx(
        "cosets (left, right, double)",
      ) ${H x}$ in the first case, and the _left cosets_ ${x H}$ in the second.
      For example, $H x$ is the right $H$-coset containing $x$, for $x in G$.],
    [Let $H,K$ be subgroups of $G$. Then the direct product $H times K$ acts on
      $G$ as follows:
      $ ((h,k),x) -> h x k^(-1), quad x in G, h in H, k in K. $
      The orbits in this case are the _$(H,K)$-double cosets_ ${H x K}$.],
    [The group $G$ acts on itself through inner automorphisms:
      $ (x,y) -> x y x^(-1) = i_x lr((y)), quad x,y in G, $
      where the map $i_x$ is the _inner automorphism_#idx(
        "inner automorphism",
      ) associated with $x$. The homomorphism $x -> i_x$, $x in G$, maps $G$
      onto the group of inner automorphisms of $G$. The kernel of this
      homomorphism is the _center_ of $G$, and is denoted by $Z(G)$.

      #source(34)
      Relative to the action by inner automorphisms, the orbits of $G$ are the
      _conjugacy classes_#idx(
        "conjugacy class",
      ) of $G$. If $frak(C)$ is a conjugacy class, and $x in frak(C)$, the
      stabilizer of $x$ in $G$ is the _centralizer_#idx(
        "centralizer",
      ) $C_G lr((x))$ of $x in G$, and is defined by
      $ C_G lr((x)) = {y in G: y x y^(-1) = x}. $
      In case $G$ is finite, the equations in @prop:orbits-stabilizers (iii)
      yield the _class equation_:
      $ |G| = |Z(G)| + sum_(C_G lr((x)) < G) |G:C_G lr((x))|. $
      <eq:class-equation>
      Here, the center is the union of conjugacy classes containing elements
      $x in G$ whose stabilizer $C_G lr((x)) = G$; in the second summation, $x$
      ranges over representatives of conjugacy classes containing more than one
      element. The class equation is used, for example, to prove that the center
      of a $p$-group $G != 1$ is nontrivial.],
    [Let $H <= G$, and let $Omega$ be the set of $G$-conjugates
      ${x H x^(-1): x in G}$ of $H$. Then $Omega$ is a $G$-set, with the action
      of $G$ given by
      $ (y,x H x^(-1)) -> y x H x^(-1) y^(-1), quad x,y in G. $
      In other words, $G$ acts on $Omega$ through inner automorphisms. We have
      $"Stab"_G H = {x in G: x H x^(-1) = H}$. This subgroup is called the
      _normalizer_#idx(
        "normalizer",
      ) $N_G lr((H))$ of $H$, and is the largest subgroup $E$ of $G$ for which
      $H lt.closed.eq E$. By @prop:orbits-stabilizers (ii), the number of
      distinct conjugates of a subgroup $H$ is the index $|G:N_G lr((H))|$.

      Proofs of the Sylow Theorems using these ideas are given in
      @bib:CurtisReiner1962[CR §~6].],
  )
] <exm:group-actions>

Our third topic is the definition of a group by generators and relations.

#definition[
  Let $G$ be a group, and let ${a_1, dots, a_n}$ be elements of $G$, and
  ${w_1, dots, w_t}$ a set of products of the elements $a_i$ and their inverses
  (possibly with repetitions). Then $G$ has a _presentation_
  $ G = chevron.l a_1, dots, a_n: w_1 = dots = w_t = 1 chevron.r, $
  provided that the following conditions are satisfied:
  #enum(
    numbering: "(i)",
    [$G = chevron.l a_1, dots, a_n chevron.r$, (that is, $G$ is generated by the
      elements $a_1, dots, a_n$), and the relations $w_1 = 1, dots, w_t = 1$ all
      hold.],
    [If $G'$ is another group containing elements $a'_1, dots, a'_n$ such that
      $w'_1 = dots = w'_t = 1$ in $G'$, where the ${w'_i}$ are the expressions
      in $G'$ corresponding to the ${w_i}$ in $G$, then there exists a unique
      homomorphism $phi: G -> G'$ such that $phi(a_i) = a'_i$, $1 <= i <= n$.],
  )
] <def:group-presentation>

It follows easily from the definition that two groups with the same presentation
are isomorphic. It is also not difficult to show, using the theory of free
#source(35)
groups, that given any expressions ${w_1, dots, w_t}$ in the symbols
${a_1, dots, a_n}$, there exists a group $G$ having the presentation
$ G = chevron.l a_1, dots, a_n: w_1 = dots = w_t = 1 chevron.r. $
Of course, there is no guarantee that the group $G$ is non-trivial.

#examples[
  #enum(
    numbering: "(i)",
    [The _dihedral groups_#idx(
        "dihedral group",
      )#idx(
        "group",
        "dihedral",
      ). For each $n$, the dihedral group $D_n$ of order $2 n$ has a
      presentation
      $ D_n = chevron.l a,b: a^n = 1, b^2 = 1, (a b)^2 = 1 chevron.r. $],
    [The _generalized quaternion groups_#idx(
        "generalized quaternion group",
      )#idx(
        "group",
        "generalized quaternion",
      ). For each positive integer $m$, there exists a finite group $Q_m$ of
      order $4 m$, having the presentation
      $
        Q_m = chevron.l a,b: a^(2 m) = 1, b^2 = a^m,
        b a b^(-1) = a^(-1) chevron.r.
      $
      For $m = 2$, we have a presentation of the quaternion group $Q$#idx(
        "group",
        "quaternion",
      )#idx(
        "quaternion group",
      ) of order $8$. We call $Q_m$ a _generalized quaternion group_.],
  )
] <exm:dihedral-quaternion-presentations>

In Chapter~7 of Volume~II, we shall discuss presentations of Coxeter groups,
which include the symmetric groups and hyper-octahedral groups.

#exercises-heading

#exercise[
  Let $A$ be a f.d. $K$-algebra, where $K$ is a field, and let $alpha in A$.
  Show that there exists an element $beta in K[alpha]$ such that
  $ alpha beta = beta alpha = N_(A slash K) lr((alpha)). $
  #hint([@exc:adjugate-element])[Use the fact that $alpha$ is a zero of its
    characteristic polynomial.]
] <exc:adjugate-element>

#exercise[
  Keep the above notation, and let $R$ be an integrally closed domain with
  quotient field $K$. Show that if $alpha in A$ is integral over $R$, then there
  exists an element $beta in R[alpha]$ such that
  $alpha beta = beta alpha = N_(A slash K) lr((alpha))$, and $beta$ is also
  integral over $R$.

  #hint([@exc:integral-adjugate-element])[Use
    @prop:characteristic-polynomial-integrality.]
] <exc:integral-adjugate-element>
