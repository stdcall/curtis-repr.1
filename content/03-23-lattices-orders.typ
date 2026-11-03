#import "main-defs.typ": *
#import "statements.typ": *

== Lattices and Orders <sec:lattices-orders>

Throughout this section, $R$ denotes a commutative ring (with 1). We shall be
primarily interested in the case where $R$ is an integral domain, though much of
the discussion below does not require this restriction on $R$. As in
§@ss:contragredient-modules, an _$R$-lattice_#idx("lattice")#idx("R-lattice") is
a f.g. projective $R$-module. This terminology is suggested by a geometric
example: let $M={(a,b):a,b in ZZ}$, the set of integral lattice points in the
plane; then $M$ is a $ZZ$-lattice relative to componentwise addition of ordered
pairs.

Suppose for the time being that $R$ is an integral domain. The torsion submodule
of an arbitrary $R$-module $M$ is defined to be
$ {m in M:r m=0 "for some nonzero" r in R}. $
Call $M$ _torsionfree_#idx("torsionfree") if its torsion submodule is 0. Some
authors use the terminology “$R$-lattice” to mean a f.g. torsionfree $R$-module.
However, we shall keep to our original definition throughout this book.

When $R$ is an integral domain, every free $R$-module is torsionfree, and
therefore every $R$-lattice is also torsionfree. The converse is not true in
general: torsionfree modules need not be lattices. However, for certain types of
rings $R$, a f.g. $R$-module $M$ is an $R$-lattice if and only if $M$ is
torsionfree. This is the case whenever $R$ is a P.I.D., for example, since then
every f.g. torsionfree $R$-module must have a finite $R$-basis.

More generally, let $R$ be a Dedekind domain. Then (see
§@ss:modules-dedekind-domains) a f.g. $R$-module is torsionfree if and only if
it is $R$-projective. Thus, when $R$ is a Dedekind domain, every $R$-lattice is
a f.g. torsionfree $R$-module, and conversely. Since submodules of f.g.
torsionfree $R$-modules are necessarily f.g. torsionfree, it follows (in this
case) that submodules of $R$-lattices are necessarily $R$-lattices. However,
factor modules of lattices need not be lattices, since they may fail to be
torsionfree.

Our next task is to motivate the definition of “order” given below. Let $R$ be
an arbitrary integral domain, and let $Lambda$ be an $R$-algebra (see
§@ss:algebras-integral-closure). Every $Lambda$-module, including $Lambda$
itself, may then be viewed as an $R$-module, using the
#source(545)
homomorphism from $R$ into the center of $Lambda$. We always take this point of
view hereafter, without further comment. Now let $M$ be any nonzero left
$Lambda$-module, and suppose that as $R$-module, $M$ is an $R$-lattice. Let us
put
$ I={x in Lambda:x M=0}=Lambda "-annihilator of" M. $
Define $overline(Lambda)=Lambda slash I$, which is obviously an $R$-algebra
acting on $M$. Indeed, $overline(Lambda)$ acts _faithfully_#idx("faithfully") on
$M$ (that is, the $overline(Lambda)$-annihilator of $M$ is 0). For
$x in Lambda$, let $overline(x)$ be its image in $overline(Lambda)$, and let
$overline(x)_l:M arrow M$ be left multiplication by $overline(x)$ on $M$. Since
the elements of $R$ commute with those of $overline(Lambda)$, it follows that
each $overline(x)_l in End_R M$. Furthermore, $overline(x)_l=0$ if and only if
$overline(x)=0$, since $overline(Lambda)$ acts faithfully on $M$. We thus obtain
a monomorphism of $R$-algebras
$ overline(Lambda) arrow End_R M, $
given by mapping $overline(x) in overline(Lambda)$ onto $overline(x)_l$.
Further, since $M$ is $R$-torsionfree, the ring homomorphism $R arrow$ center of
$overline(Lambda)$ must be a monomorphism, and thus $R$ is embedded in
$overline(Lambda)$. Instead of studying the $Lambda$-structure of $M$, we may
equally well study its $overline(Lambda)$-structure.

We may derive some important consequences from the embedding of
$overline(Lambda)$ into $End_R M$, and begin by analyzing the $R$-structure of
the latter ring. Since $M$ is an $R$-lattice, there is an $R$-isomorphism
$ M plus.o M' tilde.equiv R^((k)) $
for some $k$ and some $R$-module $M'$. Put
$E=End_R R^((k)) tilde.equiv M_k lr((R))$, and let $e:R^((k)) arrow M$ be the
idempotent projection (see §@ss:homomorphisms) associated with the above
decomposition of $R^((k))$. Then there is a _Pierce decomposition_#idx(
  "Pierce decomposition",
)
$ E=e E e plus.o e E(1-e) plus.o (1-e)E e plus.o (1-e)E(1-e), $
and we may identify $End_R M$ with $e E e$. This shows that $End_R M$ is (as
$R$-module) a direct summand of the free $R$-module $M_k lr((R))$, and therefore
$End_R M$ is an $R$-lattice.

Suppose now that $R$ is a Dedekind domain. Since $overline(Lambda)$ is an
$R$-submodule of $End_R M$, it follows that $overline(Lambda)$ is also an
$R$-lattice. Hence in studying lattices over $R$-algebras, where $R$ is a
Dedekind domain, there is no loss of generality in considering only those
$R$-algebras which are themselves $R$-lattices, with $R$ embedded in their
center.

We now make the following definition:

#definition[
  Let $R$ be a Dedekind domain with field of quotients $K$. An _$R$-order_ is a
  ring $Lambda$ whose center contains $R$, and such that $Lambda$ is an
  $R$-lattice. (This means that $Lambda$ is f.g./$R$ and $R$-projective,
  relative to the action of $R$ on $Lambda$ induced by the inclusion of $R$ in
  the center of $Lambda$.)
] <def:order>
#idx("order", target: [@def:order])

#source(546)
Now let $Lambda$ be an $R$-order, where $R$ is a Dedekind domain. Then there is
an embedding $Lambda arrow K times.o_R Lambda$, given by $x mapsto 1 times.o x$,
$x in Lambda$. We always identify $Lambda$ with its image $1 times.o Lambda$ in
$K times.o Lambda$\; this tensor product can then be written as $K dot Lambda$,
the $K$-space spanned by the elements of $Lambda$. Set $A=K times.o_R Lambda$\;
then $A$ is a f.d. $K$-algebra, and $Lambda$ is a subring of $A$ containing a
$K$-basis of $A$. We call $Lambda$ an _R-order in A_, in accordance with the
following:

#definition[
  Let $A$ be a f.d. $K$-algebra, and let $R$ be a Dedekind domain with field of
  quotients $K$. An _$R$-order_ in $A$ is a subring $Lambda$ of $A$ satisfying
  all of the conditions:

  #enum(
    numbering: "(i)",
    [The center of $Lambda$ contains $R$,],
    [$Lambda$ is f.g. as $R$-module,],
    [$K dot Lambda=A$.],
  )
] <def:order-in-algebra>
#idx("order", target: [@def:order-in-algebra])

#examples(name: [Examples of $R$-orders])[
  #enum(
    numbering: "(i)",
    [
      Let $G$ be a finite group, and let
      $ A=K G, Lambda=R G="integral group ring of" G "over" R. $
      Then $Lambda$ is an $R$-order in $A$.
    ],
    [
      Let $L$ be a finite separable field extension of $K$, and let $R'$ be the
      integral closure of $R$ in $L$. Then by @prop:integral-closure-dedekind
      $R'$ is an $R$-order in the $K$-algebra $L$. In particular, if $L$ is an
      algebraic number field, then the ring $op("alg. int."){L}$ is a $ZZ$-order
      in the $QQ$-algebra $L$.
    ],
    [
      Let $frak(b)$ be a nonzero ideal of $R$, and set $A=M_2 lr((K))$, and
      $
        Lambda=mat(R, frak(b); R, R)
        ={mat(a, b; c, d):a,c,d in R,b in frak(b)}.
      $
      Then $Lambda$ is an $R$-order in $A$.
    ],
    [
      Let $A$ be any f.d. $K$-algebra, and let $alpha in A$ be integral over $R$
      (see §@ss:algebras-integral-closure). Then the ring $R[alpha]$ is an
      $R$-order in the commutative $K$-algebra $K[alpha]$.
    ],
  )
] <exm:orders-basic-examples>

#definition[
  Let $Lambda$ be an $R$-order in a $K$-algebra $A$. A _$Lambda$-lattice_ is a
  (left) $Lambda$-module which is an $R$-lattice, that is, f.g. and projective
  as $R$-module.
] <def:order-lattice>
#idx("lattice", target: [@def:order-lattice])

Let $M$ be a $Lambda$-lattice, where $Lambda$ is an $R$-order. If $M$ is
$R$-free with a finite $R$-basis ${m_1,dots,m_d}$, then relative to this basis
$M$ affords a matrix representation $upright(bold(M))$ of $Lambda$. For
$x in Lambda$, let
$ x m_j=sum_(i=1)^d alpha_(i j)m_i, quad alpha_(i j) in R,1 <= j <= d, $
<eq:lattice-representation-coefficients>
#source(547)
and put $upright(bold(M))(x)=(alpha_(i j)) in M_d lr((R))$. The map
$x mapsto upright(bold(M))(x)$, $x in Lambda$, is then a representation of
$Lambda$ by means of matrices with entries in $R$. We call $upright(bold(M))$ an
_integral representation_#idx("integral representation") or
_$R$-representation_#idx(
  "R-representation",
) of $Lambda$.

In order to describe how a change of $R$-basis of $M$ affects the matrix
representation $upright(bold(M))$, it is convenient to write the $R$-basis
${m_i}$ as a formal row vector $upright(bold(m))=(m_1,dots,m_d)$. Then
@eq:lattice-representation-coefficients may be rewritten as
$ x upright(bold(m))=upright(bold(m))upright(bold(M))(x), quad x in Lambda. $
Let ${m'_1,dots,m'_d}$ be another free $R$-basis for $M$, and put
$upright(bold(m))'=(m'_1,dots,m'_d)$. We may write
$upright(bold(m))'=upright(bold(m))upright(bold(P))$ for some matrix
$upright(bold(P)) in GL_d lr((R))$. For $x in Lambda$, we have
$
  x upright(bold(m))'=x upright(bold(m))upright(bold(P))
  =upright(bold(m))upright(bold(M))(x)upright(bold(P))
  =upright(bold(m))' dot
  upright(bold(P))^(-1)upright(bold(M))(x)upright(bold(P)).
$
Thus, change of $R$-basis of $M$ has the effect of replacing $upright(bold(M))$
by the _equivalent representation_#idx("equivalent representations")
$upright(bold(P))^(-1)upright(bold(M))upright(bold(P))$.

We may equally well start with an $R$-representation $upright(bold(M))$ of an
$R$-order $Lambda$\; by definition, $upright(bold(M))$ is an $R$-algebra
homomorphism of $Lambda$ into a matrix ring $M_d lr((R))$, and $d$ is called the
_degree_#idx(
  "degree of a representation",
) of the representation. Let $M$ be the free $R$-module consisting of all
$d times 1$ column vectors over $R$\; then $M$ affords the representation
$upright(bold(M))$ of $Lambda$, relative to the basis ${m_1,dots,m_d}$, where
$m_i$ is the column vector with 1 at position $i$, and zeros elsewhere.

#example[
  Let
  $ G=⟨a,b:a^4=1,b^2=1,b a b^(-1)=a^(-1)⟩ $
  be the dihedral group of order 8, and let $Lambda=ZZ G$ be its integral group
  ring. Then $Lambda$ is a $ZZ$-order in the $QQ$-algebra $QQ G$. Let
  $upright(bold(M))_i$ ($i=1,2$) be the $ZZ$-representation of $Lambda$ defined
  by setting
  $
    upright(bold(M))_1 lr((a))=mat(0, 1; -1, 0),quad
    upright(bold(M))_1 lr((b))=mat(0, 1; 1, 0)\;
  $
  $
    upright(bold(M))_2 lr((a))=mat(0, 1; -1, 0),quad
    upright(bold(M))_2 lr((b))=mat(1, 0; 0, -1).
  $
  It is easily checked that
  $
    upright(bold(M))_i lr((a))^4=1,quad upright(bold(M))_i lr((b))^2=1,quad
    upright(bold(M))_i lr((b a b^(-1)))=upright(bold(M))_i lr((a^(-1))),
    quad i=1,2,
  $
  so $upright(bold(M))_1$ and $upright(bold(M))_2$ are $ZZ$-representations of
  $Lambda$ (and of the group $G$). However, $upright(bold(M))_1$ is not
  $ZZ$-equivalent to $upright(bold(M))_2$, since there is no matrix
  $upright(bold(P)) in GL_2 lr((ZZ))$ for which
  $
    upright(bold(P))^(-1)upright(bold(M))_1 lr((a))upright(bold(P))
    =upright(bold(M))_2 lr((a)),quad
    upright(bold(P))^(-1)upright(bold(M))_1 lr((b))upright(bold(P))
    =upright(bold(M))_2 lr((b)).
  $
] <exm:dihedral-integral-inequivalent-representations>

#source(548)
As in @def:order-in-algebra, let $Lambda$ be an $R$-order in a $K$-algebra $A$,
and let $M$ be any $Lambda$-lattice. Then as in §@ss:modules-dedekind-domains,
we may embed $M$ in the finite dimensional $K$-space $K times.o_R M$. We may
denote this space by $K M$, after the usual identification of $M$ with
$1 times.o M$. Then $K M$ is a f.g. left $A$-module. In practice, we usually
have a great deal of information about the $A$-module $K M$, and the difficulty
arises in trying to classify the full $Lambda$-lattices contained in $K M$.
(Recall that a _full_ $Lambda$-lattice in an $A$-module $V$ is a
$Lambda$-lattice $M$ in $V$ such that $K M=V$.)

We wish to set up a correspondence between $A$-submodules of the f.g. $A$-module
$V$ and the sublattices of a full $Lambda$-lattice $M$ in $V$. Just as in
§@ss:modules-dedekind-domains, the key concept is that of purity. A
$Lambda$-sublattice $L$ of $M$ is called _$R$-pure_#idx("pure") in $M$ if
$M slash L$ is $R$-torsionfree, or equivalently, if $L$ is an $R$-direct summand
of $M$. As in @prop:pure-sublattices-subspaces, we have:

#proposition[
  Let $R$ be a Dedekind domain with field of quotients $K$, and let $Lambda$ be
  an $R$-order in the f.d. $K$-algebra $A$. Let $M$ be a full $Lambda$-lattice
  in the left $A$-module $V$. There is an inclusion-preserving bijection
  $N arrow.l.r W$, where $N$ ranges over all $R$-pure $Lambda$-sublattices of
  $M$, and $W$ ranges over all $A$-submodules of $V$. The bijection is given
  explicitly by
  $ N=M inter W,quad W=K N. $
  Further, for each such $W$, the quotient $M slash (M inter W)$ is a full
  $Lambda$-lattice in the $A$-module $V slash W$.
] <prop:pure-order-sublattice-correspondence>

The existence of the desired bijection follows readily from
@prop:pure-sublattices-subspaces. Furthermore, for each $W$ the
$Lambda$-sublattice $M inter W$ is $R$-pure in $M$, whence $M slash (M inter W)$
is $R$-torsionfree, and is therefore a $Lambda$-lattice. Clearly
$
  K times.o_R {M slash (M inter W)} tilde.equiv
  K M slash K(M inter W)=V slash W,
$
as asserted. In the discussion below, we shall deduce this proposition, as well
as @prop:pure-sublattices-subspaces, as a special case of a more general result
which is of interest in itself, and will be useful later.

Let $R$ be an arbitrary commutative ring, and $S$ any multiplicative subset of
$R$ (see §@ss:localization). Let $S^(-1)R$ denote the ring of quotients of $R$
with respect to $S$. Likewise, for each $R$-module $M$ we may form the module of
quotients $S^(-1)M$, which we always identify with $S^(-1)R times.o_R M$ (as in
§@ss:localization). There is then an $R$-homomorphism
$ i:M arrow S^(-1)R times.o_R M=S^(-1)M, $
<eq:module-localization-map>
given by $m mapsto 1 times.o m=m slash 1$, $m in M$. The kernel of $i$ is
precisely the $S$-torsion submodule of $M$.

We wish to establish a connection between the $R$-submodules of $M$ and the
$S^(-1)R$-submodules of $S^(-1)M$, and begin with a definition which generalizes
the earlier concept of purity:

#source(549)
#definition[
  Let $S$ be a multiplicative subset of the commutative ring $R$, and let
  $L subset.eq M$ be an inclusion of $R$-modules. Call $L$ an _$S$-saturated_
  submodule of $M$ if $M slash L$ is $S$-torsionfree, or equivalently, if
  $ s m in L,s in S,m in M arrow.double m in L. $
] <def:saturated-submodule>
#idx("saturated", target: [@def:saturated-submodule])
#idx("saturated submodule", target: [@def:saturated-submodule])

#proposition[
  Let $M$ be an $R$-module, and let $i:M arrow S^(-1)M$ be the canonical
  $R$-homomorphism defined in @eq:module-localization-map. Then there is an
  inclusion-preserving bijection $L arrow.l.r X$ between the set of
  $S$-saturated $R$-submodules $L$ of $M$, and the set of $S^(-1)R$-submodules
  $X$ of $S^(-1)M$, given by
  $ X=S^(-1)L,quad L=i^(-1) lr((X)). $
] <prop:saturated-localized-submodule-correspondence>
#proof[
  Starting with any $S$-saturated $L subset.eq M$, put $X=S^(-1)L$, an
  $S^(-1)R$-submodule of $S^(-1)M$. Clearly, $L subset.eq i^(-1) lr((X))$, and
  we must prove equality. If $m in M$ is such that $i(m) in X$, then we may
  write
  $ m slash 1=l slash s "for some" l in L,s in S. $
  Hence $s's m=s'l$ for some $s' in S$, so $s's m in L$. Since $L$ is
  $S$-saturated in $M$, it follows that $m in L$. This completes the proof that
  $L=i^(-1) lr((S^(-1)L))$.

  Conversely, given an $S^(-1)R$-submodule $X$ of $S^(-1)M$, define
  $L=i^(-1) lr((X))$. Then $L$ is an $R$-submodule of $M$, and clearly
  $S^(-1)L subset.eq X$. We claim that equality holds; indeed, given $x in X$ we
  may write $x=m slash s$, $m in M$, $s in S$. Then also $m slash 1 in X$,
  whence $m in L$, so $x in S^(-1)L$. This shows that $S^(-1)L=X$. Finally, we
  verify that $L$ is $S$-saturated in $M$. If $s m in L$, where $s in S$ and
  $m in M$, then $s m slash 1 in X$. Therefore $m slash 1 in X$, so $m in L$, as
  desired. This completes the proof.
]

#corollary[
  Keep the above notation. If $M$ is a noetherian $R$-module, then $S^(-1)M$ is
  a noetherian $S^(-1)R$-module. If $R$ is a noetherian ring, so is $S^(-1)R$.
  The corresponding results hold when “noetherian” is replaced by “artinian”.
] <cor:localization-chain-conditions>

Suppose now that $Lambda$ is an $R$-algebra, where $R$ is any commutative ring,
and let $S$ be a multiplicative subset of $R$. Define
$ S^(-1)Lambda=S^(-1)R times.o_R Lambda, $
which is clearly an $S^(-1)R$-algebra. Each left $Lambda$-module $M$ gives rise
to an $S^(-1)Lambda$-module $S^(-1)M$, and clearly
$ S^(-1)M=S^(-1)R times.o_R M tilde.equiv S^(-1)Lambda times.o_Lambda M. $
If $M$ is f.g./$R$, then $S^(-1)M$ is f.g./$S^(-1)R$. If $M$ is $R$-projective,
then $S^(-1)M$ is $(S^(-1)R)$-projective; this follows at once from the fact
that if $M$ is $R$-free, then $S^(-1)M$ is $S^(-1)R$-free. In particular, if $M$
is any $Lambda$-lattice then $S^(-1)M$ is an $S^(-1)Lambda$-lattice.

#source(550)
As an immediate consequence of
@prop:saturated-localized-submodule-correspondence, we obtain:

#proposition[
  Let $S$ be a multiplicative subset of the commutative ring $R$, and let
  $Lambda$ be any $R$-algebra. Let $M$ be a left $Lambda$-module. Then there is
  an inclusion-preserving bijection $L arrow.l.r X$ between the set of
  $S$-saturated $Lambda$-submodules $L$ of $M$, and the set of
  $S^(-1)Lambda$-submodules $X$ of $S^(-1)M$. This bijection is given by
  $ X=S^(-1)L,quad L=i^(-1) lr((X))={m in M:m slash 1 in X}. $
] <prop:saturated-order-module-correspondence>

We have seen above that each $Lambda$-module $M$ gives rise to an
$S^(-1)Lambda$-module $S^(-1)M$. We may ask, conversely, whether every
$S^(-1)Lambda$-module can be obtained in this way. For our purposes, it will
suffice to restrict our attention to f.g. modules. The following result,
extremely useful in practice, settles the above question completely:

#proposition[
  Let $S$ be a multiplicative subset of the commutative ring $R$, and let
  $Lambda$ be any $R$-algebra. Then each f.g. left $S^(-1)Lambda$-module $X$
  contains a f.g. left $Lambda$-module $M$ such that
  $
    S^(-1)Lambda times.o_Lambda M tilde.equiv S^(-1)R times.o_R M
    tilde.equiv (S^(-1)R) dot M=X,
  $
  where $(S^(-1)R) dot M$ is computed inside $X$.
] <prop:localized-module-finite-model>
#proof[
  The canonical ring homomorphism $Lambda arrow S^(-1)Lambda$ is not necessarily
  an injection, but it nevertheless allows us to view each $S^(-1)Lambda$-module
  $X$ as a $Lambda$-module. Each $x in X$ then generates a $Lambda$-submodule
  $Lambda x$ of $X$. Now let $X=sum_(i=1)^k S^(-1)Lambda x_i$, and choose
  $M=sum Lambda x_i subset.eq X$. Clearly $X=(S^(-1)R) dot M$, and we need only
  show that the surjection
  $ f:S^(-1)R times.o_R M arrow (S^(-1)R) dot M $
  is injective. For this purpose, it suffices to define a map
  $g:(S^(-1)R)M arrow S^(-1)R times.o_R M$ for which $g f$ is the identity map.
  In order to define $g$, we note that each element $y in (S^(-1)R)M$ is of the
  form $y=s^(-1)m$ with $s in S$, $m in M$. Let us set
  $ g(y)=s^(-1) times.o m in S^(-1)R times.o_R M. $
  If also $y=t^(-1)n$ with $t in S$, $n in M$, then $s^(-1)m=t^(-1)n$ in $X$.
  Therefore $t m=s n$ in $M$, and so
  $
    s^(-1) times.o m=(s t)^(-1)t times.o m=(s t)^(-1) times.o t m
    =(s t)^(-1) times.o s n=t^(-1) times.o n.
  $
  This proves that $g$ is well defined, and it is obvious that $g f$ is the
  identity map, so the proof is complete.
]

#source(551)
Let us apply this machinery to the study of orders. Suppose now that $R$ is a
Dedekind domain with quotient field $K$, and let $Lambda$ be an $R$-order in
$A$. Given a multiplicative subset $S$ of $R$, we may form the $S^(-1)R$-algebra
$S^(-1)Lambda$. Clearly
$
  K times.o_(S^(-1)R) S^(-1)Lambda
  =K times.o_(S^(-1)R)(S^(-1)R times.o_R Lambda)
  tilde.equiv K times.o_R Lambda=A,
$
so $S^(-1)Lambda$ is a subring of $A$ which spans $A$ over $K$. Further,
$S^(-1)Lambda$ is f.g./$S^(-1)R$, and $S^(-1)R$ is contained in the center of
$S^(-1)Lambda$. Thus, $S^(-1)Lambda$ is an $S^(-1)R$-order in $A$. We note that
the canonical map $Lambda arrow S^(-1)Lambda$ is an injection, since $Lambda$ is
$S$-torsionfree. Each $Lambda$-module $M$ gives rise to an $S^(-1)Lambda$-module
$S^(-1)M$. The remarks preceding @prop:saturated-order-module-correspondence
show that if $M$ is a $Lambda$-lattice, then $S^(-1)M$ is an
$S^(-1)Lambda$-lattice.

In the special case where $S=R-{0}$, we note that a $Lambda$-sublattice $L$ of a
$Lambda$-lattice $M$ is $S$-saturated in $M$ if and only if $L$ is an $R$-pure
submodule of $M$. It follows at once that
@prop:pure-order-sublattice-correspondence is a special case of Proposition
@prop:saturated-order-module-correspondence. Furthermore, from
@prop:localized-module-finite-model we obtain:

#corollary[
  Let $Lambda$ be an $R$-order, where $R$ is a Dedekind domain with quotient
  field $K$, and let $S$ be any multiplicative subset of $R$. Then each
  $S^(-1)Lambda$-lattice $X$ contains a $Lambda$-lattice $M$ such that
  $ S^(-1)M tilde.equiv (S^(-1)Lambda) dot M=X. $
] <cor:localized-lattice-finite-model>
#proof[
  The $S^(-1)Lambda$-lattice $X$ is $S^(-1)R$-torsionfree, hence certainly
  $R$-torsionfree. The $Lambda$-module $M$ constructed in the proof of
  @prop:localized-module-finite-model is f.g. and torsionfree as $R$-module, and
  is therefore a $Lambda$-lattice, as desired.
]

Even the special case of the above, in which $S=R-{0}$, is extremely useful.
From @prop:pure-order-sublattice-correspondence and
@cor:localized-lattice-finite-model, we obtain:

#corollary[
  Let $Lambda$ be an $R$-order in the $K$-algebra $A$. Then every f.g. left
  $A$-module $V$ is of the form $V=K dot M$ for some full $Lambda$-lattice $M$
  in $V$. Further, for each $A$-submodule $W$ of $V$, $M slash (M inter W)$ is a
  full $Lambda$-lattice in $V slash W$.
] <cor:full-order-lattice-existence>

Let us derive several important consequences of this rather simple result. We
begin with:

#proposition[
  Let $R$ be a P.I.D. with field of quotients $K$, and let $Lambda$ be an
  $R$-order in a $K$-algebra $A$. Let $V$ be a f.g. left $A$-module. Then $V$
  has a $K$-basis, relative to which each $x in Lambda$ is represented by a
  matrix over $R$. In short, every $K$-representation of $Lambda$ is equivalent
  to an $R$-representation of $Lambda$.
] <prop:field-representation-integral-form>
#proof[
  We may write $V=K dot M tilde.equiv K times.o_R M$ for some full
  $Lambda$-lattice $M$ in $V$. Since $R$ is a P.I.D., $M$ has a free $R$-basis
  ${m_1,dots,m_d}$. This is also a $K$-basis of $V$. Relative to this basis, we
  obtain an $R$-representation of $Lambda$ as in
  @eq:lattice-representation-coefficients. This completes the proof.
]

#source(552)
Even when $R$ is not a principal ideal domain, it is sometimes possible to
choose an $R$-free $Lambda$-lattice spanning a given $A$-module. In order to
determine whether a given $Lambda$-lattice $M$ is $R$-free, we can use
Steinitz’s Theorem @th:steinitz on the structure of $R$-lattices. Specifically,
we may express $M$ as an external direct sum of (nonzero) ideals of $R$, say
$M=product_(i=1)^d J_i$. Then $M$ is $R$-free if and only if the product
$J_1 dots J_d$ is a _principal ideal_ (that is, an ideal of the form $R x$ for
some nonzero $x in K$). If $M$ is not $R$-free, we may let $J$ be an arbitrary
ideal of $R$, and form the $Lambda$-lattice $J M$. Clearly
$ J M=product_(i=1)^d J J_i, $
and $J M$ will be $R$-free if and only if $product_1^d J J_i$ is a principal
ideal, that is, if and only if the ideal $J^d dot product J_i$ is principal. We
use this to prove a beautiful theorem due to Schur, which generalizes the
preceding proposition.

#theorem(title: [Schur])[
  Let $R$ be a Dedekind domain with field of quotients $K$, and suppose that the
  ideal class number $h$ of $R$ is finite. Let $Lambda$ be an $R$-order in a
  $K$-algebra $A$, and let $V$ be a f.g. left $A$-module with $dim_K V=d$.
  Assume that $d$ is relatively prime to $h$. Then $V$ contains an $R$-free full
  $Lambda$-lattice $M$. If ${m_1,dots,m_d}$ is a free $R$-basis for $M$, it is
  also a $K$-basis of $V$. Relative to this basis, $V$ affords an
  $R$-representation of $Lambda$.
] <th:schur-integral-form-class-number>
#idx("Schur's Theorem", target: [@th:schur-integral-form-class-number])
#proof[
  By @cor:full-order-lattice-existence, $V$ contains a full $Lambda$-lattice
  $M$. As pointed out in the discussion preceding the theorem, we may write
  $M=product_(i=1)^d J_i$, and it suffices to find an $R$-ideal $J$ such that
  $J^d dot product_(i=1)^d J_i$ is principal. But $(d,h)=1$, so as $J$ ranges
  over a full set of ideal class representatives, so does $J^d$. Hence we can
  choose $J$ so that $J^d dot product_(i=1)^d J_i$ is a principal ideal, and the
  proof is finished.
]

Let us show by example that we cannot omit the hypothesis that $(h,d)=1$. Let
$R$ be a Dedekind domain whose class number $h$ is greater than 1, and let
$V tilde.equiv K^((h))$, $A=End_K lr((V))$, so we view $V$ as an
$(A,K)$-bimodule. Pick any full $R$-lattice $M$ in $V$, and let
$Lambda=End_R lr((M))$. Then $M$ is a $(Lambda,R)$-bimodule, and is a full
$Lambda$-lattice in $V$. Let us show that for any other full $Lambda$-lattice
$N$ in $V$, we have $N=M frak(a)$ for some nonzero $R$-ideal $frak(a)$ in $K$.

Let $P$ range over the maximal ideals of $R$, and let the subscript $P$ denote
localization. Then $Lambda_P=End_(R_P) lr((M_P))$, and $M_P$ is $R_P$-free on
$h$ generators. Hence $Lambda_P$ is a maximal $R_P$-order in $A$ (see
@bib:Reiner1975[MO, (8.7)]). But then $M_P tilde.equiv N_P$ as
$Lambda_P$-lattices by @bib:Reiner1975[MO (18.7)], and this isomorphism extends
to an $A$-automorphism of $V$. However, $End_A lr((V)) tilde.equiv K$, so there
exists a nonzero element $alpha_P in K$ such that $N_P=M_P alpha_P$. Further
$N_P=M_P$ a.e., so we may choose $alpha_P=1$ a.e. We now let $frak(a)$ be the
$R$-ideal of $K$ for which $frak(a)_P=R_P alpha_P$ for each $P$\; explicitly,
choose $frak(a)=inter.big_P R_P alpha_P$, an ideal with the desired properties
#source(553)
by @prop:localization-completion-lattices(vii). Then $M frak(a)$ is a left
$Lambda$-lattice in $V$ such that $(M frak(a))_P=N_P$ for all $P$, whence
$M frak(a)=N$ by @prop:localization-completion-lattices(vi).

Now let $M$ be chosen so that $M$ is _not_ $R$-free; for example, let
$V=plus.o.big_1^h K v_i$, and pick
$ M=plus.o.big_1^(h-1) R v_i plus.o frak(q) v_h, $
where $frak(q)$ is some non-principal ideal of $R$. Then we claim that $V$ does
not contain full $R$-free $Lambda$-lattices. Indeed, any $Lambda$-lattice $N$ in
$V$ is of the form $N=M frak(a)$, with $frak(a)$ an $R$-ideal in $K$. The
Steinitz class of $N$ is the ideal class of $frak(a)^h frak(q)$; but $frak(a)^h$
is principal, since $h$ is the ideal class number of $R$. Hence the Steinitz
class of $N$ is not the principal class, and so $N$ cannot be $R$-free. Thus we
see that if $Lambda=End_R lr((M))$, where $M$ is any non-$R$-free lattice, then
the $A$-module $V$ cannot contain an $R$-free $Lambda$-lattice $N$ for which
$K dot N=V$.

The preceding example shows that when $Lambda$ is an $R$-order, where $R$ is not
a P.I.D., then there exist $K$-representations of $Lambda$ which are not
$K$-equivalent to $R$-representations. There are several ways of overcoming this
difficulty, in practice. One procedure, followed in
Chapter~@ch:modular-representations, is to work over d.v.r.’s rather than
arbitrary Dedekind domains. This is an especially useful approach, since a
d.v.r. is even easier to handle than an arbitrary P.I.D. A second procedure,
used repeatedly in integral representation theory, is to study a
$Lambda$-lattice $M$ by investigating its localizations $M_P$, with $P$ ranging
over the maximal ideals of $R$. Since $R_P$ is a d.v.r., every
$Lambda_P$-lattice necessarily has an $R_P$-basis.

To conclude this section, we consider yet another approach, that of ground ring
extension. Let $Lambda$ be an $R$-order, where $R$ is an arbitrary Dedekind
domain. We hope to find an extension field $K'$ of $K$, with ring of integers
$R'$, such that every $K$-representation of $Lambda$ is $K'$-equivalent to an
$R'$-representation of $Lambda$. This can always be done when $R$ has finite
class number, as we now show:

#theorem[
  Let $R$ be a Dedekind domain whose class number $h$ is finite, and let $K$ be
  its field of quotients. Then there exists an extension field $K'$ of $K$ with
  $dim_K K' <= h$, such that for each $R$-order $Lambda$, every
  $K$-representation of $Lambda$ is $K'$-equivalent to an $R'$-representation of
  $Lambda$, where $R'$ is the integral closure of $R$ in $K'$.
] <th:integral-form-principalizing-extension>
#proof[
  Let $A=K Lambda$, and let $V$ be a f.g. $A$-module affording a
  $K$-representation of $Lambda$. If $V$ happens to contain an $R$-free full
  $Lambda$-lattice, then of course the $K$-representation of $Lambda$ is
  $K$-equivalent to an $R$-representation. However, $V$ need not contain such a
  $Lambda$-lattice, so instead we consider the $K'$-representation of $Lambda$
  afforded by the $K'$-space $K' times.o_K V$. Denote this space by $K'V$, after
  the obvious identification of $V$ with $1 times.o V$. We must show that (with
  suitably chosen $K'$), the space $K'V$ contains an $R'$-free $Lambda$-module.

  #source(554)
  To begin with, we may choose $K'$ so that $dim_K K' <= h$, and such that each
  $R$-ideal $frak(a)$ of $K$ generates a principal $R'$-ideal of $K'$ (that is,
  $R'frak(a)=R'alpha$ for some $alpha in K'$); this is proved in
  @bib:CurtisReiner1962[CR (20.14)], and we shall not repeat the proof here.
  Note that $K'$ is chosen once and for all, independently of the order
  $Lambda$. Now let $M$ be a full $Lambda$-lattice in $V$ (see
  @cor:full-order-lattice-existence). By Steinitz’s Theorem @th:steinitz, we
  have
  $ M=plus.o.big_(i=1)^n frak(a)_i m_i,quad n=dim_K V, $
  where each $frak(a)_i$ is an $R$-ideal in $K$, and each $m_i in M$. Then in
  $K'V$ we have
  $
    R' times.o_R M=plus.o.big_(i=1)^n (R'frak(a)_i)m_i
    =plus.o.big_(i=1)^n (R'alpha_i)m_i
  $
  for some elements ${alpha_i}$ of $K'$. Thus $K'V$ contains an $R'$-free
  $Lambda$-module. Relative to the basis ${alpha_1 m_1,dots,alpha_n m_n}$, $K'V$
  affords an $R'$-representation of $Lambda$. This completes the proof.
]

#remark(numbered: false)[
  If $K$ is an algebraic number field, it is known from class field theory that
  there exists a finite Galois extension $K'$ of $K$, whose Galois group is
  isomorphic to the ideal class group of $R$ (and hence is abelian), such that
  every ideal of $R$ generates a principal ideal of $R'$. For this abelian
  extension $K'$ of $K$, we have $dim_K K'=h$. The above proof shows that every
  representation of $Lambda$ by matrices over $K$ is $K'$-equivalent to a
  representation by matrices over $R'$.
]

#exercises-heading

Throughout, let $R$ be a Dedekind domain with field of quotients $K$, and let
$A$ be a f.d. $K$-algebra.

#exercise[
  Let $Lambda$ be an $R$-order in a semisimple $K$-algebra $A$, and let $M$ be a
  left $Lambda$-lattice. Show that $M$ can be embedded in a free left
  $Lambda$-module with a finite basis.

  #hint([@exc:lattice-embedding-finite-free-order-module])[
    The left $A$-module $K M$ is a direct summand of a free module $A^((k))$ for
    some finite $k$, since $A$ is semisimple. There are embeddings
    $M arrow K M$, $K M arrow A^((k))$. Hence there is an embedding
    $M arrow K dot Lambda^((k))$, and then $alpha M subset.eq Lambda^((k))$ for
    some nonzero $alpha in R$.
  ]
] <exc:lattice-embedding-finite-free-order-module>

#exercise[
  Let $Lambda subset.eq Gamma$ be $R$-orders in $A$. Each $Gamma$-lattice is
  also a $Lambda$-lattice. Show that for any $Gamma$-lattices $M$ and $N$,
  $
    Hom_Gamma lr((M,N))={f in Hom_A lr((K M,K N)):f(M) subset.eq N}
    =Hom_Lambda lr((M,N)).
  $
  Deduce that $M tilde.equiv N$ as $Gamma$-lattices if and only if
  $M tilde.equiv N$ as $Lambda$-lattices. Show that $M$ is indecomposable as
  $Gamma$-lattice if and only if $M$ is indecomposable as $Lambda$-lattice.
] <exc:overorder-lattice-homomorphisms>

#source(555)
#exercise[
  Let $Lambda$ be an $R$-order in $A$, and $M$ a full left $Lambda$-lattice in a
  f.g. left $A$-module $V$. Given an $A$-composition series for $V$:
  $ V=V_0 supset V_1 supset dots supset V_n=0, $
  put $M_i=M inter V_i$, $0 <= i <= n$. Using @cor:full-order-lattice-existence,
  show that the decreasing chain of $Lambda$-lattices
  $ M=M_0 supset M_1 supset dots supset M_n=0 $
  has the following properties:

  #enum(
    numbering: "(i)",
    [For each $i$, $M_i$ is a full $Lambda$-lattice in $V_i$.],
    [
      For each $i$, the factor module $M_(i-1) slash M_i$ is a full
      $Lambda$-lattice in the $A$-module $V_(i-1) slash V_i$.
    ],
  )
] <exc:order-lattice-composition-series>

#exercise[
  Keep the above notation; the factor modules ${M_(i-1) slash M_i:1 <= i <= n}$
  are called the _$R$-composition factors_ of the lattice $M$. Show that when
  $R$ is not a field, these are _never_ composition factors of the
  $Lambda$-module $M$ in the usual sense. Show further that the $R$-composition
  factors of $M$ are not necessarily uniquely determined up to isomorphism and
  order of occurrence.

  #hint([@exc:order-lattice-composition-factor-nonuniqueness])[
    See @bib:CurtisReiner1962[CR (73.28)].
  ]
] <exc:order-lattice-composition-factor-nonuniqueness>
#idx(
  "R-composition factors",
  target: [@exc:order-lattice-composition-factor-nonuniqueness],
)

#exercise[
  Let $Lambda$ be an $R$-order in $A$, and suppose that for each simple
  $A$-module $V$, all full $Lambda$-lattices in $V$ are mutually isomorphic.
  (This condition is satisfied, for instance, when $R$ is a d.v.r. and $Lambda$
  is a maximal $R$-order in a f.d. separable $K$-algebra $A$\; see
  @bib:Reiner1975[MO (18.10)].) Show that for each $Lambda$-lattice $M$, the
  $R$-composition factors of $M$ are uniquely determined (up to isomorphism and
  order of occurrence).
] <exc:order-lattice-composition-factor-uniqueness>

#exercise[
  Let $V$ be a f.g. left $A$-module with no repeated $A$-composition factors,
  and let $M$ be a full $Lambda$-lattice in $V$. Let ${N_1,dots,N_t}$ and
  ${N'_1,dots,N'_t}$ be two sets of $R$-composition factors of $M$, listed in
  the order of their respective series, and assume that
  $K N_i tilde.equiv K N'_i$ for each $i$. Show that $N_i tilde.equiv N'_i$ for
  each $i$.

  #hint([@exc:multiplicity-free-lattice-composition-factors])[
    See @bib:CurtisReiner1962[CR (73.13)].
  ]
] <exc:multiplicity-free-lattice-composition-factors>

#exercise[
  Let $Lambda subset Gamma$ be any pair of $R$-orders in a f.d. $K$-algebra $A$.
  Show that the map $Gamma times.o_Lambda Gamma arrow Gamma$, given by
  $x times.o y mapsto x y$, need not be a monomorphism. This provides an example
  of a left $Lambda$-lattice $M$ for which $Gamma times.o_Lambda M$ is not
  isomorphic to the product $Gamma M$ computed inside $K M$.

  #hint([@exc:overorder-tensor-product-kernel])[
    Let $I$ be a two-sided $Gamma$-ideal in $Lambda$ such that $K dot I=A$, and
    set $overline(Lambda)=Lambda slash I$, $overline(Gamma)=Gamma slash I$.
    There is a left $Lambda$-homomorphism
    $theta:Gamma times.o_Lambda Gamma arrow
    overline(Gamma) times.o_overline(Lambda)(Gamma slash Lambda)$, given by
    $x times.o y mapsto overline(x) times.o overline(y)$. For
    $x in Gamma-Lambda$ we have
    $
      theta(1 times.o x-x times.o 1)
      =overline(1) times.o overline(x)-overline(x) times.o overline(1)
      =overline(1) times.o overline(x),
    $
    since $overline(x) times.o overline(1)=0$ in $Gamma slash Lambda$ because
    $1 in Lambda$. But $1 times.o x-x times.o 1 in Gamma times.o Gamma$ is an
    element with image 0 in $Gamma$, so it suffices to choose
    $x in Gamma-Lambda$ with $overline(1) times.o overline(x)!=0$ in
    $overline(Gamma) times.o_overline(Lambda)(Gamma slash Lambda)$. Now the map
    $overline(Lambda) times.o (Gamma slash Lambda) arrow
    overline(Gamma) times.o (Gamma slash Lambda)$ is monic whenever
    $Gamma slash Lambda$ is $overline(Lambda)$-flat, and in this case any
    #source(556)
    $x in Gamma-Lambda$ will work. Thus, it suffices to give an example where
    $overline(Lambda)$ is a field. Take $Gamma=ZZ[a]$, $Lambda=ZZ[2a]$,
    $I=2Gamma$ where $a=sqrt(3)$. Then
    $overline(Lambda)=Lambda slash I=(ZZ plus.o 2a ZZ) slash
    (2ZZ plus.o 2a ZZ) tilde.equiv ZZ slash 2ZZ$. This exercise is due to J.
    Rotman.
  ]
] <exc:overorder-tensor-product-kernel>

#exercise[
  Keep the notation of Exercise~@exc:overorder-tensor-product-kernel, and let
  $M$ be a $Lambda$-lattice. Let
  $ mu:Gamma times.o_Lambda M arrow Gamma M $
  be the $Gamma$-homomorphism defined by $gamma times.o m mapsto gamma m in
  Gamma M$, where $Gamma M$ is calculated inside $K M$. Find $ker mu$.

  #hint([@exc:overorder-tensor-tor-kernel])[
    There is an exact sequence $0 arrow Gamma arrow A arrow T arrow 0$, with $T$
    an $R$-torsion $Lambda$-module. Then
    $
      op("Tor")(A,M) arrow^phi op("Tor")(T,M)
      arrow Gamma times.o M arrow^psi A times.o M
    $
    is exact, where Tor is $op("Tor")_1^Lambda$ and $times.o$ is
    $times.o_Lambda$. Since $A=K times.o_R Lambda$ is flat as a right
    $Lambda$-module, $op("Tor")(A,M)=0$. Exactness therefore identifies
    $op("Tor")(T,M)$ with $ker psi$. Under the identification
    $A times.o_Lambda M tilde.equiv K M$, the map $psi$ is $mu$ followed by the
    inclusion $Gamma M arrow K M$. Thus
    $ker mu=ker psi tilde.equiv op("Tor")(T,M)$.#ed-note[
      Divisibility and torsion alone do not imply that a homomorphism is zero,
      as $QQ arrow QQ slash ZZ$ shows. Here the required vanishing follows from
      flatness of the localization $A$ as a right $Lambda$-module.
    ]
  ]
] <exc:overorder-tensor-tor-kernel>

#exercise[
  Let $L$ be a finite separable extension of $K$, and let $S$ be the integral
  closure of $R$ in $L$. Let $Lambda$ be an $S$-order in a f.d. $L$-algebra $A$.
  Then $Lambda$ is also an $R$-order in $A$. Show that $Lambda$-lattices
  relative to $S$ are also $Lambda$-lattices relative to $R$, and conversely.

  #hint([@exc:lattices-integral-base-change])[
    It suffices to show that an $R$-torsionfree $Lambda$-module $M$ is
    necessarily $S$-torsionfree. Suppose that $s in S$, $m in M$, and that
    $s m=0$ but $s!=0$. By Exercise~@exc:integral-adjugate-element, we may
    choose $s' in S$ so that $s's=N_(L slash K) lr((s))$. Then $s's in R$,
    $s's!=0$, and $s's m=0$, which implies that $m=0$ since $M$ is
    $R$-torsionfree.
  ]
] <exc:lattices-integral-base-change>

