#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/33-finite-representation-type.typ": (
  dade-reduction-diagrams, lattice-cover-morphism-diagram,
  lattice-reconstruction-diagram, quotient-triple-lifting-diagram,
  single-branch-pullback-diagram, triple-morphism-diagram,
)

== Finite Representation Type <sec:finite-representation-type>

Throughout this section, $Lambda$ denotes an $R$-order in a separable
$K$-algebra $A$, where $K$ is a global field or the completion of a global
field, and $R$ is a Dedekind domain with quotient field $K$. As usual, we assume
that $R != K$. These hypotheses imply that $R slash frak(a)$ is finite for every
nonzero ideal $frak(a)$ of $R$, and that the Jordan-Zassenhaus Theorem holds for
$Lambda$-lattices (see introduction to §@ss:genus-basic-properties). Let
$n(Lambda)$ denote the number of isomorphism classes of indecomposable left
$Lambda$-lattices. We say that $Lambda$ has _finite representation type_ #idx(
  "finite representation type",
) if $n(Lambda)$ is finite, and _infinite representation type_ #idx(
  "infinite representation type",
) otherwise. Given an $R$-order $Lambda$, one would like to know all
indecomposable $Lambda$-lattices (up to isomorphism), since every
$Lambda$-lattice is expressible as a finite direct sum of indecomposable
lattices. As a first approximation to solving this problem, we may try to check
whether $n(Lambda)$ is finite. Once this is done, there remains the more
difficult problem of finding a full set of indecomposable $Lambda$-lattices. We
devote this section to a discussion of the first of these questions.

#source(709)
(Let us comment briefly about our restrictions on the field $K$ and the algebra
$A$. These hypotheses are imposed in order to guarantee that the
Jordan-Zassenhaus Theorem hold true for $Lambda$-lattices (see
§@sec:jordan-zassenhaus). In more general situations, where $K$ is not a global
field or where $A$ is not a separable $K$-algebra, it may happen that the
Jordan-Zassenhaus Theorem is not valid for $Lambda$-lattices. In such cases, it
is easily seen that $n(Lambda)$ must be infinite. To prove this, suppose that
$n(Lambda)$ is finite. A $Lambda$-lattice $M$ of $R$-rank $t$ is a direct sum of
at most $t$ indecomposable summands. If $n(Lambda)$ is finite, there are
finitely many isomorphism classes of such indecomposable summands, and hence
only finitely many classes of $M$'s. Thus, if the Jordan-Zassenhaus Theorem
fails for $Lambda$-lattices, then $n(Lambda)$ is necessarily infinite.
Therefore, in investigating whether $n(Lambda)$ is finite, it is reasonable to
restrict our attention to those cases where we know in advance that the
Jordan-Zassenhaus Theorem is valid.)

#heading(level: 3)[
  Jones' Theorem. Jacobinski's Criterion for Group Rings
] <ss:jones-jacobinski-finite-type>

In this subsection we shall show that the question, as to whether $Lambda$ has
finite representation type, can be decided by answering the local question at
some finite set of primes $P$ of $R$. For each maximal ideal $P$ of $R$, let the
subscript $P$ denote _completion_, rather than localization. As in
@eq:nonmaximal-order-primes, let
$
  S(Lambda)={P:Lambda_P != "maximal" R_P "-order in" A_P},
$
so $S(Lambda)$ is a finite set. Further, $S(Lambda)=nothing$ if and only if
$Lambda$ is a maximal order. This latter case is completely settled by:

#proposition[
  Let $Lambda$ be any hereditary or maximal order. Then the number $n(Lambda)$
  of non-isomorphic indecomposable $Lambda$-lattices is finite, and equals the
  number of isomorphism classes of full $Lambda$-lattices in simple $A$-modules.
] <prop:hereditary-order-finite-type>

#proof[
  This follows from @th:maximal-orders-are-hereditary and the Jordan-Zassenhaus
  Theorem.
]

For the rest of the discussion, we may assume that $S(Lambda) != nothing$. Our
main result, due to Jones~@bib:Jones1963a, is as follows:

#theorem[
  Let $Lambda$ be an $R$-order in a f.d. separable $K$-algebra $A$, where $K$ is
  a global field. Let $n(Lambda)$ be the number of non-isomorphic indecomposable
  left $Lambda$-lattices, and let $S(Lambda)$ be as above. Then #idx(
    "Jones' Theorem",
    target: [@th:jones-finite-type-completions],
  )
  $
    n(Lambda)<infinity <=> n(Lambda_P)<infinity
    "for each" P in S(Lambda).
  $
] <th:jones-finite-type-completions>

#proof[
  _Step 1._ If $n(Lambda)<infinity$, let ${M_i:1 <= i <= n}$ be a full set of
  non-isomorphic indecomposable left $Lambda$-lattices. Let $P$ be any maximal
  ideal of $R$, and let $X$ be an indecomposable $Lambda_P$-lattice. We shall
  show that $X divides (M_i)_P$ for
  #source(710)
  some $i$, whence $n(Lambda_P)<infinity$ by the K-S-A Theorem. To prove our
  assertion, first choose an $A$-module $Y_0$ such that $K_P X plus.o Y_0$ is
  $A_P$-free, say equal to $F_P$ for some f.g. free $A$-module $F$. By
  @cor:full-order-lattice-existence we may write $Y_0=K_P Y$ for some full
  $Lambda_P$-lattice $Y$ in $Y_0$. Therefore
  $ K_P lr((X plus.o Y)) tilde.equiv K_P F "as" A_P "-modules". $
  Let us treat this isomorphism as an identification, and now set
  $L=(X plus.o Y) inter F$. Then $L$ is a lattice over the localization of
  $Lambda$ at $P$, and $L_P=X plus.o Y$ by the proof of Heller's
  Theorem~@th:heller-completion-krull-schmidt. But this $L$ is the localization
  of some $Lambda$-lattice $M$, by @cor:localized-lattice-finite-model, and thus
  we have $X plus.o Y tilde.equiv M_P$. Since $M$ is a direct sum of $M_i$'s
  with various multiplicities, we deduce from @cor:krull-schmidt-summands that
  $X divides (M_i)_P$ for some $i$. This completes the proof that if
  $n(Lambda)<infinity$, then $n(Lambda_P)<infinity$ for each $P$.

  _Step 2._ Suppose now that $n(Lambda_P)=n_P<infinity$ for each
  $P in S(Lambda)$. As pointed out above, $n(Lambda)<infinity$ if $S(Lambda)$ is
  empty, so assume for the rest of the proof that $S(Lambda)$ is not empty. For
  each $P in S(Lambda)$, let ${X_1^P,dots,X_(n_P)^P}$ be a full set of
  non-isomorphic indecomposable $Lambda_P$-lattices, and let
  $n=sum_(P in S(Lambda)) n_P$. Let $C$ denote the additive semigroup of
  $n$-tuples of non-negative integers, and partially order $C$ by writing
  $(a_i) <= (b_i)$ in $C$ if $a_i <= b_i$ for $1 <= i <= n$. We shall show in
  Step 3 that relative to this partial order, every non-empty subset of $C$ has
  only a finite number of minimal elements. Let us take this for granted for the
  moment, and proceed with the argument.

  Let $M$ be a $Lambda$-lattice, and let $r(j,P)$ denote the multiplicity of
  $X_j^P$ as a direct summand of $M_P$, for $1 <= j <= n_P$ and all
  $P in S(Lambda)$. Let $theta(M)$ denote the ordered $n$-tuple in $C$ whose
  entries are the non-negative integers ${r(j,P)}$. Let $C'$ be the subsemigroup
  of $C$ consisting of all elements $theta(M)$, where $M$ ranges over all
  $Lambda$-lattices, and partially order $C'$ according to the ordering on $C$.
  If $N$ is a $Lambda$-lattice such that $N divides M$, then clearly
  $theta(N) <= theta(M)$ with equality if and only if $M or.curly N$.
  Conversely, let $N$ be a $Lambda$-lattice such that $theta(N)<theta(M)$. By
  @th:genus-local-direct-summand we have $M tilde.equiv N' plus.o L$ for some
  $N'$ in the genus of $N$, and some $Lambda$-lattice $L$. Note that
  $theta(N')=theta(N)$, and thus $theta(M)=theta(N')+theta(L)$. It follows at
  once that a nonzero $Lambda$-lattice $M$ is indecomposable if and only if
  $theta(M)$ is a minimal element in the partially ordered subset $C' - {0}$. In
  Step 3, we shall show that this subset has only finitely many minimal
  elements. Further, given such an element $theta_0 in C' - {0}$, the condition
  that $theta(M)=theta_0$ places an upper bound on the $R$-rank of $M$; hence by
  the Jordan-Zassenhaus Theorem, the number of non-isomorphic $M$'s with
  $theta(M)=theta_0$ is finite. Once we know that the number of minimal elements
  $theta_0$ in $C' - {0}$ is finite, we will have shown that
  $
    n(Lambda_P)<infinity "for all" P in S(Lambda)
    => n(Lambda)<infinity,
  $
  as desired.

  #source(711)
  _Step 3._ Let us prove finally that each non-empty subset $D$ of $C$ has a
  finite number of minimal elements, relative to the ordering introduced above.
  We use induction on $n$, where $n=sum n_P$ as above. The result is obvious
  when $n=1$, so let $n>1$, and assume the result true at $n-1$. Let
  $(d_1,dots,d_n)$ be some fixed element of $D$. Put
  $
    D(m,i)={(a_1,dots,a_n) in D:a_i=m},
    1 <= i <= n,m in ZZ,m >= 0.
  $
  For each $m$ and $i$, the partially ordered set $D(m,i)$ has finitely many
  minimal elements by the induction hypothesis (except that possibly $D(m,i)$
  may be empty). Let
  $
    frak(M)=union.big_(i=1)^n union.big_(m=0)^(d_i)
    {"set of all minimal elements of" D(m,i)},
  $
  so $frak(M)$ is a finite set. We claim that $frak(M)$ contains every minimal
  element $(b_1,dots,b_n)$ of $D$. Surely it is false that
  $ (d_1,dots,d_n)<(b_1,dots,b_n), $
  and therefore $b_i <= d_i$ for some $i$, $1 <= i <= n$. But then
  $(b_1,dots,b_n) in D(b_i,i)$ for that choice of $i$, and so $(b_1,dots,b_n)$
  is a minimal element in $D(b_i,i)$. Since $0 <= b_i <= d_i$, this shows that
  $(b_1,dots,b_n) in frak(M)$, as claimed, and the proof is finished.
]

As special cases of Jones' Theorem, we have:

#corollary[
  Let $R$ be a d.v.r. in a global field $K$, and let $hat(R)$ be its $P$-adic
  completion, where $P$ is the maximal ideal of $R$. Let $Lambda$ be an
  $R$-order in a separable $K$-algebra. Then $Lambda$ has finite representation
  type if and only if $hat(R) times.o_R Lambda$ has finite representation type.
  #idx("Jones' Theorem", target: [@cor:finite-type-completion])
] <cor:finite-type-completion>

#corollary-suffix(base: [@cor:finite-type-completion], suffix: "a")[
  Let $G$ be a finite group, and let $R$ be any Dedekind domain with quotient
  field $K$, where $char K divides.not abs(G)$. Then $n(R G)<infinity$ if and
  only if $n(R_P G)<infinity$ for each $P$ containing $abs(G)$.
] <cor:group-ring-finite-type-completions>

For the case where $R$ is local, the problem as to whether $n(R G)<infinity$ can
always be reduced to the situation in which $G$ is a $p$-group. This follows
from an easy result:

#proposition[
  Let $R$ be a complete d.v.r., and let $H subset.eq G$ be finite groups such
  that $|G:H|$ is a unit in $R$. Then $n(R G)<infinity$ if and only if
  $n(R H)<infinity$. In particular, this conclusion holds whenever $H$ is a
  Sylow $p$-subgroup of $G$, where $p$ is a non-unit in $R$.
] <prop:finite-type-sylow-reduction>

#source(712)
#proof[
  For any $R H$-lattice $M$, we have $M divides (M^G)_H$, since
  $ M^G=1 times.o M plus.o {g_2 times.o M plus.o dots plus.o g_n times.o M}, $
  where $G=union.big_(i=1)^n g_i H$, $g_1=1$. (This does not require the
  hypothesis that $n in R^dot$.) On the other hand, for any $R G$-lattice $L$ we
  claim that
  $ L divides (L_H)^G "if" |G:H| in R^dot. $
  <eq:unit-index-induction-summand>
  Indeed, $(L_H)^G=plus.o.big (g_i times.o L)$, and we define $R$-linear maps
  $phi,psi$ by
  $
    phi:(L_H)^G -> L, quad phi(xi times.o x)=xi x,
    xi in R G,x in L,
  $
  $
    psi:L -> (L_H)^G, quad psi(x)=n^(-1)
    sum_(i=1)^n g_i times.o g_i^(-1)x,x in L.
  $
  It is easily checked that $psi$ is independent of the choice of
  representatives of the cosets of $H$ in $G$, and that $phi,psi$ are
  $R G$-homomorphisms such that $phi psi$ is the identity map on $L$. This
  establishes @eq:unit-index-induction-summand. (Analogous results were given in
  @lem:induction-relative-splittings(a) and
  @prop:relative-projectivity-properties(ix).)

  Now let $R$ be a complete d.v.r., so the K-S-A Theorem holds for $R G$- and
  $R H$-lattices, and assume that $|G:H| in R^dot$. If $n(R H)<infinity$, then
  also $n(R G)<infinity$ by @eq:unit-index-induction-summand. The converse holds
  by the first paragraph of the proof, and the proposition is established.
]

Suppose next that $H$ is a $p$-group, and $R$ is a complete d.v.r. in which $p$
is a non-unit. The finiteness of $n(R H)$ depends on the nature of $R$ as well
as on the structure of $H$. If $H$ is non-cyclic, or cyclic of order greater
than $p^2$, then for every $R$ we have $n(R H)=infinity$. This follows from the
work of Heller-Reiner~@bib:Heller1963 and Berman-Gudivok~@bib:Berman1964a. It is
also a consequence of a more general result due to Dade (see
§@ss:dade-infinite-type), which applies to arbitrary orders which are not
necessarily integral group rings.

It remains to investigate the case where $H$ is cyclic of order $p$ or $p^2$,
and here the answer depends on $R$. For the ring of $p$-adic integers $R$, we
shall prove in @th:prime-cyclic-integral-lattice-classification and
@th:prime-square-cyclic-complete-lattice-classification that
$ n(R H)=3 "if" H "is cyclic of order" p, $
$ n(R H)=4p+1 "if" H "is cyclic of order" p^2, $
and indeed we shall find all indecomposable $R H$-lattices in both cases. These
results are due to Heller-Reiner~@bib:Heller1962 and
Berman-Gudivok~@bib:Berman1964a, independently. Combining all of the above facts
with Jones' Theorem, we obtain:

#theorem[
  Let $G$ be a finite group. Then $ZZ G$ has finite representation type if and
  only if for each prime $p$ dividing $abs(G)$, the Sylow $p$-subgroups of $G$
  are cyclic of order $p$ or $p^2$.
] <th:integral-group-ring-finite-type>

#source(713)
#proof[
  For $Lambda=ZZ G$, the set $S(Lambda)$ consists of all $p$'s which divide
  $abs(G)$. By Jones' Theorem, $n(Lambda)$ is finite if and only if
  $n(Lambda_p)$ is finite for each $p in S(Lambda)$. Here, $Lambda_p=ZZ_p G$
  where $ZZ_p$ is the ring of $p$-adic integers. If $H$ is a Sylow $p$-subgroup
  of $G$, then by @prop:finite-type-sylow-reduction $n(Lambda_p)$ is finite if
  and only if $n(ZZ_p H)$ is finite. The theorem therefore follows from the
  above remarks. (Berman~@bib:Berman1966 gave another proof, somewhat more
  complicated, which does not use Jones' Theorem.)
]

To conclude, we state without proof a general result due to
Jacobinski~@bib:Jacobinski1967:

#theorem[
  Let $R="alg. int." {K}$, where $K$ is an algebraic number field. For each
  prime $p$ dividing $abs(G)$, let $P$ range over all maximal ideals of $R$
  containing $p$, and let $e(P)$ denote the ramification index of $P$ for the
  extension $K slash QQ$ (see §@ss:dedekind-ideal-theory). Let $S_p$ be a Sylow
  $p$-subgroup of $G$. Then $R G$ has finite representation type if for each
  $P$, one of the following conditions is satisfied:#ed-note[
    The printed converse omits ramified cases at $p=2$. For $R=ZZ[sqrt(2)]$ and
    $G=C_2$, the unique prime above $2$ has ramification index $2$, yet the
    quotient of the maximal overorder $R times R$ by $R G$, and its radical, are
    cyclic. Thus $R G$ has finite representation type by
    @th:drozd-roiter-commutative-finite-type and
    @th:jones-finite-type-completions.
  ]
  #idx(
    "Jacobinski's Theorem",
    target: [@th:jacobinski-number-field-group-ring-finite-type],
  )
  #enum(
    numbering: "(i)",
    [$e(P)=1$, and $S_p$ is cyclic of order $p$ or $p^2$.],
    [$e(P) <= 2$, $p>3$, and $S_p$ is cyclic of order $p$.],
    [$e(P) <= 3$, $p=3$, and $S_p$ is cyclic of order $p$.],
  )
] <th:jacobinski-number-field-group-ring-finite-type>

Many partial results of this nature were obtained earlier by various authors;
see especially Gudivok~@bib:Gudivok1967 and Kneser~@bib:Kneser1966.

=== Dade's Theorem <ss:dade-infinite-type>

Let $Lambda$ be an $R$-order in a f.d. $K$-algebra $A$. We shall show that
$Lambda$ has infinite representation type if $A$ splits into a direct sum of at
least four two-sided ideals, but the order $Lambda$ itself does not decompose
into proper two-sided ideals, and $Lambda slash P Lambda$ is a local ring for
some maximal ideal $P$ of $R$. This result will imply, for example, that an
integral group ring $ZZ G$ of a $p$-group $G$ has infinite representation type
if $G$ is non-cyclic, or cyclic of order $>p^2$.

The main result of this subsection is as follows:

#theorem(title: [Dade~@bib:Dade1963])[
  Let $Lambda$ be an $R$-order in a f.d. $K$-algebra $A$, and let
  $A=A_1 plus.o A_2 plus.o A_3 plus.o A_4$, where each $A_i$ is a nonzero
  two-sided ideal of $A$. Suppose that for some maximal ideal $P$ of $R$, the
  ring $Lambda slash P Lambda$ is a local ring. Then there are infinitely many
  non-isomorphic indecomposable left $Lambda$-lattices, and indeed there exists
  a set of such lattices whose $R$-ranks tend toward infinity. #idx(
    "Dade's Theorem",
    target: [@th:dade-infinite-representation-type],
  )
] <th:dade-infinite-representation-type>

#proof[
  _Step 1._ Replacing $R$ by its localization $R_P$ does not affect the
  hypotheses. Suppose that the theorem holds true in this local case, so
  $n(Lambda_P)=infinity$. Each indecomposable $Lambda_P$-lattice is the
  localization at $P$ of some
  #source(714)
  indecomposable $Lambda$-lattice by @cor:localized-lattice-finite-model, whence
  $n(Lambda)=infinity$. Further, for each indecomposable $Lambda$-lattice $M$,
  the $R$-rank of $M$ equals the $R_P$-rank of $M_P$. Hence it suffices to
  establish the theorem in the local case. Changing notation, assume from now on
  that $R$ is a d.v.r. with maximal ideal $P$. Set
  $
    overline(R)=R slash P, quad overline(Lambda)=Lambda slash P Lambda,
    quad D=overline(Lambda) slash rad overline(Lambda).
  $
  Then $overline(Lambda)$ is a f.d. $overline(R)$-algebra, and $D$ is a
  skewfield since $overline(Lambda)$ is by hypothesis a local ring (see
  @prop:local-ring-criteria). Let $J=rad Lambda$; from
  @prop:local-theory-radical-completion we have
  $
    Lambda slash J tilde.equiv D, quad
    J^m subset.eq P Lambda subset.eq J subset Lambda
  $
  <eq:dade-order-radical>
  for some $m >= 1$.

  _Step 2._ Let $A=plus.o.big_(i=1)^4 A_i$, and let $pi_i:A -> A_i$ be the
  $i$-th projection map, so $pi_i$ is a $K$-algebra homomorphism. We put
  $
    Lambda'=plus.o.big_(i=1)^4 pi_i lr((Lambda)), quad
    J'=plus.o.big_(i=1)^4 pi_i lr((J)), quad Lambda_0=Lambda+J'.
  $
  Clearly $Lambda subset.eq Lambda'$, and $Lambda_0$ is an $R$-order in $A$ such
  that $Lambda subset.eq Lambda_0 subset.eq Lambda'$. We shall show that
  $Lambda_0$ has infinite representation type, and indeed that there exist
  indecomposable $Lambda_0$-lattices of arbitrarily large $R$-rank. The same
  will then hold true for $Lambda$, since every $Lambda_0$-lattice is also a
  $Lambda$-lattice, and since for each pair $M$ and $N$ of $Lambda$-lattices we
  have
  $ Hom_(Lambda_0) lr((M,N))=Hom_Lambda lr((M,N)) $
  (see Exercise~@exc:overorder-lattice-homomorphisms). Hence, non-isomorphic
  indecomposable $Lambda_0$-lattices are also non-isomorphic indecomposable
  $Lambda$-lattices.

  Now $J'$ is a $Lambda'$-lattice containing $J$, and $J' inter Lambda$ is a
  two-sided ideal of $Lambda$ containing $J$. Thus $J' inter Lambda$ is either
  $J$ or $Lambda$, and the latter alternative is impossible since $1 in.not J'$.
  Thus $J' inter Lambda=J$, so
  $ Lambda_0 slash J'=(Lambda+J') slash J' tilde.equiv Lambda slash J=D. $
  Further
  $
    Lambda_0 slash J' subset Lambda' slash J'
    =plus.o.big_(i=1)^4 pi_i lr((Lambda)) slash pi_i lr((J))
    tilde.equiv D^((4)).
  $
  Note that $pi_i lr((Lambda)) slash pi_i lr((J))$ is a nonzero homomorphic
  image of $Lambda slash J$, hence equals $D$. The embedding of
  $Lambda_0 slash J'$ in $Lambda' slash J'$ is just the diagonal map
  $D -> D^((4))$, given by $d in D |-> (d,d,d,d) in D^((4))$, once we identify
  $Lambda_0 slash J'$ with $D$, and $Lambda' slash J'$ with $D^((4))$.

  #source(715)
  _Step 3._ For an arbitrary positive integer $n$, set $V=D[x] slash (x^n)$, an
  $n$-dimensional left $D$-space on which $x$ acts so that $x^n=0$, and $x$
  commutes with the elements of $D$. We form the $4n$-dimensional $D$-space
  $ V^((4))=D^((4))[x] slash (x^n), $
  viewed as left $Lambda'$-module by means of the ring homomorphism
  $Lambda' -> Lambda' slash J' tilde.equiv D^((4))$. We now define
  $
    W={v in V^((4)):v=(a,b,a+b,a+x b) "for some" a,b in V}.
  $
  Then the map $Lambda_0 -> Lambda_0 slash J' tilde.equiv D$ makes $W$ into a
  left $Lambda_0$-module, and $W$ is a $Lambda_0$-submodule of $V^((4))$ such
  that $Lambda' dot W=V^((4))$. Let $M'$ be the free $Lambda'$-module defined by
  $M'=Lambda'[x] slash (x^n)$; then there is a $Lambda'$-homomorphism
  $ phi:M' -> M' slash J'M'=V^((4)). $
  We set $M=phi^(-1) lr((W))$, so $M$ is a $Lambda_0$-sublattice of the
  $Lambda'$-lattice $M'$. From $Lambda' dot W=V^((4))$ we obtain
  $ M'=Lambda'M+J'M'. $
  Now $Lambda' slash J'$ is semisimple, and $(J')^m subset.eq P J'$ by
  @eq:dade-order-radical, so $J'=rad Lambda'$. Therefore $M'=Lambda'M$ by
  Nakayama's Lemma. Thus we have diagrams
  #dade-reduction-diagrams()
  where the vertical arrows are reduction mod $J'$.

  We shall show that for each $n$, the $Lambda_0$-lattice $M$ is indecomposable.
  Since
  $ R"-rank of" M=dim_K K M=n dot dim_K A, $
  it will then follow that $Lambda_0$ has indecomposables of arbitrarily large
  rank, which will imply the theorem. To prove $M$ indecomposable, suppose to
  the contrary that there is a non-trivial $Lambda_0$-decomposition of $M$. This
  gives a non-trivial $Lambda'$-decomposition of $Lambda'M$, and hence (after an
  easy calculation) non-trivial decompositions of $W$ and $V^((4))$ which are
  consistent with the embedding of $W$ into $V^((4))$.

  Suppose now that $overline(f)$ is a non-trivial idempotent endomorphism of
  $V^((4))$ as $D^((4))$-module, such that $overline(f)(W) subset.eq W$. We may
  write
  $ overline(f)=(f_1,f_2,f_3,f_4), "with each" f_i in End_D lr((V)), $
  noting that the off-diagonal terms are zero since $overline(f)$ commutes with
  the action
  #source(716)
  of $D^((4))$. Let $a,b in V$; from $overline(f)(W) subset.eq W$ we obtain
  $ overline(f)(a,0,a,a)=(f_1 a,0,f_3 a,f_4 a) in W, $
  so
  $ f_1=f_3=f_4. $
  Also
  $ overline(f)(0,b,b,x b)=(0,f_2 b,f_3 b,f_4(x b)) in W, $
  so
  $ f_2=f_3, quad f_4(x b)=x f_2 lr((b)). $
  Hence
  $
    overline(f)=(h,h,h,h), "where" h in End_(D[x]) lr((V)),
    "and" h^2=h
  $
  (because $overline(f)^2=overline(f)$). Since $V=D[x] slash (x^n)$, its
  $D[x]$-endomorphism ring is precisely the local ring $D[x] slash (x^n)$. Thus
  $h=0$ or $1$, which contradicts the hypothesis that $overline(f) != 0$ or $1$.
  This completes the proof of Dade's Theorem.
]

As a consequence of the theorem, we deduce the following corollary, first proved
by other methods by Heller-Reiner~@bib:Heller1963 and
Berman-Gudivok~@bib:Berman1964a:

#corollary[
  Let $p$ be prime, and let $G$ be a $p$-group. Then the integral group ring
  $ZZ G$ is of infinite representation type if $G$ is non-cyclic, or if $G$ is
  cyclic and $abs(G)>p^2$.
] <cor:p-group-infinite-integral-representation-type>

#proof[
  Let $Lambda=ZZ G$, $A=QQ G$, so $Lambda slash p Lambda$ is local by
  @cor:p-group-ring-local-base. If $G$ is cyclic of order $p^k$, then $A$ splits
  into a direct sum of $k+1$ Wedderburn components, by
  Exercise~@exc:rational-cyclic-group-wedderburn. Hence if $k>2$, there are at
  least $4$ simple components of $A$, so $Lambda$ has infinite representation
  type by Dade's Theorem.

  On the other hand, if $G$ is a non-cyclic $p$-group, it is easily shown that
  $G$ has a homomorphic image $overline(G)$ of type $(p,p)$, that is,
  $overline(G)$ is the direct product of two cyclic groups of order $p$. Since
  every $ZZ overline(G)$-lattice is also a $ZZ G$-lattice, it suffices to prove
  $ZZ overline(G)$ of infinite representation type. But
  $ZZ overline(G) slash p dot ZZ overline(G)$ is local, and $QQ overline(G)$ has
  at least $4$ simple components, so we can again use Dade's Theorem.
]

In the above, we can replace $ZZ$ by any Dedekind domain $R$ of characteristic
$0$, such that $p$ is a non-unit of $R$. Dade's Theorem has been generalized by
a number of authors: Jacobinski~@bib:Jacobinski1967 (see correction in Math.
Reviews 35 \#2876), Drozd-Roiter~@bib:Drozd1967c (§2), Drozd~@bib:Drozd1974,
Green-Reiner~@bib:Green1978.

#source(717)
To conclude, we state without proof two results of Drozd~@bib:Drozd1974:

#proposition[
  Let $R$ be a d.v.r., and let $Lambda$ be an $R$-order in a separable
  $K$-algebra $A$. If there exists an indecomposable projective left
  $Lambda$-lattice $M$ such that the composition length of the $A$-module $K M$
  is $>=4$, then $Lambda$ has infinite representation type.
] <prop:projective-rational-length-infinite-type>

This follows from a stronger result due to Drozd:

#theorem[
  Let $R$ be a d.v.r., and let $Lambda$ be an $R$-order in a separable
  $K$-algebra $A$. Suppose that $Lambda$ is a local ring, and set
  $D=Lambda slash rad Lambda$ (a skewfield). Let $Gamma$ be an $R$-order in $A$
  containing $Lambda$, and suppose that $J$ is a two-sided ideal of $Gamma$ for
  which
  $ rad Lambda subset.eq J subset.eq rad Gamma. $
  Let $m$ be the dimension over $D$ of the $D$-space $Gamma slash J$. Then
  #idx("Drozd's Theorem", target: [@th:drozd-radical-overorder-infinite-type])
  #enum(
    numbering: "(i)",
    [$Lambda$ has infinite representation type if $m >= 4$.],
    [If $Gamma$ is itself a local order, and if $(rad Gamma)^2 subset.eq J$,
      then $Lambda$ has infinite representation type whenever $m >= 3$.],
  )
] <th:drozd-radical-overorder-infinite-type>

This result plays a vital role in the work of Drozd-Kirichenko~@bib:Drozd1973;
also see the remarks in §@ss:commutative-orders-finite-type.

=== Commutative Orders <ss:commutative-orders-finite-type>

Throughout this section, let $Lambda$ denote an $R$-order in a separable
$K$-algebra $A$, where $K$ is a global field or its completion, and $R$ is a
Dedekind domain with quotient field $K$. In this section we shall again consider
the question as to when $n(Lambda)<infinity$, where $n(Lambda)$ is the number of
isomorphism classes of indecomposable left $Lambda$-lattices. By Jones' Theorem,
$n(Lambda)<infinity$ if and only if $n(Lambda_P)<infinity$ for each maximal
ideal $P$ of $R$ such that $Lambda_P$ is not a maximal order, where the
subscript $P$ denotes $P$-adic completion. As we shall see, the results of
Jacobinski and Drozd-Roiter give a complete solution to the question as to when
$n(Lambda)<infinity$, in case the order $Lambda$ is commutative. There are many
partial results for the non-commutative case, of which the Drozd-Kirichenko
Theorem seems to be the best so far.

Let $Lambda$ be commutative from now on, unless specifically stated otherwise,
and let $Lambda'$ be the unique#footnote[See
  @prop:commutative-separable-unique-maximal-order.] maximal $R$-order in the
commutative separable $K$-algebra $A$. Jacobinski~@bib:Jacobinski1967 gave
necessary and sufficient conditions that $n(Lambda)$ be finite. Another version
of these results was given by Drozd-Roiter
#source(718)
@bib:Drozd1967c; their proof is independent of Jacobinski's approach. A recent
investigation by Green-Reiner~@bib:Green1978 also treats this question, and we
shall follow their approach.

The Drozd-Roiter criteria for finite representation type are somewhat easier to
state than those of Jacobinski, and we shall phrase the main theorem as in
Drozd-Roiter. These criteria involve a comparison of $Lambda$ with the maximal
order $Lambda'$ containing it. We begin with a few general remarks about
generators of modules.

Let $Gamma$ be an arbitrary ring, $X$ a f.g. left $Gamma$-module; denote by
$mu_Gamma lr((X))$, or just $mu(X)$ if there is no danger of confusion, the
minimal number of generators of $X$ as $Gamma$-module. Put $N=rad Gamma$, and
let $overline(Gamma)=Gamma slash N$, $overline(X)=X slash N X$. Each surjection
$psi:Gamma^((n)) -> X$ yields a surjection
$overline(psi):overline(Gamma)^((n)) -> overline(X)$. Conversely, every
surjection $overline(psi)$ lifts to a map $psi$, which must be surjective by
Nakayama's Lemma. From these remarks we have
$ mu_Gamma lr((X))=mu_(overline(Gamma)) lr((overline(X))) $
<eq:module-generators-semisimple-quotient>
for every f.g. $Gamma$-module $X$. We remark also that if $overline(Gamma)$ is a
semisimple artinian ring, then
$ rad X=(rad Gamma)X $
by @prop:semilocal-module-radical. Furthermore, if $Gamma$ is a local ring, then
$overline(Gamma)$ is a skewfield by @prop:local-ring-criteria; in this case, we
have
$ mu_(overline(Gamma)) lr((overline(X)))=dim_(overline(Gamma)) overline(X). $

Suppose now that $Gamma$ is an $R$-algebra, f.g./$R$ as module, where $R$ is a
Dedekind domain, and let $X$ be a f.g. $R$-torsion $Gamma$-module. Let $a in R$
be a nonzero element with $a X=0$, so we may view $X$ as a
$(Gamma slash a Gamma)$-module. Express $Gamma slash a Gamma$ and $X$ as direct
sums of $P$-primary components (see @th:primary-decomposition-dedekind):
$
  Gamma slash a Gamma tilde.equiv product Gamma_P slash a Gamma_P,
  quad X tilde.equiv product X_P,
$
where $P$ ranges over all maximal ideals of $R$ dividing $R a$, and the
subscript $P$ denotes $P$-adic completion. Clearly
$
  mu_Gamma lr((X))=op("Max")_(P divides R a) mu_(Gamma_P) lr((X_P))
  =op("Max")_("all" P) mu_(Gamma_P) lr((X_P)).
$
We remark also that if $Gamma$ is a finite direct sum of rings
$Gamma=product Gamma_i$, then each $Gamma$-module $X$ decomposes as
$X=product X_i$, with $X_i$ a $Gamma_i$-module. We have
$ mu_Gamma lr((X))=op("Max")_i mu_(Gamma_i) lr((X_i)). $

#source(719)
Now let $Lambda$ be a commutative $R$-order in $A$, and form the $R$-torsion
$Lambda$-module $Lambda' slash Lambda$, where $Lambda'$ is the maximal $R$-order
in $A$. The basic result, due to Jacobinski~@bib:Jacobinski1967 and (in this
version) to Drozd-Roiter~@bib:Drozd1967c, is as follows:

#theorem[
  Let $A$ be a separable commutative $K$-algebra, where $K$ is a global field or
  its completion. Let $Lambda$ be an $R$-order in $A$, and $Lambda'$ the maximal
  order in $A$. Then $Lambda$ has finite representation type if and only if
  #idx(
    "Jacobinski's Theorem",
    target: [@th:drozd-roiter-commutative-finite-type],
  )
  #idx(
    "Drozd-Roiter Theorem",
    target: [@th:drozd-roiter-commutative-finite-type],
  )
  $
    mu_Lambda lr((Lambda' slash Lambda)) <= 2 "and"
    mu_Lambda lr((rad_Lambda lr((Lambda' slash Lambda)))) <= 1.
  $ <eq:drozd-roiter-generator-criterion>
] <th:drozd-roiter-commutative-finite-type>

Here, $rad_Lambda lr((Lambda' slash Lambda))$ denotes the radical of the
$Lambda$-module $Lambda' slash Lambda$. Both of the $mu$'s in
@eq:drozd-roiter-generator-criterion can be computed once they are known
locally. Further, the number $n(Lambda)$ of indecomposable $Lambda$-lattices is
finite if and only if $n(Lambda_P)<infinity$ for each $P$ at which
$Lambda_P != Lambda'_P$, by Jones' Theorem. Hence it suffices to prove the
theorem for the local case.

For the rest of this proof, we assume that $R$ is a complete d.v.r. with prime
element $pi$ and finite residue class field $overline(R)=R slash pi R$. Both
$Lambda slash rad Lambda$ and $Lambda' slash rad Lambda'$ are direct sums of
field extensions of $overline(R)$, and for later calculations we would like all
these fields to coincide with $overline(R)$. We shall accomplish this by
replacing $R$ by a larger ring $S$ which is unramified over $R$, making use of
the following interesting result due to Jacobinski~@bib:Jacobinski1967:

#proposition[
  Let $L$ be a finite unramified extension of $K$ with valuation ring $S$. Then
  $n(Lambda)<infinity$ if and only if $n(S times.o_R Lambda)<infinity$.
] <prop:unramified-extension-finite-type>

#proof[
  If $n(S times.o Lambda)<infinity$, let ${L_1,dots,L_t}$ be a full set of
  indecomposable $(S times.o Lambda)$-lattices. For each indecomposable
  $Lambda$-lattice $M$, $S times.o M$ is a direct sum of copies of the $L$'s;
  but $S times.o M tilde.equiv M^((n))$ as $Lambda$-lattices, where $n=R$-rank
  of $S$. Hence $M$ is a $Lambda$-direct summand of $S times.o M$, and therefore
  $M$ is a summand of $L_i|_Lambda$ for some $i$. This shows that
  $n(Lambda)<infinity$. The argument does not depend on $L slash K$ being
  unramified.

  To prove the converse, we start with an $(S times.o Lambda)$-lattice $X$, and
  form the $Lambda$-lattice $X_Lambda$ by restriction of operators. Then
  $S times.o_R X_Lambda$ is an $(S times.o Lambda)$-lattice, and we wish to
  compare it with the original lattice $X$. Note that the $S$-rank of
  $S times.o X$ is $n$ times the $S$-rank of $X$. We must use the fact that
  $L slash K$ is a Galois extension with Galois group $G$, where
  $G tilde.equiv overline(G)=op("Gal")(overline(S) slash overline(R))$. Here
  $overline(S)=S slash pi S$ is the residue class field of $S$. Indeed, since
  $L slash K$ is unramified, we have
  $
    L=K[x] slash (f(x)), quad S=R[x] slash (f(x)),
    quad overline(S)=overline(R)[x] slash (overline(f)(x)),
  $ <eq:unramified-extension-polynomial-model>
  where $f(x) in R[x]$ is a monic irreducible polynomial whose image
  $overline(f)(x)$ is also irreducible (see Weiss~@bib:Weiss1963 (§3-2)). Then
  $overline(S)$ is a Galois extension of the finite field $overline(R)$, so
  $overline(f)(x)$ splits into distinct linear factors in $overline(S)[x]$. By
  Hensel's Lemma, $f(x)$ splits into linear factors in $S[x]$, and so
  $L slash K$ is a Galois extension. The correspondence between factorizations
  easily yields the desired isomorphism $G tilde.equiv overline(G)$.

  #source(720)
  Now let $X$ be an $(S times.o Lambda)$-lattice, on which both $S$ and $Lambda$
  act by means of the embeddings $S -> S times.o Lambda$,
  $Lambda -> S times.o Lambda$. For each $sigma in G$, we define a conjugate
  $(S times.o Lambda)$-lattice $X^sigma$, whose elements are symbols
  ${x_sigma:x in X}$ which are added according to the rule
  $(x+y)_sigma=x_sigma+y_sigma$. The action of $S times.o Lambda$ on $X^sigma$
  is given by
  $
    (s times.o lambda)x_sigma=(s^sigma lambda x)_sigma,
    "for all" s in S,lambda in Lambda,x in X.
  $
  We shall prove#footnote[
    This result is analogous to that in
    @prop:galois-orbit-simple-module-extension.
  ]
  $
    S times.o_R X_Lambda tilde.equiv product_(sigma in G) X^sigma
    "as" (S times.o Lambda)"-lattices",
  $
  <eq:unramified-conjugate-lattice-decomposition>
  and begin by defining a map $T:S times.o X -> product X^sigma$ as follows:
  $ T(s times.o x)=product (s^sigma x)_sigma,s in S,x in X. $
  We show first that $T$ is an $(S times.o Lambda)$-homomorphism; for if
  $t in S$ and $lambda in Lambda$, then
  $
    T((t times.o lambda)(s times.o x))
    // Multiplicativity of the Galois action.
      & =T(t s times.o lambda x)=product ((t s)^sigma lambda x)_sigma
        =product (t^sigma s^sigma lambda x)_sigma \
      & =(t times.o lambda)product (s^sigma x)_sigma
        =(t times.o lambda)T(s times.o x).
  $
  Now let $S=plus.o.big_(i=1)^n R s_i$, $G={sigma_1,dots,sigma_n}$. Then
  $S times.o X=plus.o.big (s_i times.o X)$, so to show that $T$ is an
  isomorphism, we must prove that given any elements $x_1,dots,x_n in X$, there
  are uniquely determined elements $y_1,dots,y_n in X$ such that
  $
    T(sum_(i=1)^n s_i times.o y_i)=product_(sigma in G) (x_j)_sigma,
    "where" x_j in X^(sigma_j).
  $
  This condition gives
  $ sum_(i=1)^n s_i^(sigma_j)y_i=x_j,1 <= j <= n. $
  But $det(s_i^(sigma_j))_(1 <= i,j <= n)$ is a unit in $S$, since the square of
  this determinant generates the discriminant ideal $d(S slash R)$, which equals
  $R$ because $S slash R$ is unramified. Hence we can solve the above equations
  uniquely for the ${y_i}$, which completes the proof of
  @eq:unramified-conjugate-lattice-decomposition.

  Now let $n(Lambda)<infinity$, and let ${M_1,dots,M_k}$ be a full set of
  indecomposable $Lambda$-lattices. Each $(S times.o Lambda)$-lattice $X$ is an
  $(S times.o Lambda)$-direct summand of $S times.o X_Lambda$ by
  @eq:unramified-conjugate-lattice-decomposition, and $X_Lambda$ is a sum of
  $M$'s. Hence if $X$ is indecomposable then
  #source(721)
  $X divides (S times.o M_i)$ for some $i$, which proves that
  $n(S times.o Lambda)<infinity$. This completes the proof of the Proposition.
]

(If $S slash R$ is ramified, the assertion in
@prop:unramified-extension-finite-type may fail; see
Exercise~@exc:ramified-extension-infinite-type.)

Keeping the above notation, we investigate the effect of this change of ground
ring on the $mu$'s in @eq:drozd-roiter-generator-criterion. Now
$S times.o Lambda$ is an $S$-order in the separable commutative $L$-algebra
$L times.o A$, and $S times.o Lambda'$ is the maximal $S$-order in
$L times.o A$; this is an immediate consequence of
@th:unramified-base-extension, since $Lambda'$ is a direct sum of valuation
rings in finite extension fields of $K$. For convenience, let
$Gamma=S times.o Lambda$ and $Gamma'=S times.o Lambda'$. As in the beginning of
the proof of @th:hattori-projective-lattice-cancellation, we have
$
  Gamma slash rad Gamma tilde.equiv
  overline(S) times.o_(overline(R)) (Lambda slash rad Lambda),
  quad rad Gamma=S times.o_R rad Lambda.
$
A corresponding formula holds with $Lambda,Gamma$ replaced by $Lambda',Gamma'$,
respectively.

Let us now choose an extension field $overline(S)$, finite over $overline(R)$,
which is a splitting field for both $Lambda slash rad Lambda$ and
$Lambda' slash rad Lambda'$. We then use
@prop:unramified-extension-residue-correspondence to obtain an unramified
extension $L$ of $K$ with the residue class field $overline(S)$. Then
$Gamma slash rad Gamma$ and $Gamma' slash rad Gamma'$ are direct sums of copies
of $overline(S)$, and we have already shown that $n(Lambda)<infinity$ if and
only if $n(Gamma)<infinity$. It remains for us to check that
$ mu_Gamma lr((Gamma' slash Gamma))=mu_Lambda lr((Lambda' slash Lambda)), $
and likewise for the $mu$'s involving radicals. But, by
@prop:semilocal-module-radical,
$
  Gamma' slash Gamma tilde.equiv S times.o (Lambda' slash Lambda),
  "and" rad(Gamma' slash Gamma)=(rad Gamma) dot (Gamma' slash Gamma)
  tilde.equiv S times.o rad(Lambda' slash Lambda).
$
We need only show that for any f.g. $Lambda$-module $Y$,
$ mu_Lambda lr((Y))=mu_Gamma lr((S times.o Y)). $
If bars denote reduction modulo the radical, we have
$mu_Lambda lr((Y))=mu_(overline(Lambda)) lr((overline(Y)))$. Also,
$overline(Gamma)=overline(S) times.o overline(Lambda)$, and
$overline(S times.o Y)=overline(S) times.o overline(Y)$, so we need to prove
that
$
  mu_(overline(Lambda)) lr((overline(Y)))
  =mu_(overline(S) times.o overline(Lambda))
  lr((overline(S) times.o overline(Y))).
$
Now $overline(Y)$ is a $overline(Lambda)$-module, and $overline(Lambda)$ is a
direct sum of fields. It therefore suffices to consider the case where
$overline(Lambda)$ is a field, and $overline(Y)$ is a vector space over
$overline(Lambda)$; but the formula is obvious in this case.

We have now shown that replacing the ground ring $R$ by an unramified extension
ring $S$ does not alter the representation type of $Lambda$ nor the expressions
occurring in @eq:drozd-roiter-generator-criterion. Hence for the remainder of
the proof, we may assume that $Lambda slash rad Lambda$ and
$Lambda' slash rad Lambda'$ are direct sums of copies of $overline(R)$. One
further reduction is needed. If $Lambda=product Lambda_i$ is a direct sum of
$R$-orders $Lambda_i$, then correspondingly $Lambda'=product Lambda'_i$ with
each $Lambda'_i$ a maximal order. Clearly,
$mu_Lambda lr((Lambda' slash Lambda))=op("Max")mu_(Lambda_i)
lr((Lambda'_i slash Lambda_i))$, etc., and $n(Lambda)<infinity$ if and only if
$n(Lambda_i)<infinity$ for each $i$. Hence
#source(722)
it suffices to prove the result when the commutative ring $Lambda$ is
indecomposable, that is, when $Lambda slash rad Lambda$ is a field. Thus, we may
assume hereafter that $Lambda$ is a local order, with
$Lambda slash rad Lambda tilde.equiv overline(R)$. Unfortunately, the theorem is
still quite difficult to prove, despite the many reduction steps, and all of the
known proofs are rather computational. We shall give some of the details of the
Green-Reiner version, which is in the same spirit as Jacobinski's original
proof, and which corrects some minor errors in that proof. The Drozd-Roiter
approach may be found in their original article, or else in the detailed
exposition in Roggenkamp~@bib:Roggenkamp1970.

Continuing with the proof, let $J=rad Lambda$, and let bars denote reduction mod
$J$. Applying $overline(Lambda) times.o_Lambda ast$ to the $Lambda$-exact
sequence $0 -> Lambda -> Lambda' -> Lambda' slash Lambda -> 0$, we obtain a
$Lambda$-exact sequence
$
  overline(Lambda) arrow.r^psi overline(Lambda') ->
  overline(Lambda' slash Lambda) -> 0,
$
in which $psi(1)=1$. Now $psi(1) != 0$, since otherwise we obtain
$Lambda'=J Lambda'$, which is impossible by Nakayama's Lemma. Since
$overline(Lambda) tilde.equiv overline(R)$, this shows that $psi$ is monic, and
hence
$ 1+dim overline(Lambda' slash Lambda)=dim overline(Lambda'), $
where $dim$ is $overline(R)$-dimension. Since
$mu_Lambda lr((Lambda' slash Lambda))
=mu_(overline(Lambda)) lr((overline(Lambda' slash Lambda)))$, we obtain
$ mu_Lambda lr((Lambda' slash Lambda))=dim overline(Lambda')-1. $
<eq:overorder-quotient-generator-dimension>
Likewise we have $rad(Lambda' slash Lambda)=J(Lambda' slash Lambda)
=(J Lambda'+Lambda) slash Lambda$, so
$
  mu_Lambda lr((rad(Lambda' slash Lambda)))
  =dim{rad(Lambda' slash Lambda) slash J dot rad(Lambda' slash Lambda)}
  tilde.equiv dim(J Lambda'+Lambda) slash (J^2 Lambda'+Lambda).
$
Hence conditions @eq:drozd-roiter-generator-criterion may be written as
$
  dim Lambda' slash J Lambda' <= 3, quad
  dim (J Lambda'+Lambda) slash (J^2 Lambda'+Lambda) <= 1.
$ <eq:local-drozd-roiter-dimension-criterion>
These conditions say that $Lambda$ is, in some sense, not too far removed from
the maximal order $Lambda'$.

The next step reduces the study of $Lambda$-lattices to the study of pairs of
modules over artinian rings. Let $I$ be any proper $Lambda'$-ideal in $Lambda$
such that $K dot I=A$, and set
$ Delta=Lambda slash I, quad Delta'=Lambda' slash I, $
so $Delta$ and $Delta'$ are nonzero $R$-torsion $R$-algebras, and hence are
artinian rings. Of course, $Delta' slash Delta tilde.equiv Lambda' slash Lambda$
and
$
  mu_Lambda lr((Lambda' slash Lambda))=mu_Delta lr((Delta' slash Delta)),
  quad mu_Lambda lr((rad(Lambda' slash Lambda)))
  =mu_Delta lr((rad(Delta' slash Delta))).
$

#source(723)
Since $Lambda$ is local, we have
$I subset.eq J subset.eq J Lambda' subset.eq rad Lambda'$, the last inclusion
resulting from the fact that $(J Lambda')^m subset.eq pi Lambda'$ for some $m$.
If $N=rad Delta$, then we obtain
$
  N=J slash I, quad
  Delta slash N tilde.equiv Lambda slash J tilde.equiv overline(R),
$
$
  rad Delta'=(rad Lambda') slash I, quad
  Delta' slash rad Delta' tilde.equiv Lambda' slash rad Lambda'
  tilde.equiv product overline(R).
$
Thus, the rings $Delta,Delta'$ satisfy the same hypotheses as $Lambda,Lambda'$,
and conditions @eq:local-drozd-roiter-dimension-criterion may be rewritten as
$
  dim Delta' slash N Delta' <= 3, quad
  dim (N Delta'+Delta) slash (N^2 Delta'+Delta) <= 1.
$ <eq:artinian-drozd-roiter-dimension-criterion>
Let $frak(P)(Lambda)$ denote the set of f.g. projective $Lambda$-modules. Given
any $Lambda$-lattice $M$, we may form $M'=Lambda'M$ computed inside $K M$, so
$M' in frak(P)(Lambda')$ since $Lambda'$ is hereditary. We have
$I M'=I Lambda'M=I M$, and so there is an inclusion
$ M slash I M subset.eq M' slash I M=Y "(say)", $
and $Y in frak(P)(Delta')$ since $M' in frak(P)(Lambda')$.

Now every f.g. $Delta$-module has a projective cover (see
§@ss:projective-covers), unique up to isomorphism. If $X$ is a projective cover
of the $Delta$-module $M slash I M$, then there is a $Delta$-surjection
$X -> M slash I M$ whose kernel lies in $N X$. Let $f in Hom_Delta lr((X,Y))$ be
defined by composition of maps
$ X -> M slash I M -> M' slash I M'=Y. $
Then we have $X in frak(P)(Delta)$, $Y in frak(P)(Delta')$, and
$ Y=Delta' dot f(X), quad ker f subset.eq N X, "where" N=rad Delta. $
<eq:lattice-cover-triple-conditions>
Now let $frak(C)=frak(C)(Delta,Delta')$ be the category whose objects are
triples $(X,Y,f)$, where $X in frak(P)(Delta)$, $Y in frak(P)(Delta')$, and
$f in Hom_Delta lr((X,Y))$ satisfies @eq:lattice-cover-triple-conditions. A
morphism
$ (alpha,beta):(X_1,Y_1,f_1) -> (X_2,Y_2,f_2) $
in $frak(C)$ is (by definition) a pair of maps
$alpha in Hom_Delta lr((X_1,X_2))$, $beta in Hom_(Delta') lr((Y_1,Y_2))$, such
that $f_2 alpha=beta f_1$. Each $Lambda$-lattice $M$ thus gives rise to an
object $F(M)=(X,Y,f)$ in $frak(C)$, defined above. Furthermore, each
$mu in Hom_Lambda lr((M_1,M_2))$ gives rise to a commutative diagram
#lattice-cover-morphism-diagram()
where $mu$ induces $mu_1$ and $mu_2$. The map $mu_1$ lifts to a map $mu_0$ of
projective
#source(724)
covers, and so $mu$ gives rise to a morphism $F(mu)=(mu_0,mu_2)$, where
$(mu_0,mu_2):F(M_1) -> F(M_2)$. However, $F$ is _not_ a functor from the
category $frak(L)(Lambda)$ of $Lambda$-lattices to the category $frak(C)$, since
$F$ need not preserve compositions of maps. Nevertheless, if $mu$ is an
isomorphism, then so is $F(mu)$. Furthermore,
$F(M_1 plus.o M_2) tilde.equiv F(M_1) plus.o F(M_2)$, since projective covers
are “additive” (see @cor:semiperfect-projective-cover-properties).

We wish to obtain information about $Lambda$-lattices by studying the category
$frak(C)$, which is easier to handle because $Delta$ and $Delta'$ are artinian
rings. This “reduction to the artinian case” occurs in one form or another in
many calculations with lattices, and is implicit in Jacobinski's technique of
working modulo the conductor of $Lambda'$ in $Lambda$. It was made explicit in
Green-Reiner~@bib:Green1978; other consequences of this reduction may be found
in Ringel-Roggenkamp~@bib:Ringel1979. We shall show that the categories
$frak(L)(Lambda)$ and $frak(C)$ are _representation equivalent_ #idx(
  "representation equivalence of categories",
), that is, there is a bijection between the sets of isomorphism classes of
indecomposable objects in the two categories. For this purpose, we must
construct a map $G:frak(C) -> frak(L)(Lambda)$.

Starting with a triple $(X,Y,f)$ in $frak(C)$, there is a surjection
$f:X -> f(X) subset.eq Y$, and we have $Y=Delta' dot f(X)$. Since
$ker f subset.eq (rad Delta)X$, the map $X -> f(X)$ gives a $Delta$-projective
cover of $f(X)$. On the other hand,
$I subset.eq J subset.eq J Lambda' subset.eq rad Lambda'$, so by
@th:complete-ring-idempotent-decompositions we have
$Y tilde.equiv M' slash I M'$ for some $M' in frak(P)(Lambda')$. We now define
the $Lambda$-module $M$ as a pullback:
#lattice-reconstruction-diagram()
The inclusion $M subset.eq M'$ shows that $M$ is a $Lambda$-lattice. Further,
from $Y=Delta' dot f(X)$ we obtain $M'=Lambda'M+I M'$, and so $M'=Lambda'M$
since $I subset.eq rad Lambda'$. Since $I M'=I M$, it follows that
$f(X) tilde.equiv M slash I M$. If we put $G(X,Y,f)=M$, then it is obvious that
$F(M) tilde.equiv (X,Y,f)$. Conversely, starting with any $Lambda$-lattice $M$,
we obtain $G F(M) tilde.equiv M$.

Finally, we show that any morphism $(alpha,beta):(X_1,Y_1,f_1) -> (X_2,Y_2,f_2)$
in $frak(C)$ gives rise to a morphism in $frak(L)(Lambda)$. Since
$beta f_1=f_2 alpha$, we have $beta f_1 lr((X_1)) subset.eq f_2 lr((X_2))$, so
there is a commutative diagram
#triple-morphism-diagram()
The map $beta$ lifts to a $Lambda'$-map $M'_1 -> M'_2$, where
$Y_j=M'_j slash I M'_j$, $j=1,2$. We then obtain an induced map $M_1 -> M_2$ on
pullbacks, so $G$ carries each morphism in $frak(C)$ onto a morphism in
$frak(L)(Lambda)$. However, $G$ is not a functor since it need not preserve
compositions. Nevertheless, $G$ preserves isomorphisms and direct
#source(725)
sums. We have thus shown that $F$ and $G$ give a representation equivalence
between the categories $frak(L)(Lambda)$ and $frak(C)$, so $Lambda$ has finite
representation type if and only if the same is true for the category
$frak(C)=frak(C)(Delta,Delta')$. (For further results of this nature, see
Exercises~@exc:artinian-quotient-finite-type–
@exc:artinian-inclusion-representation-equivalence.)

In order to prove the main theorem, we must show that the category $frak(C)$ has
finitely many isomorphism classes of indecomposable objects if and only if
conditions @eq:artinian-drozd-roiter-dimension-criterion are satisfied. We may
write
$
  A=product_(i=1)^t K_i, quad Lambda'=product_(i=1)^t S_i,
  quad rad Lambda'=product_(i=1)^t P_i,
$
where for each $i$, $S_i$ is the integral closure of $R$ in a finite separable
extension $K_i$ of $K$. Then $S_i$ is also a complete d.v.r., and
$S_i slash P_i tilde.equiv overline(R)$ since
$Lambda' slash rad Lambda' tilde.equiv product overline(R)$. Thus, $S_i$ is
completely ramified over $R$.

If $t >= 4$, then by Dade's Theorem, the order $Lambda$ and the category
$frak(C)$ have infinite representation type. Moreover,
$ dim Lambda' slash J Lambda' >= dim Lambda' slash rad Lambda'=t >= 4, $
since $J Lambda' subset.eq rad Lambda'$. Thus for the rest of the proof, we may
assume that $t <= 3$ (it will turn out that the hardest case is that where
$t=1$).

#lemma[
  The category $frak(C)$ has infinite representation type whenever
  $dim Lambda' slash J Lambda'>3$.
] <lem:overorder-length-infinite-type>

#proof[
  We apply Exercise~@exc:artinian-pair-quotient-representation-type with
  $I_0=N$, $J_0=N Delta'$, $Gamma=Delta'$, so
  $Delta slash I_0 tilde.equiv overline(R)$ and
  $Gamma slash J_0=Delta' slash N Delta' tilde.equiv Lambda' slash J Lambda'
  =Omega$, say. The category $overline(frak(C))$ consists of triples $(X,Y,f)$
  with $X in frak(P)(overline(R))$, $Y in frak(P)(Omega)$ and
  $f in Hom_(overline(R)) lr((X,Y))$ satisfying
  $ Y=Omega dot f(X), quad ker f=0, $
  (since $ker f subset.eq (rad overline(R))X$, and $rad overline(R)=0$). We may
  write
  $ Omega=product_(i=1)^t S_i slash P_i^(n_i), quad n_i >= 1 "for each" i, $
  and then
  $ dim Lambda' slash J Lambda'=dim Omega=sum_(i=1)^t n_i. $
  We shall show that $overline(frak(C))$ has infinite representation type
  whenever $sum n_i>3$, so then the same holds for $frak(C)$ by
  Exercise~@exc:artinian-pair-quotient-representation-type. As remarked earlier,
  we are restricting our attention to the case where $t <= 3$.

  #source(726)
  Suppose first that two of the ${n_i}$ are $>=2$, say $n_1 >= 2$ and
  $n_2 >= 2$. Again using
  Exercise~@exc:artinian-pair-quotient-representation-type, with
  $
    I_0=0, quad J_0=P_1^2 slash P_1^(n_1)
    plus.o P_2^2 slash P_2^(n_2) plus.o product_(i>2) S_i slash P_i^(n_i),
  $
  we may now assume $t=2$ and $n_1=n_2=2$. For convenience of notation, put
  $k=overline(R)$. Then $Omega$ has a $k$-basis ${y_i:1 <= i <= 4}$ with
  $y_1=1$, and $rad Omega=k y_3+k y_4$. As in Step 3 in the proof of Dade's
  Theorem, let $V=k[x] slash (x^n)$ be a local ring of $k$-dimension $n$. Define
  $G(V) in overline(frak(C))$ by
  $ G(V)=(V plus.o V,Omega times.o_k V,psi), $
  where
  $
    psi(v, v')=1 times.o v+y_3 times.o v'+y_4 times.o theta v',
    quad v,v' in V,
  $
  and where $theta(v')=x v'$, $v' in V$. (It is easily verified that
  $G(V) in overline(frak(C))$.) The $overline(frak(C))$-endomorphism ring of
  $G(V)$ consists of all pairs $(alpha,beta)$ such that
  $
    alpha in End_k lr((V plus.o V)),
    quad beta in End_Omega lr((Omega times.o V)),
    quad psi alpha=beta psi.
  $
  Since $Omega times.o_k V=product_1^4 y_i times.o V$, we may write
  $ beta(1 times.o v)=sum_1^4 y_i times.o beta_i v, quad beta_i in End_k V. $
  Note that $y_3^2=y_3 y_4=y_4^2=0$ since $(rad Omega)^2=0$. For $v in V$, the
  condition $psi alpha(v, 0)=beta psi(v, 0)$ becomes (writing
  $alpha=(alpha_(i j))^(2 times 2)$),
  $
    1 times.o alpha_(11)v+y_3 times.o alpha_(21)v
    +y_4 times.o theta alpha_(21)v
    =1 times.o beta_1 v+y_2 times.o beta_2 v
    +y_3 times.o beta_3 v+y_4 times.o beta_4 v,
  $
  whence
  $
    beta_1=alpha_(11),quad beta_2=0,quad
    beta_3=alpha_(21),quad beta_4=theta alpha_(21).
  $
  Likewise, from the condition $psi alpha(0, v)=beta psi(0, v)$, $v in V$, we
  obtain
  $ beta_1=alpha_(22), quad beta_1 theta=theta alpha_(22), quad alpha_(12)=0. $
  Thus
  $
    alpha=mat(alpha_(11), 0; alpha_(21), alpha_(11)),quad
    alpha_(11)theta=theta alpha_(11).
  $
  If $(alpha,beta)$ is idempotent, then $alpha_(11)^2=alpha_(11)$. Surely
  $alpha_(11) != 0$, since if $alpha_(11)=0$ then from $alpha^2=alpha$ we obtain
  $alpha_(21)=0$, and therefore $(alpha,beta)=0$. Thus $alpha_(11)$ is an
  #source(727)
  idempotent element of the local ring $End_(k[x])V$, which shows that
  $alpha_(11)=1$. This implies that $alpha_(21)=0$ and $beta=1$, so
  $(alpha,beta)=1$. We have therefore proved that the
  $overline(frak(C))$-endomorphism ring of $G(V)$ has no nontrivial idempotents,
  so $G(V)$ is indecomposable. Therefore $overline(frak(C))$ has infinite
  representation type, as claimed.

  We are thus left with the case where at most one $n_i>1$. If each $n_i=1$,
  then $dim Lambda' slash J Lambda'=t$, contradicting our underlying hypothesis
  that $t <= 3$. Thus we may assume that $n_1 >= 2$, $n_i=1$ for $i>1$. Since
  $t <= 3$ and $sum n_i>3$, the only possibilities for $Omega$ are as follows:
  $ Omega=S_1 slash P_1^(n_1) plus.o k plus.o k,quad n_1 >= 2; $
  $
    Omega=S_1 slash P_1^(n_1) plus.o k,quad n_1 >= 3;
    quad Omega=S_1 slash P_1^(n_1),quad n_1 >= 4.
  $
  In each case, a construction of the above type shows that $overline(frak(C))$
  has infinite representation type; see Green-Reiner~@bib:Green1978, pp.~69–70
  for details. This completes the proof of the lemma.
]

Continuing with the proof of the main theorem, suppose now that
$
  dim Delta' slash N Delta' <= 3,
  quad dim (N Delta'+Delta) slash (N^2 Delta'+Delta)>1,
$
and again let us show that $overline(frak(C))$ has infinite representation type.
Using Exercise~@exc:artinian-pair-quotient-representation-type once more, with
$I_0=N^2$, $J_0=N^2 Delta'$, $overline(Delta)=Delta slash I_0$,
$overline(Delta')=Delta' slash J_0$, the problem is reduced to a new pair of
rings. Changing notation, we may then assume that $N^2=0$ and
$dim N Delta' slash N >= 2$. Since $dim Delta' slash N Delta' <= 3$, we find
readily that the only possible situations are as follows:
$
  Delta'=product_(i=1)^3 S_i slash P_i^(n_i),
  quad N Delta'=product_(i=1)^3 P_i slash P_i^(n_i),
  quad n_1=n_2=n_3=2;
$
$
  Delta'=product_(i=1)^2 S_i slash P_i^(n_i),
  quad N Delta'=P_1^2 slash P_1^(n_1) plus.o P_2 slash P_2^(n_2),
  quad n_1=4,n_2=2;
$
$ Delta'=S_1 slash P_1^(n_1),quad N Delta'=P_1^3 slash P_1^(n_1),quad n_1=6. $
Again, in each case, a construction of the above type shows that
$overline(frak(C))$ has infinite representation type (see
Green-Reiner~@bib:Green1978, pp.~70–71). This completes the proof that
conditions @eq:artinian-drozd-roiter-dimension-criterion are _necessary_ for
$Lambda$ to have finite representation type.

We turn next to the harder part of the proof of the main theorem, namely, the
proof that conditions @eq:artinian-drozd-roiter-dimension-criterion are
_sufficient_ for finite representation type. After using
Exercise~@exc:artinian-inclusion-representation-equivalence to replace $Delta$
and $Delta'$ by $Delta slash I_0$ and $Delta' slash I_0$, respectively, where
$I_0$ is the largest (two-sided) $Delta'$-ideal in $Delta$, and then changing
notation, we may assume that $Delta$ contains no nonzero (two-sided)
$Delta'$-ideal. Suppose that @eq:artinian-drozd-roiter-dimension-criterion
holds. It is then easily verified (see Green-Reiner~@bib:Green1978, pp.~71–72)
that
#source(728)
the problem of finite representation type can be reduced to the following three
test cases:
#enum(
  numbering: "(I)",
  [$Delta'=S_1 slash P_1^(n_1)$, and there exist elements $x,y in N$ such that
    $ Delta'x=P_1^3 Delta',quad Delta'y=P_1^4 Delta' "or" P_1^5 Delta'. $
  ],
  [$Delta'=S_1 slash P_1^(n_1) plus.o S_2 slash P_2^(n_2)$, and there exist
    $x,y in N$ such that
    $
      Delta'x=(P_1 plus.o P_2^2)Delta',
      quad Delta'y=P_2^2 Delta' "or" P_2^3 Delta'.
    $
  ],
  [$Delta'=product_(i=1)^3 S_i slash P_i^(n_i)$, and there exist $x,y in N$ such
    that
    $
      Delta'x=(P_1 plus.o P_2^b)Delta',
      quad Delta'y=(P_2 plus.o P_3)Delta',
    $
  ],
)
where $b=0$ or $1$.

By way of illustration, let us show that $frak(C)$ has finite representation
type in Case (II), under the assumption that $Delta'y=P_2^2 Delta'$. Let
$Gamma_i=S_i slash P_i^(n_i)$, $i=1,2$, so $Delta'=Gamma_1 plus.o Gamma_2$. Each
$X in frak(P)(Delta)$ has a free $Delta$-basis ${x_1,dots,x_m}$, and each
$Y in frak(P)(Delta')$ is of the form $Y=Y_1 plus.o Y_2$, with $Y_i$ a free
$Gamma_i$-module. If $(X,Y,psi) in frak(C)$, then expressing the elements
${psi(x_1),dots,psi(x_m)}$ in terms of a $Gamma_i$-basis of $Y_i$, $i=1,2$, we
can represent $psi$ by a matrix
$ bold(F)=mat(bold(A); bold(B); augment: #(hline: 1)), $
where $bold(A)$ is a matrix over $Gamma_1$ with $m$ columns, and $bold(B)$ is a
matrix over $Gamma_2$ with $m$ columns. Basis changes in $X$ and $Y$ yield the
equivalence relation
$
  mat(bold(A); bold(B); augment: #(hline: 1))
  tilde mat(
    bold(P)_1 bold(A)bold(T); bold(P)_2 bold(B)bold(T);
    augment: #(hline: 1)
  ),
  quad bold(P)_i in GL(Gamma_i),bold(T) in GL(Delta).
$
The triple $(X,Y,psi)$ is indecomposable in $frak(C)$ if and only if the matrix
$bold(F)$ is indecomposable under such an equivalence.

We shall now find canonical forms for indecomposable $bold(F)$'s. For
convenience, set $k=overline(R) tilde.equiv S_i slash P_i$, $P_i=pi_i S_i$,
$i=1,2$. If bars denote passage to $k$, then since $Y=Delta' dot psi(X)$, we see
at once that the rows of $overline(bold(A))$ are linearly independent over $k$,
and the same holds for $overline(bold(B))$. We have
$ Delta slash N tilde.equiv Gamma_i slash P_i Gamma_i tilde.equiv k,i=1,2. $

Consider the step $bold(A) arrow bold(P)_1 bold(A) bold(T)$. We may choose
$bold(P)_1 in GL(Gamma_1)$, $bold(T) in GL(Delta)$, such
#source(729)
that
$
  overline(bold(P)_1) overline(bold(A)) overline(bold(T))
  =mat(overline(bold(I)), overline(bold(0)); delim: "[")
  "over the field" k.
$
(Note that $overline(bold(A))$ has rank $<=m$, and the rows of
$overline(bold(A))$ are linearly independent.) Therefore we have
$ bold(A) tilde mat(bold(I)+pi_1 bold(F)_1, pi_1 bold(F)_2; delim: "[") $
for some matrices $bold(F)_1,bold(F)_2$ over $Gamma_1$. Since
$bold(I)+pi_1 bold(F)_1 in GL(Gamma_1)$, we obtain
$
  bold(A) tilde (bold(I)+pi_1 bold(F)_1)^(-1)
  mat(bold(I)+pi_1 bold(F)_1, pi_1 bold(F)_2; delim: "[")
  =mat(bold(I), pi_1 bold(F)_3; delim: "[")
$
for some matrix $bold(F)_3$.

Let us now use the hypothesis that $Delta$ contains an element $x$ such that
$x Gamma_1=pi_1 Gamma_1$. Since
$Delta slash N tilde.equiv Gamma_1 slash P_1 tilde.equiv k$, we can subtract $x$
multiples of the first set of columns of the new $bold(A)$ from the last set of
columns, so as to change $pi_1 bold(F)_3$ to a new matrix $pi_1^2 bold(F)_4$. We
then use $x^2$ multiples to bring $pi_1^2 bold(F)_4$ to the form
$pi_1^3 bold(F)_5$, and so on, until we eventually obtain
$bold(A) tilde mat(bold(I), bold(0); delim: "[")$. We then have
$
  mat(bold(A); bold(B); augment: #(hline: 1))
  tilde mat(bold(I), bold(0); bold(B)_1, bold(B)_2; augment: #(hline: 1)).
$
We now proceed with a further set of equivalence transformations, which preserve
the form $mat(bold(I), bold(0); delim: "[")$ of the top row. For example, we can
add $Delta$-multiples of the last set of columns to the first set of columns.
Note also that
$
  bold(F)=mat(bold(I), bold(0); bold(B)_1, bold(B)_2; augment: #(hline: 1))
  tilde mat(
    bold(I), bold(0); bold(P)_2 bold(B)_1 bold(T)_1,
    bold(P)_2 bold(B)_2 bold(T)_2; augment: #(hline: 1)
  ),
$
where $bold(P)_2 in GL(Gamma_2)$, $bold(T)_2 in GL(Delta)$ is arbitrary, and
$bold(T)_1 in GL(Delta)$ is chosen so that $bold(P)_1 bold(T)_1=bold(I)$ for
some $bold(P)_1 in GL(Gamma_1)$. Under the equivalence
$bold(B)_2 |-> bold(P)_2 bold(B)_2 bold(T)_2$, we can bring $bold(B)_2$ into the
form
$ mat(bold(I), pi_2 bold(B)_(13); bold(0), pi_2 bold(B)_(23)), $
and now
$
  bold(F) tilde mat(
    bold(I), bold(0), bold(0);
    bold(B)_(11), bold(I), pi_2 bold(B)_(13);
    bold(B)_(21), bold(0), pi_2 bold(B)_(23);
    augment: #(hline: 1),
  ).
$
After subtracting $Delta$-multiples of the second set of columns from the first
set,
#source(730)
we can replace $bold(B)_(11)$ by $pi_2 bold(B)'_(11)$ (say). Since the rank of
$overline(bold(B))$ equals the number of rows of $bold(B)$, it follows that the
rank of $overline(bold(B)_(21))$ is equal to the number of rows of
$bold(B)_(21)$. We can then use further equivalence transformations to bring
$bold(B)_(21)$ into the form $mat(bold(I), pi_2 bold(C); delim: "[")$ for some
$bold(C)$, and thus
$
  bold(F) tilde #block-matrix(
    4,
    (
      grid.cell(colspan: 2)[$bold(I)$],
      grid.cell(colspan: 2)[$bold(0)$],
      [$pi_2 bold(D)_1$],
      [$pi_2 bold(D)_2$],
      [$bold(I)$],
      [$pi_2 bold(B)_(13)$],
      [$bold(I)$],
      [$pi_2 bold(D)_4$],
      [$bold(0)$],
      [$pi_2 bold(B)_(23)$],
    ),
    hlines: ((at: 1),),
    vlines: ((at: 2),),
    delimiters: (sym.paren.l, sym.paren.r),
  ).
$
We next work on $pi_2 bold(B)_(23)$, bringing it into the form
$ mat(pi_2 bold(C)_1, pi_2^2 bold(C)_2; pi_2^2 bold(C)_3, pi_2^2 bold(C)_4), $
and so on. This process eventually terminates (see Green-Reiner~@bib:Green1978,
p.~79), and yields the following list of indecomposables for $bold(F)$:
$
  mat(ast; 1; augment: #(hline: 1)),quad
  mat(1; ast; augment: #(hline: 1)),quad
  mat(1; 1; augment: #(hline: 1)),quad
  #block-matrix(
    2,
    (grid.cell(colspan: 2)[$ast$], [$1$], [$pi^n$]),
    hlines: ((at: 1),),
    delimiters: (sym.paren.l, sym.paren.r),
  ),quad
  mat(1, 0; 1, pi^n; augment: #(hline: 1)),quad
  mat(1, 0; pi^n, 1; augment: #(hline: 1)),quad
  mat(1, 0; 0, 1; 1, pi^n; augment: #(hline: 2)),
$
where $n=1,3,5,dots,q$, with $q$ the least odd integer such that $pi_2^q in N$.
The asterisk indicates a matrix with no rows.

The matrix $mat(ast; 1; augment: #(hline: 1))$ corresponds to the case
$ X=Delta,quad Y=Gamma_2,quad psi:Delta -> Gamma_2,quad psi(1)=1. $
The $Lambda$-lattice $M$ is a corresponding pullback:
#single-branch-pullback-diagram()
where $e_1,e_2$ are the primitive idempotents of $Lambda'$. Thus in this case
$M tilde.equiv Lambda e_2$, since $im psi=$ image of $Lambda e_2$ in
$S_2 slash P_2^(n_2)$. Likewise, the matrix $mat(1; ast; augment: #(hline: 1))$
yields the indecomposable $Lambda$-lattice $Lambda e_1$, and the matrix
$mat(1; 1; augment: #(hline: 1))$ gives $M=Lambda$.

Consider next the matrix $#block-matrix(
  2,
  (grid.cell(colspan: 2)[$ast$], [$1$], [$pi^n$]),
  hlines: ((at: 1),),
  delimiters: (sym.paren.l, sym.paren.r),
)$, which corresponds to the case
$
  X=Delta x_1 plus.o Delta x_2,quad Y=Gamma_2 y,
  quad psi(x_1)=y,psi(x_2)=pi^n dot y.
$
#source(731)
This case gives
$ M=(Lambda+Lambda pi_2^n)e_2. $
In the same way, the last three $bold(F)$'s yield the indecomposable
$Lambda$-lattices
$ Lambda+pi_2^n Lambda e_2,quad Lambda(e_1+pi_2^n e_2)+Lambda e_2, $
and
$ Lambda(u_1+v_1)+Lambda(u_2+pi_2^n v_1), $
the last viewed as sublattice of the direct sum
$S_1 u_1 plus.o S_1 u_2 plus.o S_2 v_1$ of two copies of $S_1$ and one copy of
$S_2$.

Analogous calculations can be performed for the other cases (I)–(III) above, and
in each case one can give a complete list of indecomposable lattices. Case I
turns out to be the most complicated, and many steps are required to decompose a
given matrix $bold(F)$ into a direct sum of indecomposable submatrices.

The calculations in Jacobinski~@bib:Jacobinski1967 and
Drozd-Roiter~@bib:Drozd1967c are also quite formidable, and a neater proof of
the main theorem has yet to be found.

For $R$ a ring of algebraic integers, the question as to whether
$n(R G)<infinity$ can always be reduced to the case where $R$ is replaced by a
complete d.v.r., and $G$ by one of its Sylow $p$-subgroups $H$. Further,
$n(R H)=infinity$ if $H$ is non-cyclic (see
@cor:p-group-infinite-integral-representation-type), so we need only study the
case in which $H$ is cyclic. In this case, the order $R H$ is of course
commutative, so in dealing with representations of groups, it suffices to
consider only commutative orders.

However, there is the obvious question of generalizing the Jacobinski,
Drozd-Roiter Theorem to the case of non-commutative orders. Many authors have
obtained partial generalizations, in which the given non-commutative order is
subjected to various restrictive hypotheses. Part of the difficulty seems to
arise from the fact that $Lambda subset.eq Lambda'$ need not imply that
$rad Lambda subset.eq rad Lambda'$, in the non-commutative case.

The best result obtained so far, for the general case, is the following theorem
of Drozd-Kirichenko~@bib:Drozd1973:

#theorem[
  Let $Lambda$ be a $ZZ$-order in a f.d. semisimple $QQ$-algebra $A$, not
  necessarily commutative, and let $C$ be the center of $Lambda$. Suppose that
  for each prime ideal $P$ of $C$, the localization $Lambda_P$ is _primary_
  (that is, $Lambda_P slash rad Lambda_P$ is a simple artinian ring.) Let
  $tilde(Lambda)$ be the intersection of all maximal $ZZ$-orders in $A$ which
  contains $Lambda$.

  Then $Lambda$ is of finite representation type if and only if:
  #idx("Drozd-Kirichenko Theorem", target: [@th:drozd-kirichenko-finite-type])
  #enum(
    numbering: "(i)",
    [$tilde(Lambda)$ is a hereditary ring, and],
    [$mu_Lambda lr((tilde(Lambda) slash Lambda)) <= 2$ and
      $mu_Lambda lr((rad(tilde(Lambda) slash Lambda))) <= 1$.],
  )
] <th:drozd-kirichenko-finite-type>

#source(732)
The proof is complicated, and uses strongly the theory of Bass and Gorenstein
orders (see @sec:bass-gorenstein-orders).

#exercises-heading

#exercise[
  Let $p >= 5$ be prime, $R = "ring of" p$-adic integers, $S=R[zeta]$ where
  $zeta$ is a primitive $p$-th root of 1, and let $G$ be a cyclic group of order
  $p$. Show that $n(R G)<infinity$ but $n(S times.o_R R G)$ is infinite. Thus,
  finite representation type need not be preserved under ramified extensions.
] <exc:ramified-extension-infinite-type>

#exercise[
  Let $R$ be a complete d.v.r. with maximal ideal $P$, and let
  $Lambda'=M_n lr((R))$. Let $Lambda = { (alpha_(i j))^(n times n) in Lambda' :
    alpha_(i j) in P "for" 1 <= i < j <= n }$. Show that $Lambda$ is a
  hereditary order, and that $P Lambda'$ is a left ideal of $Lambda$ for which
  $mu_Lambda lr((P Lambda'))=n$.
] <exc:hereditary-order-ideal-generators>

#exercise[
  Let $A$ be a simple artinian ring, $S$ a simple left $A$-module, and let
  $thin_A A approx S^((n))$. For a f.g. left $A$-module $X$, let $l(X)$ denote
  its composition length, so $l(A)=n$. Show that
  $
    mu_A lr((X))=1 "if" 1 <= l(X) <= n, quad
    mu_A lr((X))=2 "if" n+1 <= l(X) <= 2 n,
  $
  and so on.
] <exc:simple-artinian-module-generators>

#exercise[
  A left artinian ring $Delta$ is said to have _finite representation type_ if
  there are only finitely many non-isomorphic f.g. indecomposable left
  $Delta$-modules.
  #idx("finite representation type")
  Let $overline(Delta)=Delta slash I_0$, where $I_0$ is a two-sided ideal of
  $Delta$. Show that if $overline(Delta)$ has infinite representation type, then
  so does $Delta$.
] <exc:artinian-quotient-finite-type>

#exercise[
  Let $phi:Delta arrow Gamma$ be a ring homomorphism of left artinian rings such
  that $phi(I_0) subset.eq J_0$, where $I_0$ and $J_0$ are two-sided ideals of
  $Delta$ and $Gamma$, respectively. Set $overline(Delta)=Delta slash I_0$,
  $overline(Gamma)=Gamma slash J_0$, so $phi$ induces a ring homomorphism
  $overline(phi):overline(Delta) arrow overline(Gamma)$. Let $frak(C)$ be the
  category whose objects are triples $(X,Y,f)$ with $X in frak(P)(Delta)$,
  $Y in frak(P)(Gamma)$, and $f in Hom(X, Y)$ any map such that
  $
    Gamma dot f(X)=Y, quad ker f subset.eq (rad Delta) X.
  $
  (The map $phi$ allows us to view each $Gamma$-module as a $Delta$-module.)
  Define $overline(frak(C))$ analogously for the rings $overline(Delta)$,
  $overline(Gamma)$. Show that if $overline(frak(C))$ has infinite
  representation type, then so does $frak(C)$.
] <exc:artinian-pair-quotient-representation-type>

#hint([@exc:artinian-pair-quotient-representation-type], caption: [Hint])[
  (Green-Reiner~@bib:Green1978): Given
  $overline(A)=(overline(X),overline(Y),overline(f))
  in overline(frak(C))$, set
  $overline(W)=overline(f)(overline(X)) subset.eq overline(Y)$. Choose a finite
  $Delta$-projective cover $pi:X arrow overline(X)$ and a $Gamma$-projective
  cover $rho:Y arrow overline(Y)$.#ed-note[
    The printed preimage need not be finitely generated over $Delta$. Take
    $Delta=k$, $Gamma=k(t)[epsilon] slash (epsilon^2)$, $I_0=0$,
    $J_0=(epsilon)$, $overline(X)=k$, $overline(Y)=k(t)$, and $overline(f)$ the
    inclusion. The preimage of $k$ under $Gamma arrow k(t)$ is $k+epsilon k(t)$,
    which is infinite-dimensional over $k$.
  ] The induced projective covers identify
  $X slash I_0 X tilde.equiv overline(X)$ and
  $Y slash J_0 Y tilde.equiv overline(Y)$. By $Delta$-projectivity of $X$, lift
  $overline(f) pi$ through $rho$ to a map $g:X arrow Y$. Let $W=g(X)$, let
  $f:X arrow W$ be the induced surjection, let $psi:W arrow Y$ be the inclusion,
  and define $sigma:W arrow overline(W)$ by $sigma=rho bar_W$. Then there is a
  commutative diagram
  #quotient-triple-lifting-diagram()
  Since $ker overline(f) subset.eq (rad overline(Delta))overline(X)$ and
  $ker pi subset.eq (rad Delta)X$, we have $ker g subset.eq (rad Delta)X$. Also
  $Gamma g(X)+ker rho=Y$, so $Gamma g(X)=Y$ by Nakayama's Lemma. Thus the triple
  $(X,Y,psi f)$ lies in $frak(C)$. Set $H(overline(A))=(X,Y,psi f)$. Quotienting
  by $I_0$ and $J_0$ recovers $overline(A)$, so an isomorphism
  $H(overline(A)) tilde.equiv H(overline(B))$ induces
  #source(733)
  an isomorphism $overline(A) tilde.equiv overline(B)$. Finally, if
  $
    H(overline(A))=(X_1,Y_1,f_1) plus.o (X_2,Y_2,f_2)
    "in" frak(C),
  $
  then reduction modulo $I_0$ and $J_0$ gives a corresponding decomposition of
  $overline(A)$. No nonzero summand disappears: if $X_i slash I_0 X_i=0$, then
  $X_i=I_0 X_i subset.eq (rad Delta)X_i$, whence $X_i=0$ and
  $Y_i=Gamma f_i lr((X_i))=0$. It follows that indecomposable $overline(A)$
  gives indecomposable $H(overline(A))$, and distinct isomorphism classes remain
  distinct.
]

#exercise[
  Let $phi:Delta arrow Gamma$ be a homomorphism of artinian rings, and let
  $I_0=ker phi$, $J_0=0$. Show that the categories $frak(C)$ and
  $overline(frak(C))$, defined in
  @exc:artinian-pair-quotient-representation-type, are representation
  equivalent.
] <exc:artinian-homomorphism-representation-equivalence>

#exercise[
  Let $Delta subset.eq Gamma$ be an inclusion of artinian rings, and let $J_0$
  be a two-sided $Gamma$-ideal contained in $Delta$. Choosing $I_0=J_0$, show
  that the categories $frak(C)$ and $overline(frak(C))$ above have finite
  representation type simultaneously. If $J_0 subset.eq rad Delta$, show that
  they are representation equivalent.
] <exc:artinian-inclusion-representation-equivalence>

#exercise[
  Let $R=hat(ZZ)_p$ be the ring of $p$-adic integers, $G=chevron.l x chevron.r$
  a cyclic group of order $p^2$. Let $Lambda=R G$, $Lambda'="maximal" R$-order
  in $hat(QQ)_p G$. Verify that
  $
    mu_Lambda lr((Lambda' slash Lambda))=2 "and"
    mu_Lambda lr((rad(Lambda' slash Lambda)))=1,
  $
  so $Lambda$ has finite representation type. (See also
  @ss:cyclic-p-squared-lattices.)
] <exc:prime-square-cyclic-finite-type-criterion>
