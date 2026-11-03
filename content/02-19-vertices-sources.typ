#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/19-vertices-sources.typ": *

== Vertices and Sources <sec:vertices-sources>

Let $(K,R,k)$ be a $p$-modular system, and let $V$ be a simple $K G$-module, for
a finite group $G$. Let $M$ be a full $R G$-lattice in $V$. By Exercise
@exc:simple-module-lattice-indecomposable, $M$ is an indecomposable
$R G$-lattice. Thus the classification of indecomposable $R G$-lattices is
closely connected with the investigation of simple $K G$-modules and their
characters. In §§@sec:vertices-sources and @sec:green-correspondence we present
an introduction to Green's work on indecomposable $R G$-lattices. It is here,
for the first time, that we see the deep relationships between representation
theory and the $p$-local structure of $G$, described in the introduction to the
chapter. Green's work also provides powerful methods for understanding Brauer's
theory of blocks (Chapter~9 of Volume~II).

#source(471)
#heading(level: 3)[
  Relative Projective and Injective Modules over Group Rings
] <ss:relative-projectivity>

The theory of vertices and sources (Green~@bib:Green1959, @bib:Green1962) is
based on the results of Gaschütz~@bib:Gaschutz1952 on relative projective and
injective modules over group rings. For remarks on the background, and
extensions to ring theory, see @bib:CurtisReiner1962[CR §§62 and~63].

Throughout §@ss:relative-projectivity, $R$ denotes an arbitrary commutative
ring, and $(G,H)$ a pair consisting of a finite group $G$ and a subgroup $H$ of
$G$. All $R G$-modules are assumed to be f.g./$R$ as usual. In this section and
the next, we use the notation
$ M divides N $
to indicate that the $R G$-module $M$ is isomorphic to a direct summand of an
$R G$-module $N$.

#definitions[
  A f.g. $R G$-module $M$ is _(G,H)-projective_ if every ses (short exact
  sequence) of $R G$-modules
  $ 0 arrow M' arrow M'' arrow M arrow 0, $
  for which the ses of restrictions to $H$
  $ 0 arrow M'_H arrow M''_H arrow M_H arrow 0 $
  is $R H$-split, is necessarily $R G$-split. A f.g. $R G$-module $M$ is
  _(G,H)-injective_ if every ses of $R G$-modules
  $ 0 arrow M arrow M' arrow M'' arrow 0, $
  for which the ses of $R H$-modules
  $ 0 arrow M_H arrow M'_H arrow M''_H arrow 0 $
  is $R H$-split, is necessarily $R G$-split.
] <def:relative-projective-injective>
#idx("relative projective", target: [@def:relative-projective-injective])
#idx("relative injective", target: [@def:relative-projective-injective])

Let us consider two extreme cases of the definition. When $H=G$, the condition
“$(G,G)$-projective” places no restriction at all on the $R G$-module $M$. On
the other hand, taking $H=1$, it is clear that every $R G$-projective module $M$
is $(G,1)$-projective. The converse is not necessarily true, because ses's of
$R$-modules do not always split. However, the conditions “$R G$-projective” and
“$(G,1)$-projective” are equivalent if $R$ is a field. They are also equivalent
for an $R G$-lattice $M$ when $R$ is a Dedekind domain, since in that case every
$R G$-exact sequence $0 arrow M' arrow M'' arrow M arrow 0$ is necessarily split
over $R$.

#theorem(title: [Gaschütz~@bib:Gaschutz1952])[
  Let $M$ be a f.g. $R G$-module, and let $H$ be a subgroup of $G$. The
  following statements are equivalent:

  #source(472)
  #enum(
    numbering: "(i)",
    [
      $M$ is $(G,H)$-projective.
    ],
    [
      $M$ is $(G,H)$-injective.
    ],
    [
      Let $G=union_(i=1)^n g_i H$. Then there exists
      $gamma in End_(R H) lr((M_H))$ such that
      $ sum_(i=1)^n g_i gamma g_i^(-1)=1_M. $
    ],
    [
      $M divides M_H^G$.
    ],
    [
      $M divides L^G$ for some $R H$-module $L$.
    ],
  )
] <th:gaschutz-relative-projectivity>
#idx("Gaschütz’s Theorem", target: [@th:gaschutz-relative-projectivity])

The ideas in this result arise naturally from the proof of Maschke's Theorem
@th:maschke. We first require the following:

#lemma[
  Let $M$ be a f.g. $R G$-module, $L$ a f.g. $R H$-module, and let
  $G=union_(i=1)^n g_i H$, with $g_1=1$. Then

  #enum(
    numbering: "(a)",
    [
      The formula
      $ L^G=(1 times.o L) plus.o (plus.o.big_(i=2)^n g_i times.o L) $
      gives an $R H$-direct sum decomposition of $L^G$. In particular,
      $M_H divides (M_H^G)_H$.
    ],
    [
      The map
      $ psi:M_H^G arrow M, $
      given by $psi(sum g_i times.o m_i)=sum g_i m_i$, is an $R G$-surjection.
      The map $psi$ is split by the $R H$-homomorphism $lambda:M arrow M_H^G$
      defined by $lambda(m)=1 times.o m$, $m in M$.
    ],
  )
] <lem:induction-relative-splittings>

The proof is immediate from the properties of induced modules discussed in
§@sec:induced-modules, and is left as an exercise for the reader. By Lemma
@lem:induction-relative-splittings, (i) $arrow.double$ (iv) and (ii)
$arrow.double$ (iv). We complete the proof of Theorem
@th:gaschutz-relative-projectivity by showing, in order, that (v) $arrow.double$
(iii), (iii) $arrow.double$ (ii), (iii) $arrow.double$ (i), and (iv)
$arrow.double$ (v).

(v) $arrow.double$ (iii): We assume that $M divides L^G$ for some $R H$-module
$L$. Without loss of generality, we may suppose that $M subset.eq L^G$, so there
exists an $R G$-projection $pi:L^G arrow M$ such that $pi=1$ on $M$. Let
$gamma^* in End_(R H) lr((L^G))$ be defined by
$ gamma^*(sum g_j times.o l_j)=1 times.o l_1, $
where $g_1=1$ as usual. It is easily verified that $sum g_i gamma^* g_i^(-1)$
acts as $1$ on $L^G$. We set
$ gamma=pi dot gamma^*|_M in End_(R H) M. $

#source(473)
Then for $m in M$,
$
  sum_(i=1)^n g_i gamma g_i^(-1)m
  =pi(sum g_i gamma^* g_i^(-1)m)=pi(m)=m,
$
which establishes (iii).

(iii) $arrow.double$ (ii): Assuming (iii), suppose that $M$ and $M'$ are
$R G$-modules such that $M subset.eq M'$ and $M$ is an $R H$-direct summand of
$M'$. Then there exists an $R H$-projection $pi$ of $M'$ onto $M$. Now define
$ pi'=sum_(i=1)^n g_i gamma pi g_i^(-1), $
where $gamma$ is the map occurring in (iii). It is easily checked that
$pi' in End_(R G) M'$ and that $pi'$ is a projection of $M'$ onto $M$. Thus $M$
is an $R G$-direct summand of $M'$, so we have proved that $M$ is
$(G,H)$-injective, and (ii) is established.

(iii) $arrow.double$ (i): Let $phi:M' arrow M$ be a surjection of $R G$-modules,
and let $xi:M_H arrow M'_H$ be an $R H$-homomorphism which splits $phi$, that
is, $phi xi=1_M$. Assuming (iii), set $xi'=sum g_i xi gamma g_i^(-1)$. Then, as
in the preceding proof, one checks that $xi' in Hom_(R G) lr((M,M'))$ and that
$phi xi'=1_M$. Thus $phi$ is $R G$-split, and we have proved that $M$ is
$(G,H)$-projective, as required.

Finally, it is immediate that (iv) $arrow.double$ (v), which completes the proof
of the theorem.

As a first application, we prove:

#corollary[
  Let $R$ be a Dedekind domain, and let $M$ and $P$ be f.g. $R G$-lattices with
  $P in cal(P)(R G)$. Then $M times.o_R P in cal(P)(R G)$.
] <cor:tensor-projective-group-lattice>
#proof[
  We have already noted that since $P in cal(P)(R G)$, $P$ is
  $(G,1)$-projective. By Theorem @th:gaschutz-relative-projectivity(iii), there
  exists $gamma in End_R P$ such that
  $ sum_(g in G) g gamma g^(-1)=1_P. $
  Then $1 times.o gamma in End_R lr((M times.o_R P))$, and we clearly have
  $ sum_(g in G) g(1 times.o gamma)g^(-1)=1 quad "on" M times.o_R P. $
  By Theorem @th:gaschutz-relative-projectivity again, it follows that
  $M times.o_R P$ is $(G,1)$-projective. Since $R$ is a Dedekind domain, and $M$
  and $P$ are $R$-lattices, it follows from §@sec:dedekind-domains that
  $M times.o_R P$ is $R$-projective. Combining these results, we conclude that
  $M times.o_R P in cal(P)(R G)$, as required.
]

#source(474)
We conclude this section with a list of other corollaries and observations which
will be basic for the theory of vertices and sources. A number of facts about
induced modules, and conjugates ${attach(L, tl: x):x in G}$ of $R H$-modules
$L$, will be noted (see §@sec:induced-modules). For $H_1,H_2 subset.eq G$, we
shall write $H_1 scripts(<=)_G H_2$ to mean that
$attach(H_1, tl: x) subset.eq H_2$ for some $x in G$, and $H_1 scripts(=)_G H_2$
to mean that $attach(H_1, tl: x)=H_2$ for some $x in G$.

#proposition[
  Let $R$ be an arbitrary commutative ring, and $H$ a subgroup of $G$.

  #enum(
    numbering: "(i)",
    [
      Direct summands of $R G$-lattices are $R G$-lattices.
    ],
    [
      If $L$ is an $R H$-lattice, then $L^G$ is an $R G$-lattice.
    ],
    [
      An $R H$-lattice $L$ is indecomposable if and only if for each $a in G$,
      the conjugate $R dot attach(H, tl: a)$-lattice $attach(L, tl: a)$ is
      indecomposable.
    ],
    [
      $(attach(L, tl: a))^G tilde.equiv L^G$ for each $R H$-lattice $L$ and each
      $a in G$.
    ],
    [
      Let $M$ be an $R G$-lattice, and let $M=M_1 plus.o M_2$ for $R G$-lattices
      $M_1$ and $M_2$. Then $M$ is $(G,H)$-projective if and only if both $M_1$
      and $M_2$ are $(G,H)$-projective.
    ],
    [
      If $M$ is a $(G,H)$-projective $R G$-lattice, then $M$ is also
      $(G,attach(H, tl: a))$-projective for all $a in G$.
    ],
    [
      An $R G$-lattice $M$ is $(G,H)$-projective if and only if it is
      $(G,H')$-projective for all $H' scripts(>=)_G H$.
    ],
    [
      If $M$ is an $R G$-lattice, and $M divides L^G$ for an
      $(H,H_0)$-projective $R H$-lattice $L$, where $H_0 subset.eq H$, then $M$
      is $(G,H_0)$-projective.
    ],
    [
      Let $H$ be a subgroup of $G$ whose index $|G:H|$ is a unit in $R$. Then
      every $R G$-module $M$ is $(G,H)$-projective, and $M divides M_H^G$.
    ],
  )
] <prop:relative-projectivity-properties>
#proof[
  (i)–(v) are left as exercises (most of them have been proved elsewhere).

  (vi) By Theorem @th:gaschutz-relative-projectivity, $M divides L^G$ for some
  $R H$-lattice $L$. By (iv), $L^G tilde.equiv (attach(L, tl: a))^G$, and
  $attach(L, tl: a)$ is an $R dot attach(H, tl: a)$-lattice. By
  @th:gaschutz-relative-projectivity again, $M$ is
  $(G,attach(H, tl: a))$-projective.

  (vii) Assume $M divides L^G$ for some $R H$-lattice $L$, and let
  $H' scripts(>=)_G H$, so $attach(H, tl: x) subset.eq H'$ for some $x in G$.
  Then $attach(L, tl: x)$ is an $R attach(H, tl: x)$-module,
  $(attach(L, tl: x))^(H')$ is an $R H'$-module, and
  $M divides ((attach(L, tl: x))^(H'))^G$, since
  $((attach(L, tl: x))^(H'))^G tilde.equiv (attach(L, tl: x))^G tilde.equiv
  L^G$, by transitivity of induction. By @th:gaschutz-relative-projectivity, $M$
  is $(G,H')$-projective. The converse is clear.

  #source(475)
  (viii) By @th:gaschutz-relative-projectivity we have $L divides L_0^H$ for
  some $R H_0$-module $L_0$. Since $M divides L^G$ by assumption, we have
  $M divides (L_0^H)^G$ by the additive property of tensor products. Then
  $M divides L_0^G$ by transitivity of induction, and hence $M$ is
  $(G,H_0)$-projective by @th:gaschutz-relative-projectivity.

  (ix) Let $G=union_(i=1)^n g_i H$, and define $gamma in End_(R H) lr((M_H))$ by
  $gamma(m)=|G:H|^(-1)m$, $m in M$. Then $sum g_i gamma g_i^(-1)=1_M$, and $M$
  is $(G,H)$-projective by Theorem @th:gaschutz-relative-projectivity.
]

#remarks(numbered: false)[
  Most of the results in @prop:relative-projectivity-properties hold for
  arbitrary f.g. $R G$-modules. They are stated for $R G$-lattices because in
  §@ss:indecomposable-lattice-vertices-sources we shall be concerned entirely
  with the classification of $R G$-lattices. It is therefore important to note
  that the module operations of taking direct summands, conjugates, induced
  modules, etc., carry lattices to lattices.

  It will also be noted from the proof of @prop:relative-projectivity-properties
  that, among the equivalent conditions for $(G,H)$-projectivity stated in
  Theorem @th:gaschutz-relative-projectivity, perhaps the most useful one is
  (v), which asserts that $M divides L^G$ for an $R H$-module $L$. In the next
  section, we shall use this condition as our working definition of
  $(G,H)$-projectivity.

  Finally, we remark that @prop:relative-projectivity-properties(ix) will be
  used several times in Chapter @ch:local-global-integral-representations,
  especially in the proof of @prop:finite-type-sylow-reduction and the
  calculations in §@ss:dihedral-metacyclic-integral-representations.
]

=== Vertices and Sources of Indecomposable Lattices
<ss:indecomposable-lattice-vertices-sources>

All the results in the rest of this section, and in §@ss:green-correspondence,
as well, are due to Green (@bib:Green1959, @bib:Green1962, and @bib:Green1964),
with some reorganization and alternate proofs by other authors.

The basic set-up consists of a finite group $G$, a prime $p$, and a commutative
ring $R$ such that either of the following two conditions hold:

(A) $R$ is a field of characteristic $p$; or

(B) $R$ is a d.v.r. with quotient field $K$ and maximal ideal $frak(p)$, such
that the residue field $overline(R)=R slash frak(p)$ has characteristic $p$, and
$R$ is complete in the $frak(p)$-adic topology.

In the context of a $p$-modular system $(K,R,k)$, the results will be applied
both to $R G$-modules and $k G$-modules (assuming the completeness hypothesis is
satisfied). In case $K$ is sufficiently large, of characteristic zero, the
results will also apply to $R G$-modules without the completeness assumption.

We shall be concerned only with $R G$-lattices, that is, f.g. $R G$-modules
which are $R$-projective. In case $R$ is a field of characteristic $p$, every
f.g. $R G$-module is of course an $R G$-lattice. It will be convenient to use
the following notation, which will be in force throughout
§§@sec:vertices-sources–@sec:green-correspondence.
$ op("Ind") R G="set of all indecomposable" R G "-lattices". $
#idx("Ind R G")

#source(476)
Because of the hypothesis on $R$, the K-S-A Theorem holds for all $R G$-lattices
$M$, and asserts that every such $M$ can be expressed as a direct sum
$ M=plus.o.big_(i=1)^m U_i, quad U_i in op("Ind") R G, $
where the indecomposable summands ${U_i}$ are uniquely determined up to
isomorphism and order of occurrence. The K-S-A Theorem was proved in
§@ss:krull-schmidt-azumaya for $R G$-lattices, with commutative rings $R$
satisfying conditions (A) or (B) above. In case $R$ is a d.v.r. which is not
necessarily complete, we shall show in @th:heller-completion-krull-schmidt that
the K-S-A Theorem is valid for $R G$-lattices, provided that $K$ is sufficiently
large and $char K=0$.

Besides the K-S-A Theorem, we shall also make heavy use of the results in
§@ss:relative-projectivity, and the Subgroup Theorem @th:mackey-subgroup, which
we restate for the reader's convenience as follows:

#theorem(name: "Subgroup Theorem")[
  Let $B$ and $C$ be subgroups of $G$, and let $L$ be an $R B$-lattice. Then
  $
    (L^G)_C tilde.equiv plus.o.big_(C a B)
    (attach(L, tl: a)_(attach(B, tl: a) inter C))^C,
  $
  where the sum is taken over the double cosets $C backslash G slash B$, and the
  summands are independent of the choice of representatives ${a}$.
] <th:vertex-subgroup-decomposition>

The objective of the theory of vertices and sources is to determine the
structure of indecomposable $R G$-lattices in terms of certain $p$-subgroups of
$G$ and indecomposable lattices associated with these subgroups.

#definition[
  Let $M$ be an $R G$-lattice. We denote by $cal(V)(M)$ the set of all subgroups
  $H$ of $G$ such that $M$ is $(G,H)$-projective. We view $cal(V)(M)$ as a
  preordered set under the relation $scripts(<=)_G$.
] <def:relative-projectivity-subgroups>

#remark(numbered: false)[
  For each $R G$-lattice $M$, $cal(V)(M)$ is nonempty, because $M$ is
  $(G,G)$-projective. We also note that if $H in cal(V)(M)$, and
  $H' scripts(>=)_G H$, then $H' in cal(V)(M)$, by
  @prop:relative-projectivity-properties(vii).
]

#theorem[
  Let $M in op("Ind") R G$. There exists a subgroup $D in cal(V)(M)$ such that
  $D scripts(<=)_G H$ for all $H in cal(V)(M)$.
] <th:minimal-relative-projectivity-subgroup>

The proof depends on two lemmas.

#lemma[
  Let $D$ and $H$ be subgroups of $G$, and let $M=R G$-lattice, $L=R D$-lattice,
  and assume $M divides L^G$. Let $U divides M_H$ for some $U in op("Ind") R H$.
  Then there exists $a in G$ such that
  $U divides (attach(L, tl: a)_(attach(D, tl: a) inter H))^H$, and $U$ is
  $(H,attach(D, tl: a) inter H)$-projective.
] <lem:relative-projective-restriction-summand>
#source(477)
#proof[
  By the Subgroup Theorem @th:vertex-subgroup-decomposition we have
  $
    (L^G)_H tilde.equiv plus.o.big_(H a D)
    (attach(L, tl: a)_(attach(D, tl: a) inter H))^H.
  $
  Then $M divides L^G$ implies $M_H divides (L^G)_H$. Since $U divides M_H$ and
  $U in op("Ind") R H$, the K-S-A Theorem implies that
  $U divides (attach(L, tl: a)_(attach(D, tl: a) inter H))^H$ for some $a in G$.
  By @th:gaschutz-relative-projectivity(v), $U$ is
  $(H,attach(D, tl: a) inter H)$-projective, as required.
]

#lemma[
  Let $M in op("Ind") R G$, and assume conditions (i)–(iii):

  #enum(
    numbering: "(i)",
    [
      $D$ is a minimal element of $cal(V)(M)$ with respect to the order relation
      $scripts(<=)_G$,
    ],
    [
      $M divides L^G$ where $L in op("Ind") R D$, and
    ],
    [
      $H$ is an arbitrary member of $cal(V)(M)$.
    ],
  )

  Then there exists $U in op("Ind") R H$ such that
  $ U divides M_H, M divides U^G, $
  and for such a lattice $U$, there exists an $a in G$ satisfying
  $
    attach(D, tl: a) subset.eq H "and" U divides (attach(L, tl: a))^H,
    quad "where" (attach(L, tl: a))^H=op("ind")_(attach(D, tl: a))^H
    lr((attach(L, tl: a))).
  $
] <lem:minimal-subgroup-common-source>
#proof[
  Since $M$ is $(G,H)$-projective, $M divides M_H^G$, by
  @th:gaschutz-relative-projectivity(iv). By the K-S-A Theorem, it follows that
  there exists $U in op("Ind") R H$ such that
  $ M divides U^G "and" U divides M_H. $
  For such a lattice $U$, by Lemma
  @lem:relative-projective-restriction-summand
  $U divides (attach(L, tl: a)_(attach(D, tl: a) inter H))^H$ and $U$ is
  $(H,attach(D, tl: a) inter H)$-projective, for some $a in G$. By
  @prop:relative-projectivity-properties(viii), $M$ is
  $(G,attach(D, tl: a) inter H)$-projective. But
  $attach(D, tl: a) inter H scripts(<=)_G D$, so by minimality of $D$ in
  $cal(V)(M)$, $attach(D, tl: a) inter H scripts(=)_G D$, whence
  $attach(D, tl: a) subset.eq H$ (otherwise $|attach(D, tl: a) inter H|<|D|$).
  Then the condition $U divides (attach(L, tl: a)_(attach(D, tl: a) inter H))^H$
  becomes $U divides (attach(L, tl: a))^H$ in this case, and the proof is
  complete.
]

#proof(head: emph[Proof of Theorem
  @th:minimal-relative-projectivity-subgroup.])[
  Let $D$ be a minimal member of $cal(V)(M)$, and let $H in cal(V)(M)$. By Lemma
  @lem:minimal-subgroup-common-source, $D scripts(<=)_G H$, and the theorem is
  proved.
]

#definition[
  Let $M in op("Ind") R G$, and let $D$ be a subgroup in $cal(V)(M)$ such that
  $D scripts(<=)_G H$ for all subgroups $H in cal(V)(M)$, as in Theorem
  @th:minimal-relative-projectivity-subgroup. Such a subgroup $D$ is called a
  _vertex_ of $M$. The set of all vertices of $M$ is denoted by $op("vtx") M$.
  If $D$ is a vertex of $M$, and $L in op("Ind") R D$ is a module such that
  $M divides L^G$, then $L$ is called a _source_ of $M$.
] <def:lattice-vertex-source>
#idx("vertex", target: [@def:lattice-vertex-source])
#idx("source", target: [@def:lattice-vertex-source])

#remarks(numbered: true)[
  By Theorem @th:minimal-relative-projectivity-subgroup, each
  $M in op("Ind") R G$ has a vertex. Moreover the set of all vertices of $M$
  forms a single conjugacy class of subgroups of
  #source(478)
  $G$, by @prop:relative-projectivity-properties(vi) and the properties of the
  preorder relation $scripts(<=)_G$. Now let $D in op("vtx") M$, so $M$ is
  $(G,D)$-projective, and $M divides X^G$ for some $R D$-lattice $X$. By the
  K-S-A Theorem, $M divides L^G$ for some $L in op("Ind") R D$ such that
  $L divides X$. Thus for each $D in op("vtx") M$, there exists an
  $L in op("Ind") R D$ which is a source of $M$.
] <rem:vertices-conjugate-sources-exist>

#proposition[
  Let $M in op("Ind") R G$. Then:

  #enum(
    numbering: "(i)",
    [
      $op("vtx") M$ is a single conjugacy class of $p$-subgroups of $G$.
    ],
    [
      If $D in op("vtx") M$, and both $L$ and $L'$ are indecomposable
      $R D$-lattices which are sources of $M$, then
      $L' tilde.equiv attach(L, tl: x)$ for some $x in N_G lr((D))$.
    ],
  )
] <prop:vertices-p-subgroups-source-conjugacy>
#proof[
  (i) Let $D in op("vtx") M$; we have already shown in
  @rem:vertices-conjugate-sources-exist that $op("vtx") M$ consists of all
  conjugates of $D$. Now let $S$ be a Sylow $p$-subgroup of $G$. Then the
  integer $|G:S|$ is prime to $p$, and hence is a unit in $R$, by hypothesis (A)
  or (B) above. By @prop:relative-projectivity-properties(ix) it follows that
  $M$ is $(G,S)$-projective. Therefore $D scripts(<=)_G S$ by
  @def:lattice-vertex-source, which shows that $D$ is a $p$-subgroup.

  (ii) We first apply Lemma @lem:minimal-subgroup-common-source to $M,D,L$, with
  $H=D$. By the lemma, there exists a module $U in op("Ind") R D$ such that
  $U divides (attach(L, tl: a))^D$ and $attach(D, tl: a) subset.eq D$, where the
  choice of $U$ is independent of $L$. Then $a in N_G lr((D))$, and
  $U tilde.equiv attach(L, tl: a)$. Applying the lemma a second time, with $L'$
  in place of $L$, we obtain $U tilde.equiv attach(L', tl: a')$, for some
  $a' in N_G lr((D))$. It follows that $L' tilde.equiv attach(L, tl: x)$, with
  $x=(a')^(-1)a in N_G lr((D))$, completing the proof.
]

The organization of Green's results in the rest of this subsection was
influenced by Burry~@bib:Burry1979.

#theorem[
  Let $H$ be an arbitrary subgroup of $G$, let $M in op("Ind") R G$,
  $U in op("Ind") R H$, and let $D_M in op("vtx") M$ and $D_U in op("vtx") U$.
  Then we have:

  #enum(
    numbering: "(i)",
    [
      $U divides M_H arrow.double D_U scripts(<=)_G D_M$,
    ],
    [
      $M divides U^G arrow.double D_M scripts(<=)_G D_U$.
    ],
  )
] <th:vertices-induction-restriction>
#proof[
  (i) Since $D_M in op("vtx") M$, we have $M divides L^G$ for some
  $L in op("Ind") R D_M$. Then $U divides M_H$ implies by
  @lem:relative-projective-restriction-summand that $U$ is
  $(H,attach(D_M, tl: a) inter H)$-projective for some $a in G$. Therefore the
  vertex $D_U$ of $U$ satisfies the condition
  $ D_U scripts(<=)_H (attach(D_M, tl: a) inter H), $
  by Theorem @th:minimal-relative-projectivity-subgroup. Since
  $attach(D, tl: a) inter H scripts(<=)_G D$, for any $D$, we have
  $D_U scripts(<=)_G D_M$, and (i) is proved.

  (ii) Since $M divides U^G$, and $U$ is $(H,D_U)$-projective, it follows that
  $M$ is $(G,D_U)$-projective by @prop:relative-projectivity-properties(viii).
  Then $D_M scripts(<=)_G D_U$ by @def:lattice-vertex-source, completing the
  proof.
]

#source(479)
The next result is a kind of _going-down theorem_, in which we begin with a
subgroup $H$ of $G$ and a lattice $M in op("Ind") R G$, and construct lattices
$U in op("Ind") R H$ satisfying various conditions, such as having a common
vertex and source with $M$.

#theorem[
  Let $M in op("Ind") R G$, and let $H$ be a subgroup of $G$ such that
  $H in cal(V)(M)$. Then the set $cal(D)$ of all vertices of $M$ contained in
  $H$ is nonempty, and $cal(D)$ may be expressed as a disjoint union
  $ cal(D)=cal(D)_1 union dots union cal(D)_m $
  of $H$-conjugacy classes of subgroups of $H$. Moreover, the following
  statements hold:

  #enum(
    numbering: "(i)",
    [
      There exists $U in op("Ind") R H$ such that $M divides U^G$ and
      $U divides M_H$. For any such $U$, we have $op("vtx") U=cal(D)_i$ for some
      class $cal(D)_i subset.eq cal(D)$.
    ],
    [
      Given a fixed class $cal(D)_i subset.eq cal(D)$, there exists
      $U in op("Ind") R H$ such that $U divides M_H$ and $op("vtx") U=cal(D)_i$.
    ],
    [
      Given a fixed class $cal(D)_j subset.eq cal(D)$, there exists
      $W in op("Ind") R H$ such that $M divides W^G$ and $op("vtx") W=cal(D)_j$.
    ],
    [
      For any $U in op("Ind") R H$ such that $U divides M_H$ and
      $op("vtx") U subset.eq cal(D)$, the lattices $U$ and $M$ have a common
      vertex and a common source.
    ],
  )
] <th:green-vertices-going-down>
#idx("Green's Theorem", "on Vertices", target: [@th:green-vertices-going-down])

#remark(numbered: false)[
  Before starting the proof, we remark that there is no reason to expect that
  (ii) and (iii) can be satisfied by the same indecomposable $R H$-lattice, for
  a given class $cal(D)_i subset.eq cal(D)$. See §@sec:green-correspondence,
  however, for further discussion of this point.
]
#proof[
  The condition $H in cal(V)(M)$ implies that $D scripts(<=)_G H$ for
  $D in op("vtx") M$, so there exist vertices of $M$ contained in $H$. By
  @prop:vertices-p-subgroups-source-conjugacy(i), $op("vtx") M$ is a single
  conjugacy class of subgroups of $G$, so clearly the collection $cal(D)$ of
  subgroups $D in op("vtx") M$ such that $D subset.eq H$ can be expressed as a
  union of $H$-conjugacy classes of subgroups. We now prove the assertions
  (i)–(iv) in order.

  (i) Since $H in cal(V)(M)$, $M$ is $(G,H)$-projective, so $M divides M_H^G$ by
  Theorem @th:gaschutz-relative-projectivity. Then $M divides U^G$ for some $U$
  in $op("Ind") R H$ such that $U divides M_H$, by the K-S-A Theorem. For any
  such $U$, let $D in op("vtx") U$; then $D in op("vtx") M$ by Theorem
  @th:vertices-induction-restriction, and it follows that
  $op("vtx") U=cal(D)_i$, for some $cal(D)_i subset.eq cal(D)$.

  (ii) Let $D in cal(D)_i$ for a fixed class $cal(D)_i subset.eq cal(D)$. Then
  $D in op("vtx") M$, so $D in cal(V)(M)$, and we can apply part (i) to $D$
  instead of $H$. In this case, $D$ is the unique vertex of $M$ contained in
  $D$. We thus obtain an $L in op("Ind") R D$ such that $L divides M_D$ and
  $D in op("vtx") L$. Since $D subset.eq H subset.eq G$, it follows from the
  K-S-A Theorem that there exists $U in op("Ind") R H$ such that $L divides U_D$
  and $U divides M_H$. Applying @th:vertices-induction-restriction(i) to the
  #source(480)
  situation $L divides U_D$ and the pair of groups $D$ and $H$, we obtain
  $D in op("vtx") U$, so the class $cal(D)_i$ containing $D$ coincides with
  $op("vtx") U$, as required.

  (iii) Let $D in cal(D)_j$, for fixed $cal(D)_j$, and apply (i) again to obtain
  an $L in op("Ind") R D$ such that $M divides L^G$ and $D in op("vtx") L$. Then
  $M divides W^G$, for some $W in op("Ind") R H$ such that $W divides L^H$, by
  the K-S-A Theorem. Let $D' in op("vtx") W$; then by
  @th:vertices-induction-restriction(ii) applied to the situation
  $W divides L^H$, we have $D' scripts(<=)_H D$. On the other hand
  $M divides W^G$ and $D in op("vtx") M$ together imply that
  $D scripts(<=)_G D'$, by @th:vertices-induction-restriction(ii) again. It
  follows that $D' scripts(=)_H D$, hence $D in op("vtx") W$, and
  $op("vtx") W=cal(D)_j$, completing the proof of (iii).

  (iv) By the hypothesis of (iv), $op("vtx") U subset.eq op("vtx") M$, and the
  problem is to find a common source. Let $D in op("vtx") U$, and let
  $L in op("Ind") R D$ be a source of $M$. By Lemma
  @lem:relative-projective-restriction-summand, there exists $a in G$ such that
  $ U divides (attach(L, tl: a)_(attach(D, tl: a) inter H))^H, $
  and therefore $U$ is $(H,attach(D, tl: a) inter H)$-projective. Then
  $attach(D, tl: a) subset.eq H$, because otherwise $U$ has a vertex contained
  in $attach(D, tl: a) inter H$ of smaller order than $D$, which contradicts
  Theorem @th:minimal-relative-projectivity-subgroup since $D in op("vtx") U$.
  Since $attach(D, tl: a) subset.eq H$, the same reasoning shows that
  $attach(D, tl: a) in op("vtx") U$. Then $attach(L, tl: a)$ is an
  indecomposable $R(attach(D, tl: a))$-lattice, and we have
  $M divides (attach(L, tl: a))^G$ and $U divides (attach(L, tl: a))^H$. Thus
  $attach(L, tl: a) in op("Ind") R(attach(D, tl: a))$ is a common source of $M$
  and $U$, and the theorem is proved.
]

Our final result is a _going-up theorem_:

#theorem[
  Let $H$ be a subgroup of $G$, and let $U in op("Ind") R H$. Then there exists
  an $M in op("Ind") R G$ such that $M divides U^G$ and $U divides M_H$. For any
  such $M$, the modules $M$ and $U$ have a vertex and source in common.
] <th:vertices-going-up>
#proof[
  Applying Lemma @lem:induction-relative-splittings(a) to $U$, we have
  $U divides (U^G)_H$. By the K-S-A Theorem, it follows that there exists
  $M in op("Ind") R G$ such that $M divides U^G$ and $U divides M_H$. The rest
  of the theorem follows from @th:green-vertices-going-down(i) and
  @th:green-vertices-going-down(iv).
]

#examples(numbered: false)[
  (i) _Indecomposable projective RG-lattices._ Let $P$ be an indecomposable
  projective $R G$-lattice. Then $P$ is $(G,1)$-projective, hence $op("vtx") P$
  consists of the trivial subgroup ${1}$, and $P divides 1_({1})^G$. Now
  $1_({1})^G tilde.equiv R G$ as left $R G$-modules, whence $P divides R G$. Let
  $S$ be a Sylow $p$-subgroup of $G$, and let $U in op("Ind") R S$ be a lattice
  such that $U divides P_S$. By Theorem @th:vertices-induction-restriction,
  $op("vtx") U subset.eq op("vtx") P={1}$, hence each such $U$ is
  $(S,1)$-projective. Since each summand $U$ of $P_S$ is also $R$-projective,
  each summand $U$ of $P_S$ belongs to $cal(P)(R S)$, whence#footnote[
    This is obvious anyway, since for any $P in cal(P)(R G)$ and any
    $H subset.eq G$, the restriction $P_H$ lies in $cal(P)(R H)$.
  ] $P_S in cal(P)(R S)$. Since $R S$ is a local $R$-algebra by
  @cor:p-group-ring-local-base, projective $R S$-modules are free (Exercise
  @exc:projective-local-free), and it follows that $P_S$ is a free $R S$-module.
  In particular, the $R$-rank of $P$ is
  #source(481)
  divisible by $|G|_p$; we showed this in §@sec:cartan-brauer-triangle in the
  case where $R$ is a d.v.r. with a sufficiently large quotient field.

  (ii) _Blocks of RG._ The direct product $G times G$ acts on the group ring
  $R G$ according to the rule
  $ (x,y)dot a=x a y^(-1),x,y in G,a in R G. $
  Then $R G$ is an $R(G times G)$-lattice. The indecomposable
  $R(G times G)$-direct summands of $R G$ are called the _p-blocks_#idx("block")
  of $R G$. Clearly the $p$-blocks are indecomposable two-sided ideals in $R G$
  whose direct sum is $R G$. Let $G_0$ be the diagonal subgroup of $G times G$.
] <exm:indecomposable-projective-group-lattices>

#proposition[
  Each $p$-block $B$ of $R G$ is $(G times G,G_0)$-projective.
] <prop:block-diagonal-relative-projectivity>
#proof[
  By @th:gaschutz-relative-projectivity, it is sufficient to prove that
  $ R G tilde.equiv 1_(G_0)^(G times G), $
  where $1_(G_0)$ is the trivial $R$-representation of $G_0$. We first notice
  that the elements of $G$ are permuted among themselves by the action of
  $G times G$ on $R G$. It is clear that the action of $G times G$ is
  transitive, and that the stabilizer in $G times G$ of the identity element of
  $R G$ is $G_0$. The above isomorphism follows from these remarks.
]

#corollary[
  The vertex of each $p$-block $B$ of $R G$ is isomorphic to a $p$-subgroup of
  $G$.
] <cor:block-vertex-p-subgroup>
#proof[
  By @prop:block-diagonal-relative-projectivity,
  @th:minimal-relative-projectivity-subgroup and
  @prop:vertices-p-subgroups-source-conjugacy, any vertex of $B$ is a
  $p$-subgroup of $G times G$ isomorphic to a subgroup of $G_0$. Since
  $G_0 tilde.equiv G$, the result follows.
]

#definition(numbered: false)[
  A $p$-subgroup of $G$ corresponding to a vertex of a $p$-block $B$ of $R G$
  (as in @cor:block-vertex-p-subgroup) is called a _defect group_ of the block
  $B$.
] <def:block-defect-group>
#idx("defect group", target: [@def:block-defect-group])

The $p$-blocks and their defect groups were first defined by Brauer, from a
different point of view (see @bib:CurtisReiner1962[CR Chapter~12]). The study of
blocks, and of their applications to character theory and finite group theory,
constitutes the central part of Brauer's theory of modular representations, and
will be taken up in Chapter~9 of Volume~II.

=== The Green Indecomposability Theorem <ss:green-indecomposability>

Many of the deeper results on vertices and sources, and their applications to
block theory, depend on a result of Green~@bib:Green1959, which asserts that
under certain circumstances, induction from an indecomposable $R H$-lattice
produces an indecomposable $R G$-lattice, for normal subgroups $H$ of $G$. The
main
#source(482)
results will be stated precisely later in this subsection. We begin with an
analysis, similar to that in §@ss:clifford-systems for simple modules, of the
endomorphism algebra $End_(R G) lr((L^G))$, where $L$ is an absolutely
indecomposable $R H$-lattice and $H$ is a normal subgroup of $G$. The proof of
the main result is an adaptation of the work of Conlon, Ward and Tucker (see
§@ss:clifford-systems for references, and also Broué~@bib:Broue1976 for a
related result).

Throughout this subsection, $R$ denotes a commutative ring satisfying either of
the following two conditions involving a prime $p$ (see
§@ss:indecomposable-lattice-vertices-sources):

(A) $R$ is a perfect field of characteristic $p$, or

(B) $R$ is a d.v.r. with maximal ideal $frak(p)$, such that the residue-field
$overline(R)=R slash frak(p)$ is a perfect field of characteristic $p$, and $R$
is complete in the $frak(p)$-adic topology.

The additional hypothesis that $overline(R)$ is perfect certainly holds true if
$overline(R)$ is a finite field or is algebraically closed. In case (A), we take
$frak(p)=0$ and identify $overline(R)$ with $R$ in the discussion to follow. The
additional assumption that $overline(R)$ be perfect is needed because, later in
this subsection, we require Theorem
@th:absolute-indecomposability-residue-endomorphism; this theorem asserts that
an $R H$-lattice $L$ is absolutely indecomposable if and only if
$ End_(R H) L slash rad(End_(R H) L) tilde.equiv overline(R), $
provided that the field $overline(R)$ is perfect.

For the first main result, we start with a finite group $S$, and an $R$-algebra
$A$ f.g./$R$ as module, such that $A$ has an $S$-graded Clifford system in the
sense of Definition @def:graded-clifford-system. We recall that in this
situation we have $A=plus.o.big_(s in S) A_s$, where the ${A_s}$ are
$R$-submodules of $A$ satisfying the conditions:
$
  A_s A_t=A_(s t), A_s=A_1 a_s=a_s A_1
  quad "for some units" a_s in A,
$
and $1 in A_1$. Then $A_1$ is an $R$-subalgebra of $A$. If $L$ is a left
$A_1$-module and $M$ a left $A$-module, we denote by $L^A$ the induced
$A$-module $A times.o_(A_1) L$, and by $M_(A_1)$ the $A_1$-module obtained by
restriction of scalars from $A$ to $A_1$. From §@ss:clifford-systems we have
$ L^A=plus.o.big_(s in S) a_s times.o L, $
and each $a_s times.o L$ is an $A_1$-submodule of $L^A$. The endomorphism ring
$E=End_A L^A$ will be viewed as a ring of right operators on $L^A$. We shall
make constant use of @prop:graded-endomorphism-algebra, which established the
following:

(i) Letting $E_s={f in E:(1 times.o L)f subset.eq a_s times.o L}$, $s in S$, we
have for all $s,t in S$:
$
  A_s lr((a_t times.o L))=a_(s t) times.o L,
  (a_s times.o L)E_t subset.eq a_(s t) times.o L,
$
$ E_s E_t subset.eq E_(s t), 1 in E_1, E=plus.o.big_(s in S) E_s. $

#source(483)
(ii) For $s in S$, let $U_s=Hom_(A_1) lr((1 times.o L,a_s times.o L))$. Then
each $phi in U_s$ extends uniquely to an element $hat(phi) in E_s$ such that
$ (a times.o l)hat(phi)=a((1 times.o l)phi) quad "for" l in L,a in A. $
The map $phi mapsto hat(phi)$ gives an isomorphism of $R$-modules
$ U_s tilde.equiv E_s,s in S. $
In particular, $E_1 tilde.equiv End_(A_1) L$ as $R$-algebras.

#theorem[
  Let $A$ be an $S$-graded $R$-algebra as above, and let $L$ be an
  indecomposable $A_1$-lattice. Keeping the above notation, set
  $ tilde(E)_1=E_1 slash rad E_1, E=End_A L^A, $
  and assume that $tilde(E)_1 tilde.equiv overline(R)$. Let
  $ T={s in S:1 times.o L tilde.equiv a_s times.o L "as" A_1 "-modules"}. $
  Then $T$ is a subgroup of $S$. Moreover, there exists a two-sided ideal $J$ of
  $E$ such that
  $
    frak(p)E subset.eq J subset.eq rad E,
    quad J=plus.o.big_(s in S)(J inter E_s),
  $
  and $E slash J$ is a $T$-graded $overline(R)$-algebra, whose grading is given
  by
  $ E slash J=plus.o.big_(t in T) E_t slash (E_t inter J). $
  Each submodule $E_t slash (E_t inter J)$ is a one-dimensional
  $overline(R)$-subspace of $E slash J$.
] <th:graded-induced-endomorphism-quotient>
#proof[
  Since $L$ is an indecomposable $A_1$-lattice, so are its conjugates
  ${a_s times.o L:s in S}$, and the formula
  $ L^A=plus.o.big_(s in S) a_s times.o L $
  gives the direct sum decomposition of $L^A$ into indecomposable
  $A_1$-submodules. Let ${mu_s}$ and ${pi_s}$ be the associated injections and
  projections, respectively, where for $s in S$,
  #graded-summand-inclusion-projection

  Let us put $E'=End_(A_1) lr((L^A))$, so $E$ is a subring of $E'$. Each
  $f in E'$ can then be represented as a matrix
  $
    f=(f_(r s))_(r,s in S), "where"
    f_(r s)=mu_r f pi_s in Hom_(A_1) lr((a_r times.o L,a_s times.o L)),
    r,s in S,
  $
  #source(484)
  remembering that $E$ and $E'$ act from the right on $L^A$. Composition of
  $f$'s corresponds to multiplication of matrices. We now proceed in a series of
  steps.

  _Step 1._ Let us set
  $ J=E inter rad E', "where" E'=End_(A_1) L^A. $
  Clearly $J$ is a two-sided ideal of $E$. Since
  $(rad E')^m subset.eq frak(p)E'$ for some integer $m$, we have
  $J^m subset.eq (frak(p)E' inter E)$. It is easily verified that
  $frak(p)E' inter E=frak(p)E$, since $L^A$ is an $R$-lattice. Therefore
  $J^m subset.eq frak(p)E$, so $J subset.eq rad E$ by Exercise
  @exc:nilpotent-modulo-radical. On the other hand, $rad E' supset.eq frak(p)E'$
  by @prop:finite-algebra-local-base-radical, so $J supset.eq frak(p)E$ as
  desired.

  Our next task is to give another description of the ideal $J$, using the
  following result of independent interest:

  #lemma(numbered: false)[
    Let $B$ be an $R$-algebra f.g./$R$, where $R$ is as above, and let
    ${L_i:1 <= i <= n}$ be a set of f.g. indecomposable $B$-modules. Put
    $L=L_1 plus.o dots plus.o L_n$, and let $E'=End_B L$, viewed as ring of
    right operators on $L$. Each $f in E'$ may be written as a matrix
    $ f=(f_(i j))^(n times n), "where" f_(i j) in Hom_B lr((L_i,L_j)). $
    Then $rad E'$ coincides with the set $J'$ of all matrices $(f_(i j))$ all of
    whose entries are non-isomorphisms.
  ] <lem:radical-indecomposable-endomorphism-matrices>
  #proof[
    Changing notation, we may write
    $ L=product_(i=1)^d L_i^((n_i)), $
    where ${L_1,dots,L_d}$ are non-isomorphic indecomposable $B$-modules. Each
    $f in E'$ is thus represented by a $d times d$ array
    $
      f=(F_(r s))^(d times d), "where"
      F_(r s) in Hom_B lr((L_r^((n_r)),L_s^((n_s))))
      quad "for" 1 <= r,s <= d.
    $
    For $r!=s$, $L_r$ is not isomorphic to $L_s$, so each entry of $F_(r s)$ is
    a non-isomorphism. On the other hand, the ring $End_B L_r$ is local, so the
    set of non-automorphisms of $L_r$ in this ring coincides with
    $rad(End L_r)$. Therefore $J'$ consists of all $d times d$ arrays
    $(F_(r s))^(d times d)$ with arbitrary off-diagonal blocks, and with
    diagonal blocks $F_(r r)$ having entries in $rad(End L_r)$, $1 <= r <= d$.

    It is easily checked that $J'$ is a two-sided ideal of $E'$, by using two
    obvious facts:

    (i) If $alpha,beta in End L_r$, with either $alpha$ or $beta$ not an
    automorphism, then $alpha beta$ is not an automorphism.

    #source(485)
    (ii) If $alpha in Hom(L_r, L_s)$ and $beta in Hom(L_s, L_r)$, where $r!=s$,
    then $beta alpha$ is not an automorphism of $L_s$ (since otherwise
    $L_s divides L_r$).

    Clearly,
    $
      E' slash J' tilde.equiv product_(r=1)^d M_(n_r) lr(
        ((End L_r) slash (rad
            End L_r))
      ),
    $
    so $E' slash J'$ is semisimple by @prop:radical-matrix-ring. We need only
    show that $J' subset.eq rad E'$. Since $frak(p)E' subset.eq J'$, it suffices
    to prove that $overline(J') subset.eq rad overline(E')$, where bars denote
    reduction mod $frak(p)$. By @prop:finite-algebra-local-base-radical, for
    large enough $k$ we have
    $ {rad(End L_r)}^k subset.eq frak(p) dot End L_r, 1 <= r <= d, $
    so each diagonal block in every matrix in $overline(J')$ is nilpotent.
    Further, every triangular matrix in $overline(J')$, with zero diagonal
    blocks, is also nilpotent. Hence $overline(J')$ is nilpotent by Wedderburn's
    Theorem (see Exercise @exc:wedderburn-nilpotent-basis), and
    $overline(J') subset.eq rad overline(E')$, which completes the proof that
    $J'=rad E'$ and establishes the lemma.
  ]

  _Step 2._ Each $f in E$ can be represented by a matrix $(f_(r s))_(r,s in S)$,
  whose first row is determined by the restriction of $f$ to $1 times.o L$.
  Conversely, given the elements ${f_(1 s):s in S}$, we know the action of $f$
  on $1 times.o L$, and hence also on $a_r times.o L$ for each $r in S$. Thus we
  have
  $ f=sum_(s in S) hat(f)_(1 s), $
  and this is precisely the formula which arises from the decomposition
  $E=plus.o.big_(s in S) E_s$.

  By Step 1, we have
  $ J={f in E:f_(r s) "is not an isomorphism for each" r,s in S}. $
  But for $f in E$, if $f_(1 s)$ is not an isomorphism, then $f_(t,t s)$ is not
  an isomorphism for any $t in S$. It follows at once that we have a
  decomposition
  $ J=plus.o.big_(s in S)(J inter E_s), $
  induced from the decomposition of $E$. Further, the preceding argument shows
  that
  $ J inter E_1 tilde.equiv rad E_1, $
  the isomorphism being given by restriction of $f in J inter E_1$ to the module
  $1 times.o L$. It remains for us to establish the $T$-graded Clifford
  structure on $E slash J$.

  #source(486)
  Now let $T={s in S:1 times.o L tilde.equiv a_s times.o L}$. For each
  $s in S-T$, there are no isomorphisms from $1 times.o L$ onto $a_s times.o L$.
  It follows at once that $E_s subset.eq J$, that is,
  $ J inter E_s=E_s "for" s in S,s in.not T. $
  This implies that
  $ E slash J=plus.o.big_(t in T) E_t slash (E_t inter J), $
  as claimed. Note that $E slash J$ is an $overline(R)$-space, since
  $J supset.eq frak(p)E$.

  _Step 3._ Finally, we prove that $E slash J$ has a $T$-graded Clifford system.
  Given $t in T$, there exists an $A_1$-isomorphism
  $ psi:1 times.o L tilde.equiv a_t times.o L, $
  whose extension $hat(psi)$ to $L^A$ gives an element of $E_t$. Then
  $hat(psi) in.not J$ since $hat(psi)_(1,t)$ is an $A_1$-isomorphism. For each
  $s in S$, we have
  $
    (a_s times.o L)hat(psi)=a_s lr(((1 times.o L)hat(psi)))
    =a_s lr((a_t times.o L))=a_(s t) times.o L,
  $
  which shows that $hat(psi)$ is surjective, and hence $hat(psi) in Aut_A L^A$.
  Now for any $f in E_t$, we have $f hat(psi)^(-1) in E_1$, and $f in J$ if and
  only if $f hat(psi)^(-1) in rad E_1$. But
  $E_1 slash rad E_1 tilde.equiv overline(R)$ by the hypothesis of the theorem,
  so for each $f in E_t$ lying outside $J$, we have
  $ f equiv beta hat(psi) quad "mod" J inter E_t $
  for some $beta in R$. We have therefore shown that for each $t in T$,
  $E_t slash (J inter E_t)$ is a one-dimensional $overline(R)$-space (with basis
  element $hat(psi)$, a unit in $E slash J$).

  Set $overline(E)_t=E_t slash (J inter E_t)$, $t in T$. The above remarks imply
  that $T$ is a group (see proof of @prop:graded-inertia-subgroup), and
  $overline(E)_s overline(E)_t=overline(E)_(s t)$ for $s,t in T$. Thus
  $E slash J$ is indeed a $T$-graded Clifford system, with the grading induced
  from the $S$-grading of $E$ by means of the natural surjection
  $E arrow E slash J$. This completes the proof of the theorem.
]

#theorem[
  Keeping the notation and hypotheses of Theorem
  @th:graded-induced-endomorphism-quotient, let
  $ B=plus.o.big_(t in T) A_t, E_T=plus.o.big_(t in T) E_t. $
  Let $L^B=B times.o_(A_1) L=plus.o.big_(i=1)^m U_i$ be the decomposition of
  $L^B$ into indecomposable $B$-modules ${U_i}$. Then
  $
    L^A=A times.o_(A_1) L=plus.o.big_(i=1)^m U_i^A,
    "where" U_i^A=A times.o_B U_i,
  $
  gives the decomposition of $L^A$ into indecomposable $A$-modules ${U_i^A}$.
  Moreover, $U_i tilde.equiv U_j$ as $B$-modules if and only if
  $U_i^A tilde.equiv U_j^A$ as $A$-modules.
] <th:graded-inertia-indecomposable-induction>
#source(487)
#proof[
  By Exercise @exc:graded-endomorphism-restriction, the restriction map
  $ op("res"):E_T arrow End_B L^B, $
  obtained by restricting each $f in E_T$ to the module $L^B$, is an isomorphism
  of $R$-algebras. Now let
  $ J_T={f in E_T:f_(t u) "is not an isomorphism for each" t,u in T}. $
  Then by the identification $E_T tilde.equiv End_B L^B$, we have
  $ J_T=End_B lr((L^B)) inter rad(End_(A_1) L^B) $
  as in Theorem @th:graded-induced-endomorphism-quotient, and clearly
  $J inter E_T subset.eq J_T$. To prove equality, by Theorem
  @th:graded-induced-endomorphism-quotient it suffices to show that
  $ J inter E_t=J_T inter E_t "for all" t in T, $
  and we have already pointed out the inclusion
  $J inter E_t subset.eq J_T inter E_T$. But by the last step of the proof of
  @th:graded-induced-endomorphism-quotient, both $J inter E_t$ and
  $J_T inter E_t$ are maximal submodules of $E_t$, and so they coincide. This
  completes the proof that $J inter E_T=J_T$, and it now follows easily from
  @th:graded-induced-endomorphism-quotient that there is an isomorphism of
  $R$-algebras
  $ E slash J tilde.equiv E_T slash J_T. $

  The theorem is now proved as follows. By @prop:morita-summand-equivalence, a
  decomposition $L^B=plus.o.big U_i$ into indecomposable summands corresponds to
  a decomposition of $E_T$ into indecomposable left ideals, with isomorphisms
  between direct summands of $L^B$ corresponding to isomorphisms between left
  ideals. By @th:complete-ring-idempotent-decompositions, since
  $J_T subset.eq rad E_T$, a decomposition of $E_T$ into indecomposable left
  ideals corresponds to such a decomposition of $E_T slash J_T$, with
  isomorphism between summands preserved. By @prop:morita-summand-equivalence
  and @th:complete-ring-idempotent-decompositions, the same statements apply to
  decompositions of $L^A=(L^B)^A$ into indecomposable summands, and
  decompositions of $E$, and of $E slash J$, into indecomposable left ideals.
  Since $E slash J tilde.equiv E_T slash J_T$, we conclude in particular that
  the ${U_i^A}$ are indecomposable summands of $L^A$, since otherwise they would
  split up further, contradicting the fact that $L^A$ and $L^B$ have the same
  number of indecomposable summands. We also have $U_i tilde.equiv U_j$ if and
  only if $U_i^A tilde.equiv U_j^A$ by the preceding discussion, and the theorem
  is proved.
]

The preceding theorem reduces the decomposition problem for $L^A$ to the stable
case, and this is now easily handled by the following important result of Conlon
(see also Tucker, Ward, loc. cit.):

#theorem[
  Keep the hypotheses of @th:graded-induced-endomorphism-quotient, and assume
  also that $L$ is a stable $A_1$-module relative to $A$, that is, the groups
  $S$ and $T$ coincide. Then each
  #source(488)
  decomposition $L^A=plus.o.big W_i$ into indecomposable summands corresponds to
  a decomposition of $E slash J$ into indecomposable left ideals, with
  preservation of isomorphisms between summands. Moreover, $E slash J$ is
  isomorphic to a twisted group algebra of $S$ over the residue field
  $overline(R)$.
] <th:conlon-stable-induced-decomposition>
#idx("Conlon's Theorem", target: [@th:conlon-stable-induced-decomposition])
#proof[
  Since $S=T$, we know by @th:graded-induced-endomorphism-quotient that
  $E slash J$ is an $S$-graded Clifford system over $overline(R)$. By Example
  (b) following @def:graded-clifford-system and the subsequent discussion, it
  follows that $E slash J$ is a twisted group algebra $(overline(R)S)_alpha$
  over $overline(R)$, for some factor set $alpha:S times S arrow overline(R)$.
  The correspondence between decompositions of $L^A$ and $E slash J$ follows
  easily from @prop:morita-summand-equivalence and
  @th:complete-ring-idempotent-decompositions, as explained in the proof of
  @th:graded-inertia-indecomposable-induction. This completes the proof of
  @th:conlon-stable-induced-decomposition.
]

We now come to a main result of this section. To understand the proof, it will
be necessary for the reader to become familiar with
§@ss:extension-ground-ring-local-theory, on absolutely indecomposability of
$Lambda$-lattices. In particular, we require Theorem
@th:absolute-indecomposability-residue-endomorphism, which asserts that a f.g.
indecomposable $Lambda$-module is absolutely indecomposable if and only if
$tilde(E)(M) tilde.equiv overline(R)$, provided that $overline(R)$ is a perfect
field (recall that $tilde(E)(M)=E(M) slash rad E(M)$, and $E(M)=End_Lambda M$).

#theorem(
  name: "The Green Indecomposability Theorem",
  title: [Green~@bib:Green1959],
)[
  Let $L$ be an absolutely indecomposable $R H$-module, where $H$ is a normal
  subgroup of $G$ such that $|G:H|=p$. Then the induced module $L^G$ is
  absolutely indecomposable.
] <th:green-indecomposability>
#idx("Green Indecomposability Theorem", target: [@th:green-indecomposability])
#idx("absolutely indecomposable", target: [@th:green-indecomposability])
#proof[
  By Example (a) of §@ss:clifford-systems, $R G$ is an $S$-graded Clifford
  system, with $A=R G$, $A_1=R H$, and $S=G slash H$. By Theorem
  @th:absolute-indecomposability-residue-endomorphism we have
  $tilde(E)(L) tilde.equiv overline(R)$, so the hypothesis of
  @th:graded-induced-endomorphism-quotient is satisfied. Since $S$ has order
  $p$, there are only two cases that can occur.

  Case (i). The subgroup $T$ in @th:graded-induced-endomorphism-quotient is
  trivial. In this case $B=A_1 tilde.equiv R H$, and by
  @th:graded-inertia-indecomposable-induction,
  $ E slash J tilde.equiv E_T slash J_T tilde.equiv overline(R). $
  By @th:graded-inertia-indecomposable-induction, it follows that $L^G$ is
  indecomposable, and that $tilde(E)(L^G) tilde.equiv overline(R)$, where
  $tilde(E)(L^G) tilde.equiv End_(R G) lr((L^G)) slash rad(
    End_(R G)
    lr((L^G))
  )$. Then $L^G$ is absolutely indecomposable by
  @th:absolute-indecomposability-residue-endomorphism, and the theorem is proved
  in this case.

  Case (ii). The subgroup $T$ in @th:graded-induced-endomorphism-quotient
  coincides with $S$, and has order $p$. In this case, we apply
  @th:conlon-stable-induced-decomposition to conclude that a decomposition of
  $L^G$ corresponds to a decomposition of $E slash J$ into left ideals.
  Moreover, it follows from @prop:morita-summand-equivalence that corresponding
  summands of $L^G$ and $E slash J$ have isomorphic semisimple quotients of
  their endomorphism algebras. By @th:conlon-stable-induced-decomposition,
  $E slash J$ is isomorphic to a twisted group algebra $(overline(R)S)_alpha$ of
  $S$ over the perfect field $overline(R)$, for some factor set
  $alpha:S times S arrow overline(R)$. Since $S$ is a $p$-group and
  $overline(R)$ is a perfect field of characteristic $p$, we can apply the
  remark following Lemma @lem:schur-multiplier-finiteness, and conclude that
  $alpha$ is a principal factor set. It follows that $E slash J$ is isomorphic
  to the group algebra $overline(R)S$. By @th:p-group-algebra-local,
  $overline(R)S$ is an indecomposable left ideal, whose endomorphism algebra is
  $overline(R)S$. Since
  #source(489)
  $overline(R)S slash rad overline(R)S tilde.equiv overline(R)$ by
  @th:p-group-algebra-local, it follows that $L^G$ is indecomposable and
  $tilde(E)(L^G) tilde.equiv overline(R)$. Thus $L^G$ is absolutely
  indecomposable by @th:absolute-indecomposability-residue-endomorphism, and the
  theorem is proved.
]

There are three corollaries to the Green Indecomposability Theorem, which extend
its scope considerably:

#corollary[
  Suppose that $H ⊴ G$, and $G slash H$ is a $p$-group. If $L$ is an absolutely
  indecomposable $R H$-module, then $L^G$ is an absolutely indecomposable
  $R G$-module.
] <cor:normal-p-quotient-indecomposable-induction>

The proof is immediate from @th:green-indecomposability, using transitivity of
induction and the fact that every $p$-group is solvable.

#corollary[
  Suppose that $G$ is a $p$-group, and $H$ is an arbitrary subgroup (not
  necessarily normal). If $L$ is an absolutely indecomposable $R H$-module then
  $L^G$ is an absolutely indecomposable $R G$-module.
] <cor:p-group-indecomposable-induction>
#proof[
  If $H=G$, there is nothing to prove. Since $G$ is a $p$-group, any proper
  subgroup is properly contained in its normalizer (see
  §@ss:background-group-theory). It follows that there is a normal series
  between $H$ and $G$ whose factors are cyclic of order $p$. The result then
  follows from @th:green-indecomposability, using transitivity of induction.
]

#corollary[
  Let $G$ be a $p$-group, and let $M$ be a transitive permutation module over
  $R G$, that is, $M$ has a free $R$-basis $X$ which is a transitive $G$-set.
  Then $M$ is an absolutely indecomposable $R G$-module.
] <cor:p-group-transitive-permutation-indecomposable>
#proof[
  Let $x_0 in X$ and let $H=op("Stab")_G x_0$. Then $X$ affords the induced
  permutation representation $1_H^G$, so $M=L^G$, where $L$ affords the trivial
  $R$-representation of $H$. Then $L^G$ is absolutely indecomposable by
  Corollary @cor:p-group-indecomposable-induction. (For a generalization of this
  result, see @th:transitive-permutation-lattice-indecomposable below.)
]

We conclude this section with two applications of the Green Indecomposability
Theorem. The first is a generalization of
@exm:indecomposable-projective-group-lattices[Example] (i) following
@th:vertices-going-up.

#theorem[
  Let $M$ be an indecomposable $R G$-lattice, let $D in op("vtx") M$, and let
  $H$ be a Sylow $p$-subgroup of $G$ containing $D$. Then the $R$-rank of $M$ is
  divisible by the index $|H:D|$.
] <th:vertex-index-divides-lattice-rank>
#proof[
  We show first that it suffices to consider the case where $G$ is a $p$-group.
  By @th:vertices-induction-restriction, each indecomposable $R H$-summand of
  $M_H$ has vertex $D_U scripts(<=)_G D$. Therefore, if we know the result for
  the $p$-subgroup $H$ and modules $U in op("Ind") R H$, then the result also
  holds for the $R G$-module $M$.

  For the rest of the proof, we may assume that $G$ is a $p$-group. We shall
  treat the case where $R$ is a d.v.r. as in (B) above, leaving to the reader
  the easier case where $R$ is a perfect field. Let $M in op("Ind") R G$, and
  let $D in op("vtx") M$. By
  #source(490)
  Lemma @lem:minimal-subgroup-common-source, $M divides L^G$ for some
  $L in op("Ind") R D$. If $L$ is absolutely indecomposable, then so is $L^G$ by
  @cor:p-group-indecomposable-induction, and it follows that
  $M tilde.equiv L^G$. But then
  $ R "-rank of" M=|G:D|dot(R "-rank of" L), $
  which gives the desired result.

  We now show how to reduce the general situation to the absolutely
  indecomposable case. By @cor:absolute-indecomposable-unramified-extension,
  there exists a complete d.v.r. $S$ which is an extension of $R$ with perfect
  residue class field $overline(S)$, such that $S M=plus.o.big N_i$, where each
  $N_i$ is an absolutely indecomposable $S G$-lattice for which
  $tilde(E)(N_i) tilde.equiv overline(S)$. If $D in op("vtx") M$, then clearly
  each $N_i$ is $(G,D)$-projective, so it has a vertex $D_i scripts(<=)_G D$. By
  the previous discussion, the $S$-rank of each $N_i$ is a multiple of
  $|G:D_i|$, and hence of $|G:D|$. Therefore the $S$-rank of $S M$ is a multiple
  of $|G:D|$. But the $S$-rank of $S M$ equals the $R$-rank of $M$, which
  completes the proof.
]

The final result is an application of @th:green-indecomposability to character
theory, and illustrates the kind of result about complex characters which can be
obtained from the theory of modular representations. The following theorem is of
interest in its own right, and is essential for block theory (Chapter~9 of
Volume~II).

#theorem(
  name: "Green's Theorem on Zeros of Characters",
  title: [Green~@bib:Green1962],
)[
  Let $R$ be a complete d.v.r. with quotient field $K$, and perfect residue
  class field $overline(R)$ of characteristic $p$. Let $M$ be an $R G$-lattice
  which is $(G,D)$-projective, for some $p$-subgroup $D$ of $G$. Let $x in G$ be
  an element whose $p$-part $u$ is not conjugate to an element of $D$. Then the
  trace map on $M$ vanishes at $x$, that is,
  $ op("Tr")(x,M)=0. $
  In other words, the $K$-character of $G$ afforded by $K times.o_R M$ vanishes
  at $x$.
] <th:green-character-zeros>
#idx(
  "Green's Theorem",
  "on Zeros of Characters",
  target: [@th:green-character-zeros],
)
#proof[
  Let $u$ be the $p$-part of $x$; then $u in.not D$, so $u!=1$. Set $X=⟨x⟩$,
  $Y=⟨x^p⟩$. Then $|X:Y|=p$ because $u!=1$. Since $u in.not attach(D, tl: a)$
  for all $a in G$, we have
  $ attach(D, tl: a) inter X subset.eq Y quad "for all" a in G. $
  Now $M$ is $(G,D)$-projective, so $M divides L^G$ for some $R D$-lattice $L$.
  Then $M_X divides (L^G)_X$, and by Mackey's Theorem
  @th:vertex-subgroup-decomposition, we have
  $
    (L^G)_X & tilde.equiv plus.o.big_a
              ((attach(L, tl: a))_(attach(D, tl: a) inter X))^X \
            & =plus.o.big_a ((attach(L, tl: a))_(attach(D, tl: a) inter X)^Y)^X,
  $
  since $Y ⊴ X$. We may write
  $ ((attach(L, tl: a))_(attach(D, tl: a) inter X))^Y=plus.o.big N_j, $
  for certain indecomposable $R Y$-lattices $N_j$. By
  @cor:absolute-indecomposable-unramified-extension, we may assume, after a
  suitable extension of $R$ (which does not affect the trace function), that the
  ${N_j}$ are absolutely indecomposable $R Y$-lattices. By the Green
  Indecomposability Theorem @th:green-indecomposability, each module $N_j^X$ is
  an indecomposable $R X$-lattice. By
  #source(491)
  the K-S-A Theorem, it follows that $M_X$ is isomorphic to a direct sum of some
  of the modules ${N_j^X}$. Since $X$ is abelian, and $x in.not Y$, we have
  $ op("Tr")(x,N_j^X)=0 "for each" j. $
  Therefore $op("Tr")(x,M)=0$ and the proof is complete.
]

#exercises-heading

#exercise[
  Let $H$ be a Sylow $p$-subgroup of the finite group $G$, and let $char k=p$.
  Let $|op("Ind") k H|$ denote the number of isomorphism classes of
  indecomposable $k H$-modules (always assumed f.g.).

  (i) Show that
  $ |op("Ind") k G|<infinity arrow.l.r.double |op("Ind") k H|<infinity. $

  (ii) Prove that if $H=⟨x⟩$ is a cyclic group of order $p^n$, then
  $op("Ind") k H$ consists of the indecomposable modules
  $ M_d=k[x] slash (1-x)^d k[x],1 <= d <= p^n. $

  (iii) Prove that $|op("Ind") k H|$ is infinite when $H$ is not cyclic.

  #hint([@exc:finite-indecomposable-group-algebras])[
    (These results are due to D. G. Higman~@bib:Higman1954): For (i), use
    @th:gaschutz-relative-projectivity and @lem:induction-relative-splittings.
    For (ii), see @prop:cyclic-normal-sylow-indecomposables below. A proof of
    (iii) is given in @bib:CurtisReiner1962[CR §64]; the result also follows as
    a special case of Dade's Theorem @th:dade-infinite-representation-type
    below.
  ]
] <exc:finite-indecomposable-group-algebras>

#exercise[
  Let $(K,R,k)$ be a $p$-modular system. Show that for each projective
  $R G$-lattice $M$, the $R$-rank of $M$ is a multiple of $|G|_p$.
] <exc:projective-lattice-rank-p-part>

#exercise[
  Let $R$ be any commutative ring, and let $G$ be a finite group whose order is
  a unit in $R$. Show that every $R G$-lattice $M$ is a projective $R G$-module.

  #hint([@exc:invertible-group-order-projective-lattice])[
    $M$ is $R G$-projective if and only if $M$ is $(G,1)$-projective, since $M$
    is a lattice. Now use @prop:relative-projectivity-properties with $H={1}$.
    For related results, see @th:invertible-group-order-lattice-isomorphism
    below.
  ]
] <exc:invertible-group-order-projective-lattice>

#exercise[
  Prove _Wedderburn's Theorem_. Let $A$ be a f.d. algebra over a field $K$, and
  let $B$ be a left ideal of $A$ which has a $K$-basis ${b_i}$ consisting of
  nilpotent elements. Then $B$ is a nilpotent ideal of $A$, and therefore
  $B subset.eq rad A$.

  #hint([@exc:wedderburn-nilpotent-basis])[
    After extending the ground field, we may assume that $K$ is algebraically
    closed. Let $N=rad A$, and set
    $ overline(A)=A slash N, overline(B)=(B+N) slash N. $
    Then $overline(B)$ is a left ideal of the split semisimple $K$-algebra
    $overline(A)$, and $overline(B)$ also has a $K$-basis ${overline(b)_i}$
    consisting of nilpotent elements. It suffices to prove that $overline(B)=0$.
    If $overline(B)!=0$, then $overline(B)$ contains a minimal left ideal
    $overline(A)e$ of $overline(A)$, where $e$ is some primitive idempotent of
    $overline(A)$. We may represent $e$ as a matrix $op("diag")(1,0,dots,0)$,
    and then $op("Trace")(e)=1$. On the other hand,
    $e=sum beta_i overline(b)_i$, $beta_i in K$, with each $overline(b)_i$
    nilpotent, so $op("Trace")(e)=0$.
  ]
] <exc:wedderburn-nilpotent-basis>
#idx(
  "Wedderburn's Theorem (on nilpotent ideals)",
  target: [@exc:wedderburn-nilpotent-basis],
)
