#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/20-green-correspondence.typ": *

#heading(level: 2)[
  The Green Correspondence. Applications to Character Theory
] <sec:green-correspondence>

#source(492)
In this section, we prove several fundamental results of Green @bib:Green1964,
which establish further connections between indecomposable $R G$-lattices and
indecomposable $R H$-lattices, for certain subgroups $H$ of $G$. The idea is to
achieve a _group-theoretical reduction_, which transfers the study of
indecomposable lattices from $G$ to proper subgroups of $G$. More precisely, let
$D$ be a fixed $p$-subgroup of $G$, and let $H>=N_G lr((D))$. We shall show that
there is a certain family $frak(A)$ of subgroups of $D$, including $D$ itself,
for which there exists a bijection between the set of indecomposable
$R G$-lattices ${M}$ with vertices in $frak(A)$, and the set of indecomposable
$R H$-lattices ${N}$ with vertices in $frak(A)$, such that corresponding
lattices have the same vertex. This bijection is called the Green
Correspondence.

When applied to blocks (see §@ss:indecomposable-lattice-vertices-sources and
Chapter~9 of Volume~II), the Green correspondence provides an interpretation of
some of the main theorems of Brauer.

In §@ss:green-correspondence-character-applications, we give Thompson's
application of the theory of vertices and sources, and the Green correspondence,
to the character theory of certain groups involving Frobenius groups as
subgroups. This application, in turn, will be crucial for the theory of blocks
in Chapter~9 of Volume~II.

=== The Green Correspondence <ss:green-correspondence>

Throughout this section, the hypotheses and notation established in
§@ss:indecomposable-lattice-vertices-sources remain in force. Thus,
$op("Ind") R G$ denotes the set of indecomposable $R G$-lattices, where $R$ is
either a field of characteristic $p$ or a d.v.r. with residue field
$overline(R)=R slash frak(p)$ of characteristic $p$, such that the K-S-A Theorem
holds for $R G$-lattices. As in §@ss:indecomposable-lattice-vertices-sources,
$op("vtx") M$ denotes the set of vertices of $M in op("Ind") R G$. By
@prop:vertices-p-subgroups-source-conjugacy, $op("vtx") M$ is a single conjugacy
class of $p$-subgroups of $G$. It will be convenient to add to our terminology
as follows:

#definitions[
  Let $frak(Z)$ be a family of subgroups of $G$. An $R G$-lattice $M$ is said to
  be _$(G,frak(Z))$-projective_#idx(
    "relative projective",
    target: [@def:family-relative-projectivity],
  ) if $M=plus.o M_i$, where for each $i$, $M_i$ is a $(G,Z_i)$-projective
  $R G$-lattice for some subgroup $Z_i in frak(Z)$. Using a notation borrowed
  from analysis, we write
  $ M=O(frak(Z)) $
  to denote a $(G,frak(Z))$-projective $R G$-lattice $M$. We shall write
  $Z scripts(lt.eq)_G frak(Z)$ to indicate that $Z scripts(lt.eq)_G Z'$ for some
  subgroup $Z' in frak(Z)$. We also write
  $ M=L plus.o O(frak(Z)) $
  whenever $M=L plus.o N$ with $N=O(frak(Z))$.
] <def:family-relative-projectivity>

We first require two preliminary results.

#source(493)
#lemma[
  Let $frak(Z)$ be a family of subgroups of $G$. Then direct sums, and summands,
  of $(G,frak(Z))$-projective $R G$-lattices are $(G,frak(Z))$-projective.
] <lem:family-relative-projectivity-summands>
#proof[
  Direct sums of $(G,frak(Z))$-projective $R G$-lattices are clearly
  $(G,frak(Z))$-projective by definition (see
  @def:family-relative-projectivity). Now let $M=O(frak(Z))$, and let $N$ be an
  $R G$-lattice such that $N divides M$. By the first part of the proof, it is
  sufficient to prove that the indecomposable direct summands of $N$ are
  $O(frak(Z))$, so we may assume that $N$ is indecomposable. By
  @def:family-relative-projectivity, $M=plus.o M_i$, where each summand $M_i$ is
  $(G,Z_i)$-projective for some subgroup $Z_i in frak(Z)$. Since $N divides M$
  and $N in op("Ind") R G$, the K-S-A Theorem implies that $N divides M_i$ for
  some $i$, and $N$ is $(G,Z_i)$-projective by
  @prop:relative-projectivity-properties(v). This completes the proof of the
  lemma.
]

#lemma[
  Let $frak(Z)$ be a family of subgroups of $G$. Let $M$ be an indecomposable
  $R G$-lattice with vertex $D^*$. Then $M=O(frak(Z))$ if and only if
  $D^* scripts(lt.eq)_G frak(Z)$.
] <lem:family-relative-projectivity-vertex>
#proof[
  If $D^* scripts(lt.eq)_G frak(Z)$ then $D^* scripts(lt.eq)_G Z_i$ for some
  $Z_i in frak(Z)$. Then $M$ is $(G,Z_i)$-projective by
  @prop:relative-projectivity-properties(viii), and so $M=O(frak(Z))$.
  Conversely, if $M=O(frak(Z))$, then $M$ is $(G,Z_i)$-projective for some
  subgroup $Z_i in frak(Z)$, and we have $D^* scripts(lt.eq)_G Z_i$ by
  Theorem~@th:minimal-relative-projectivity-subgroup.
]

#definition[
  An _admissible triple_#idx(
    "admissible triple for Green correspondence",
    target: [@def:green-admissible-triple],
  ) $(G,H,D)$ for the Green correspondence consists of a finite group $G$, a
  $p$-subgroup $D$ of $G$, and a subgroup $H$ containing $N_G lr((D))$. For each
  such triple, we define families of subgroups:
] <def:green-admissible-triple>
$
  cases(
    frak(X)=frak(X)(D,H)={attach(D, tl: x) inter D:x in G-H},
    frak(Y)=frak(Y)(D,H)={attach(D, tl: x) inter H:x in G-H},
    frak(A)=frak(A)(D,H)={D^*<=D:D^* scripts(lt.eq.not)_G frak(X)}.
  )
$ <eq:green-subgroup-families>
We recall that $D^* scripts(lt.eq.not)_G frak(X)$ means
$D^* scripts(lt.eq.not)_G X$ for all subgroups $X in frak(X)$. We also note that
$D in frak(A)$, so that $frak(A)$ is nonempty. The main result is as follows:

#theorem[
  Let $(G,H,D)$ be an admissible triple of groups as in
  @def:green-admissible-triple, and let $frak(A),frak(X),frak(Y)$ be the
  families of subgroups defined in @eq:green-subgroup-families. Then there
  exists a bijection
  $ g:[M] arrow.l.r [N] $
  from the set of isomorphism classes of indecomposable $R G$-lattices $M$ with
  vertex in $frak(A)$ to the set of isomorphism classes of indecomposable
  $R H$-lattices $N$ with vertex in $frak(A)$. A lattice $M in op("Ind") R G$
  with vertex in $frak(A)$ corresponds to an indecomposable $R H$-lattice $N$
  with the same vertex if and only if either of the following equivalent
  conditions holds:
  #enum(
    numbering: "(i)",
    [$M_H=N plus.o O(frak(Y))$],
    [#source(494)$N^G=M plus.o O(frak(X))$.],
  )
  Furthermore, corresponding modules have the same source as well as the same
  vertex.
] <th:green-correspondence>

#definition[
  The bijection $g$ defined in Theorem~@th:green-correspondence is called the
  _Green correspondence_#idx(
    "Green correspondence",
    target: [@def:green-correspondence],
  ) (associated with the triple $(G,H,D)$).
] <def:green-correspondence>

Before proving the theorem, it may be helpful to state a corollary which is a
less general version of the Green correspondence, but is perhaps easier to
understand.

#corollary[
  Let $D$ be a $p$-subgroup of $G$, and let $H>=N_G lr((D))$. Then there is a
  bijection $g:[M] arrow.l.r [N]$ between isomorphism classes of indecomposable
  $R G$-lattices $M$ with vertex $D$, and isomorphism classes of indecomposable
  $R H$-lattices $N$ with vertex $D$. Two lattices $M in op("Ind") R G$ and
  $N in op("Ind") R H$ correspond to each other if and only if either
  $M divides N^G$ or $N divides M_H$.
] <cor:green-correspondence-fixed-vertex>

The proof of Theorem~@th:green-correspondence will be given in several steps,
some of which are of interest in themselves.

#case-list(
  numbering: "Step 1.",
  [#case[
    Let $N$ be an $(H,D)$-projective $R H$-lattice. We assert that
    $ (N^G)_H=N plus.o O(frak(Y)). $
    We have already noted several times that $N divides (N^G)_H$; see
    @lem:induction-relative-splittings(a) or the Subgroup Theorem
    @th:vertex-subgroup-decomposition. Therefore $(N^G)_H=N plus.o N'$ for some
    $R H$-lattice $N'$. We have to prove that $N'=O(frak(Y))$. Since $N$ is
    $(H,D)$-projective, by @th:gaschutz-relative-projectivity(v) we have
    $ L^H=N plus.o U $
    for some $R D$-lattice $L$ and some $R H$-lattice $U$. Then
    $U divides (U^G)_H$, so we may write $(U^G)_H=U plus.o U'$. This gives
    $
      N plus.o N' plus.o U plus.o U'
      =(N^G)_H plus.o (U^G)_H
      tilde.equiv ((L^H)^G)_H tilde.equiv (L^G)_H.
    $
    By the Subgroup Theorem, we obtain
    $
      (L^G)_H=L^H plus.o
      (plus.o_(x in.not H)(attach(L, tl: x)_(attach(D, tl: x) inter H))^H)
      tilde.equiv N plus.o U plus.o
      (plus.o_(x in.not H)(attach(L, tl: x)_(attach(D, tl: x) inter H))^H).
    $
    By the cancellation theorem (Corollary~@cor:krull-schmidt-cancellation), we
    conclude that
    $
      N' plus.o U' tilde.equiv
      plus.o_(x in.not H)(attach(L, tl: x)_(attach(D, tl: x) inter H))^H
      =O(frak(Y)).
    $
    By Lemma~@lem:family-relative-projectivity-summands, it follows that
    $N'=O(frak(Y))$, and the proof is completed.
  ] <case:green-restricted-induction>],
  [#case[
    #source(495)
    Let $D^*<=D$, and let $frak(X)$ and $frak(Y)$ be the families of subgroups
    defined in @eq:green-subgroup-families. Then
    $
      D^* scripts(lt.eq)_G frak(X) arrow.l.r.double D^* scripts(lt.eq)_H frak(X)
      arrow.l.r.double D^* scripts(lt.eq)_H frak(Y).
    $
    The proof is left as an exercise.
  ] <case:green-subgroup-comparison>],
  [#case[
    Let $M in op("Ind") R G$, and suppose there exists $D^* in op("vtx") M$ such
    that $D^*<=D$. The following statements hold:
    #enum(
      numbering: "(i)",
      [If $M=O(frak(X))$, then $M_H=O(frak(Y))$.],
      [If $M!=O(frak(X))$, then $M_H=N plus.o O(frak(Y))$ for some
        indecomposable $R H$-lattice $N$ with vertex $D^*$, such that
        $N!=O(frak(Y))$.],
    )
    We first prove (i). By @th:green-vertices-going-down(iii), there exists
    $W in op("Ind") R H$ such that $M divides W^G$ and $D^* in op("vtx") W$.
    Since $D^*<=D$, $W$ is $(H,D)$-projective, so
    $ (W^G)_H=W plus.o O(frak(Y)) $
    by @case:green-restricted-induction. But $M_H divides (W^G)_H$, and
    $M=O(frak(X))$ by hypothesis, so $D^* scripts(lt.eq)_G frak(X)$ by Lemma
    @lem:family-relative-projectivity-vertex. Therefore
    $D^* scripts(lt.eq)_H frak(Y)$ by @case:green-subgroup-comparison. Since
    $D^* in op("vtx") W$, we can apply @lem:family-relative-projectivity-vertex
    to $W$, to obtain $W=O(frak(Y))$. Thus $(W^G)_H=O(frak(Y))$, so
    $M_H=O(frak(Y))$ by Lemma @lem:family-relative-projectivity-summands.

    To prove (ii), we apply @th:green-vertices-going-down(iii) again, to obtain
    $N in op("Ind") R H$ such that $M divides N^G$ and $D^* in op("vtx") N$. By
    @case:green-restricted-induction, $(N^G)_H=N plus.o O(frak(Y))$. Since
    $M!=O(frak(X))$, $D^* scripts(lt.eq.not)_G frak(X)$ by
    @lem:family-relative-projectivity-vertex, so
    $D^* scripts(lt.eq.not)_H frak(Y)$. By
    @lem:family-relative-projectivity-vertex again, $N$ is the unique
    indecomposable summand of $(N^G)_H$ which is not $O(frak(Y))$. By
    @th:green-vertices-going-down(ii), $M_H$ has an indecomposable summand with
    vertex $D^*$. Since $M_H divides (N^G)_H$ and $(N^G)_H=N plus.o O(frak(Y))$,
    this summand must be $N$. It follows that $M_H=N plus.o O(frak(Y))$,
    completing the proof of (ii).

    The significant feature of @case:green-restriction-summand is that, in case
    (ii), $N$ is the _unique_ indecomposable summand of $M_H$ not in
    $O(frak(Y))$. This phenomenon is the key to the proof of
    Theorem~@th:green-correspondence. The next result shows that the same thing
    happens in the opposite direction.
  ] <case:green-restriction-summand>],
  [#case[
    Let $N$ be an indecomposable $R H$-lattice with vertex $D^*<=D$. The
    following statements hold:
    #enum(
      numbering: "(i)",
      [If $N=O(frak(X))$, then also $N^G=O(frak(X))$.],
      [If $N!=O(frak(X))$, then $N^G=M plus.o O(frak(X))$ for some lattice
        $M in op("Ind") R G$ such that $N divides M_H$, and
        $D^* in op("vtx") M$.],
    )
    We first prove (i). Since $D^* in op("vtx") N$, $N$ is $(H,D^*)$-projective,
    and hence $N divides (N_(D^*))^H$ by Theorem
    @th:gaschutz-relative-projectivity. Then $N^G divides (N_(D^*))^G$ by
    transitivity of induction, and so $N^G$ is $(G,D^*)$-projective. Since
    $D^* scripts(lt.eq)_H frak(X)$ by
    Lemma~@lem:family-relative-projectivity-vertex, it follows that
    $N^G=O(frak(X))$, completing the proof of (i).

    #source(496)
    The proof of (ii) is more difficult. We first write
    $
      N^G=M_1 plus.o dots.c plus.o M_l,
      "with" M_i in op("Ind") R G,1<=i<=l.
    $
    From the proof of part (i) and @prop:relative-projectivity-properties(v),
    each module $M_i$ is $(G,D^*)$-projective, and hence each $M_i$ has a vertex
    $D_i$ such that
    $ D_i scripts(lt.eq)_G D^*<=D. $
    By @case:green-restriction-summand, for each $i$, $1<=i<=l$, we have either:
    #enum(
      numbering: "(a)",
      [$M_i=O(frak(X))$ and $(M_i)_H=O(frak(Y))$,],
      [$M_i!=O(frak(X))$ and $(M_i)_H$ has exactly one indecomposable direct
        summand which is $!=O(frak(Y))$.],
    )
    By @case:green-restricted-induction we also have
    #enum(numbering: "(a)", start: 3, [$ (N^G)_H=N plus.o O(frak(Y)). $])
    By the hypothesis of (ii), $N!=O(frak(X))$, and hence
    $D^* scripts(lt.eq.not)_H frak(X)$ by Lemma
    @lem:family-relative-projectivity-vertex. Then
    $D^* scripts(lt.eq.not)_H frak(Y)$ by @case:green-subgroup-comparison, and
    $N!=O(frak(Y))$, by @lem:family-relative-projectivity-vertex again. From
    (a)–(c) above, it follows that there is a unique indecomposable summand
    $M_(i_0)$ of $N^G$ such that $M_(i_0)!=O(frak(X))$. Moreover, $N$ is the
    unique indecomposable summand of $(M_(i_0))_H$ which is $!=O(frak(Y))$,
    according to (b). Finally, $M_(i_0)$ has vertex $D^*$, by
    @th:vertices-going-up, completing the proof.
  ] <case:green-induced-summand>],
  [#case[
    It is now easy to assemble a proof of @th:green-correspondence. Let
    $M in op("Ind") R G$, with $D^* in op("vtx") M$ for some subgroup $D^*$ in
    $frak(A)$. Then $D^* scripts(lt.eq.not)_G frak(X)$ by
    @eq:green-subgroup-families, so $M!=O(frak(X))$ by
    @lem:family-relative-projectivity-vertex, and $M_H$ has a uniquely
    determined indecomposable summand $N!=O(frak(Y))$, where $N$ has vertex
    $D^*$. Thus we have a well-defined map of isomorphism classes
    $ g:[M] arrow [N], $
    as in @th:green-correspondence. By @case:green-induced-summand, the map $g$
    is surjective. To prove it is injective, suppose that $N divides M_H$ where
    $N in op("Ind") R H$ and $M in op("Ind") R G$ both have vertex $D^*$ in
    $frak(A)$. We have to prove that the isomorphism class of $M$ is uniquely
    determined by these conditions, and for that, it is sufficient by
    @case:green-induced-summand to prove that $M divides N^G$. (Notice that this
    is closely related to the question as to whether both conditions (ii) and
    (iii) of Theorem~@th:green-vertices-going-down can be satisfied with the
    same module.) By @th:green-vertices-going-down(iii), applied to the
    $H$-conjugacy class containing the actual vertex $D^*$, choose
    $U in op("Ind") R H$ with vertex $D^*$ such that $M divides U^G$. Since $U$
    is $(H,D)$-projective, @case:green-restricted-induction gives
    $ (U^G)_H=U plus.o O(frak(Y)). $
    But $N divides M_H divides (U^G)_H$ and $N!=O(frak(Y))$. By
    @lem:family-relative-projectivity-summands, every indecomposable summand of
    $O(frak(Y))$ is $O(frak(Y))$, so the K-S-A Theorem forces $N tilde.equiv U$.
    Consequently $M divides N^G$, as required. This completes the proof that $g$
    is a bijection of isomorphism classes.
    #ed-note[
      The original choice of a $G$-conjugate vertex did not justify the
      comparison with the $H$-relative family $frak(Y)$. The choice with the
      specified $H$-conjugacy class is supplied by
      Theorem~@th:green-vertices-going-down(iii).
    ]

    The second statement of @th:green-correspondence is immediate from
    @case:green-restriction-summand and @case:green-induced-summand, and the
    final remark follows from @th:green-vertices-going-down(iv).
  ] <case:green-correspondence-bijection>],
)

=== Applications to Character Theory
<ss:green-correspondence-character-applications>

#source(497)
In this subsection, we shall apply the results of §@sec:vertices-sources and
§@ss:green-correspondence to character theory. Our presentation is based mainly
on Thompson's paper @bib:Thompson1967. The first part is devoted to general
results on characters afforded by $R G$-modules, with reference to questions
about projectivity and reduction mod $frak(p)$. The discussion then focuses on
the character theory of a group $G$ with a cyclic self-centralizing Sylow
$p$-subgroup $D$, which is a T.I. set. Examples will be given to show that this
configuration occurs frequently among simple groups which are minimal in some
sense. Such a subgroup $D$ is a special abelian subgroup. This situation was
studied previously in §@ss:exceptional-characters-ca-groups, and the results on
exceptional and non-exceptional characters relative to such a subgroup can be
applied (see Propositions @prop:sa-subgroup-special-classes and
@prop:exceptional-character-values). The main point of the discussion below is
that with the help of modular representations, we can obtain much sharper
versions of the results of §@ss:exceptional-characters-ca-groups. The summarized
version @rem:green-character-tables shows how, in this case, a remarkable amount
of information about the characters of $G$ can be lifted from the character
theory of a $p$-local subgroup of $G$. In Chapter~9 of Volume~II, these sharper
results will be applied to the study of blocks with cyclic defect groups. One
result along the way, of independent interest, is the determination of all
indecomposable $k G$-modules for certain Frobenius groups which occur as
normalizers of $p$-groups $D$ as above (see
@prop:cyclic-normal-sylow-indecomposables and
@prop:cyclic-kernel-frobenius-indecomposables).

Throughout this subsection, $G$ denotes a finite group, and $(K,R,k)$ a
$p$-modular system such that $char K=0$, $K$ is sufficiently large relative to
$G$, and $R G$ is a semiperfect ring. In this situation, all of the results of
§§@sec:cartan-brauer-triangle, @sec:vertices-sources and
@ss:green-correspondence are valid, and we shall frequently use the notation and
results established in those sections.

If $M$ is any $R G$-lattice, by the _ $K$-character of $G$ afforded by $M$_
#idx("character", "over K") we shall always mean the $K$-character $mu$ of $G$
afforded by the $K G$-module $K times.o_R M$. The values ${mu(x):x in G}$ can be
computed from an $R$-representation of $G$ relative to an $R$-basis of $M$,
without passing to $K times.o_R M$.

Suppose now that $U$ and $V$ are $K G$-modules affording characters $mu,nu$,
respectively. As in §@ss:relative-projectivity, we shall write $mu divides nu$
to indicate that $U divides V$ (that is, $U$ is isomorphic to a $K G$-direct
summand of $V$).

As preparation for the following discussion, the reader may wish to review the
properties of $R$-pure sublattices of $R G$-lattices, as described in
§@ss:modules-dedekind-domains.

Our first result asserts that summands of the character afforded by an
indecomposable projective lattice $M$ can be “taken off the top” of $M$.

#proposition[
  Let $P$ be an indecomposable projective $R G$-lattice, affording the
  $K$-character $tau$, and let $mu$ be a nonzero $K$-character of $G$ such that
  $mu divides tau$. Then there exists an $R$-pure $R G$-sublattice $N$ of $P$
  such that $P slash N$ affords $mu$, and $overline(P slash N)$ is an
  indecomposable $k G$-module.
] <prop:projective-character-quotient-lattice>
#proof[
  Let $V=K times.o_R P$, so $V$ is a semisimple $K G$-module, and write
  $tau=mu+nu$ for some character $nu$. Then correspondingly $V=U plus.o W$,
  where $U,W$ afford
  #source(498)
  $mu,nu$, respectively. Setting $N=W inter P$, we obtain an exact sequence of
  $R G$-lattices
  #projective-quotient-sequence
  since $N$ is $R$-pure in $P$ (see @prop:pure-sublattices-subspaces). Clearly
  $P slash N$ affords $mu$. (This part of the argument does not depend on $P$
  being an indecomposable projective module, and is a special case of
  @cor:full-order-lattice-existence below.)

  In order to prove that $overline(P slash N)$ (and hence also $P slash N$) is
  indecomposable, we note that the $R G$-homomorphism
  #projective-quotient-reduction
  defined by composition of maps, has the property that
  $frak(p)P subset.eq ker phi$. Therefore $overline(P slash N)$ is a homomorphic
  image of the indecomposable projective $k G$-module $overline(P)$, and is
  therefore indecomposable, since $overline(P)$ has a unique maximal submodule,
  by @prop:projective-cover-summary. This completes the proof.
]

#proposition[
  Let $M$ be an $R G$-lattice such that $overline(M)=N_1 plus.o P_1$, where
  $P_1$ is a projective $k G$-module. Then there exist an $R G$-lattice $N$ and
  a projective $R G$-lattice $P$ such that
  $
    M tilde.equiv N plus.o P,quad overline(N) tilde.equiv N_1,
    quad overline(P) tilde.equiv P_1.
  $
] <prop:projective-reduction-summand-lifting>
#proof[
  By @prop:projective-cover-summary,
  $P_1 tilde.equiv overline(P)=P slash frak(p)P$ for some projective
  $R G$-lattice $P$. Likewise, we may write $overline(M)=M slash frak(p)M$.
  Consider the diagram
  #projective-summand-lifting
  where $alpha,beta$ are natural maps, and $i,j$ arise from the direct sum
  decomposition $overline(M) tilde.equiv overline(P) plus.o N_1$. Thus, $j i=1$
  on $overline(P)$.

  Since $P$ is $R G$-projective, we can find a map $f in Hom_(R G) lr((P,M))$
  such that $beta f=i alpha$ on $P$. Likewise, since $M$ is $R$-projective, we
  can find a map $g in Hom_R lr((M,P))$ such that $alpha g=j beta$ on $M$. Then
  $ alpha g f=j beta f=j i alpha=alpha, $
  and consequently
  $ P=frak(p)P+(g f)P. $
  This implies that $P=(g f)P$ by Nakayama's Lemma, since $P$ is a f.g.
  $R$-module.
  #source(499)
  It follows now that $f$ is a monomorphism, and the exact sequence of
  $R G$-modules #named-equation(name: [$(ast)$])[
    $ 0 arrow P arrow^f M arrow M slash P arrow 0 $
  ] <eq:projective-summand-split-sequence>
  is split by the $R$-homomorphism $(g f)^(-1)g:M arrow P$, since $g f$ is an
  automorphism of the finite free $R$-module $P$. In particular, $M slash P$ is
  also a $R G$-lattice.

  Since $P$ is $R G$-projective, $P$ is also $(G,1)$-projective in the sense of
  @def:relative-projective-injective. But then $P$ is $(G,1)$-injective by
  @th:gaschutz-relative-projectivity. Since the sequence
  @eq:projective-summand-split-sequence is split over $R$, it follows that it is
  also split over $R G$. Thus
  $ M tilde.equiv P plus.o (M slash P) $
  as $R G$-modules, which completes the proof.
]

As a special case of @prop:projective-reduction-summand-lifting, it follows that
if $overline(M)$ is $k G$-projective, then $M$ is $R G$-projective. In this
connection, see @th:dvr-projectivity-reduction.

For the rest of this subsection, we shall assume that the finite group $G$ has a
cyclic Sylow $p$-subgroup $D$ of order $p^d$. Our main interest centers on the
case where the following holds:
$ D=C_G lr((D)),"and" D^* "is a T.I. set", $
(see @def:trivial-intersection-set), where $D^*=D-{1}$. We put $H=N_G lr((D))$.

It is clear from the conditions on $D$ that $D=C_G lr((x))$ for all $x in D^*$,
so $D$ is a special abelian subgroup of $G$ (see
@lem:ca-maximal-abelian-centralizers). Then by
@prop:sa-subgroup-special-classes(i), if $H>D$, then $H$ is a Frobenius group
with Frobenius kernel $D$. A further simplification is that each $p$-irregular
element is a $p$-element. Here are some examples of the above situation:
$ G=op("PSL")_2 lr((p)),D="Sylow" p "-subgroup of" G,p "odd"; $
$ G=A_5,p=3,5;quad G=A_6 tilde.equiv op("PSL")_2 lr((9)),p=5; $
$
  G=op("PSL")_2 lr((7)) tilde.equiv GL_3 lr((2)),p=3,7;
  quad G=SL_2 lr((8)),p=7;
$
$ G=op("PSL")_2 lr((11)),p=5,11;quad G=M_11,p=5,11. $
The results obtained below are helpful in determining the character tables of
all of the groups listed above.

Our first step is the determination of all indecomposable $k H$-modules, the key
fact being that $H$ has a cyclic normal Sylow $p$-subgroup $D$. We showed in
@bib:CurtisReiner1962[CR (64.6)] that there are at most $|H|$ distinct
indecomposable $k H$-modules, and that this maximum is achieved if and only if
$H slash D$ is abelian, and $k$ is sufficiently large relative to $H slash D$.
We shall need a more detailed version of this result for the case where $D$
satisfies the restrictive hypotheses described earlier. However, since this same
situation arises in many other contexts, we
#source(500)
shall begin with a more general discussion of indecomposable $k H$-modules. The
following result occurs frequently in the literature (see, for example,
Srinivasan~@bib:Srinivasan1960, O'Reilly~@bib:OReilly1965,
Berman~@bib:Berman1966, Lam–Reiner~@bib:Lam1969):

#proposition[
  Let $D$ be a cyclic normal Sylow $p$-subgroup of a finite group $H$, and let
  $k$ be any field of characteristic $p$, not necessarily a splitting field for
  $H$. Let ${U_i:1<=i<=s}$ be a basic set of projective indecomposable
  $k H$-modules, and let
  $ D=⟨x:x^(p^d)=1⟩,quad N=rad k D=(x-1)k D, $
  so $N$ is nilpotent of exponent $p^d$. Put
  $ M_(i j)=U_i slash N^j U_i,quad 1<=j<=p^d,1<=i<=s. $
  Then the $s dot p^d$ modules ${M_(i j)}$ are a full set of non-isomorphic
  indecomposable $k H$-modules.
] <prop:cyclic-normal-sylow-indecomposables>
#proof[
  For each $a in H$ we have $a N a^(-1)=N$ since $D ⊴ H$, and therefore
  $N^j U_i$ is a $k H$-submodule of $U_i$, for each $i$ and $j$. Furthermore, by
  @prop:projective-cover-summary the projective indecomposable $k H$-module
  $U_i$ has a unique maximal submodule $(rad k H)U_i$, with simple quotient
  $ F_i=U_i slash (rad k H)U_i,quad 1<=i<=s, $
  and these ${F_i}$ are a basic set of simple $k H$-modules. Since
  $N dot k H=k H dot N$ and $N$ is nilpotent, it is clear that
  $N subset.eq rad k H$, and thus $N^j U_i subset.eq (rad k H)U_i$ for each $i$
  and $j$. Therefore each $M_(i j)$ has a unique maximal submodule
  $(rad k H)U_i slash N^j U_i$, with simple quotient $F_i$. This shows that each
  $M_(i j)$ is indecomposable, and that $M_(i j) tilde.equiv M_(i' j')$ implies
  $i=i'$.

  Next, since each $U_i$ is $k H$-projective, it follows that its restriction
  $U_i|_D$ is $k D$-projective, and is therefore free as $k D$-module by
  @th:p-group-algebra-local. This implies that
  $ dim_k M_(i j)=j dot dim_k M_(i 1), $
  so no two of the modules ${M_(i j):1<=j<=p^d}$ can be isomorphic. We have
  therefore constructed $s dot p^d$ indecomposable $k H$-modules
  ${M_(i j):1<=j<=p^d,1<=i<=s}$, and it remains to prove that there are no
  others.

  By linear algebra, there are exactly $p^d$ indecomposable $k D$-modules, given
  by
  $
    T_j tilde.equiv k[x] slash (1-x)^j k[x]=k D slash N^j,
    quad 1<=j<=p^d,
  $
  and $dim_k T_j=j$ for each $j$. Since $D$ is a Sylow $p$-subgroup of $H$, each
  #source(501)
  $M in op("Ind") k H$ is $(H,D)$-projective by
  @prop:relative-projectivity-properties(ix), and hence $M divides T_j^H$ for
  some $j$. But
  $
    T_j^H=k H times.o_(k D)(k D slash N^j)
    tilde.equiv k H slash N^j k H,quad 1<=j<=p^d.
  $
  Since $k H$ is expressible as a direct sum of $U_i$'s with various
  multiplicities, say
  $ k H tilde.equiv product.co_(i=1)^s U_i^((n_i)), $
  it follows that
  $
    T_j^H tilde.equiv product.co_(i=1)^s (M_(i j))^((n_i)),
    quad 1<=j<=p^d.
  $
  This completes the proof that the ${M_(i j)}$ are a full set of indecomposable
  $k H$-modules, and establishes the proposition. Furthermore, since $k H$ is a
  free left $k D$-module on $e=|H:D|$ generators, it follows that
  $T_j^H|_D tilde.equiv T_j^((e))$ (this can also be deduced from the Subgroup
  Theorem), and therefore for each $i$, the restriction $M_(i j)|_D$ is
  isomorphic to a sum of copies of $T_j$.
]

#remarks[
  #enum(
    numbering: "(i)",
    [
      Since $D$ is a Sylow $p$-subgroup of $H$, the Schur–Zassenhaus Theorem
      tells us that $H=D times.r A$ for some subgroup $A$ of $H$. We have not
      used this fact anywhere in the above proof. Furthermore, the fact that $D$
      is a Sylow group was only used to deduce that every $k H$-module is
      $(H,D)$-projective. Thus, the above proof yields the following more
      general statement, which will be needed in Chapter~6 of Volume~II, in our
      discussion of relative Grothendieck rings.

      _Let $D$ be a cyclic normal $p$-subgroup of $H$. Then the modules
      ${M_(i j)}$ constructed above are a full set of non-isomorphic
      indecomposable $(H,D)$-projective $k H$-modules, and every
      $(H,D)$-projective $k H$-module is uniquely expressible as a direct sum of
      $M_(i j)$'s._
    ],
    [
      An analogous calculation, in which we determine all indecomposable
      representations of $H$ over the ring of $p$-adic integers, is given in the
      paragraphs following @eq:metacyclic-localized-indecomposable-lattices
      below.
    ],
  )
] <rem:cyclic-normal-relative-indecomposables>

We now resume the main current of our discussion, and prove:

#proposition[
  Let $H$ be a Frobenius group whose Frobenius kernel $D$ is cyclic of order
  $p^d$, and let $k$ be a field of characteristic $p$ which is sufficiently
  large relative to $H$. Let $A$ be a Frobenius complement in $H$. Then $A$ is
  an abelian group, whose order $e$ divides $p-1$, and we have:
  #enum(
    numbering: "(i)",
    [For each simple $k H$-module $F$, $dim_k F=1$.],
    [#source(502)There are exactly $|H|$ non-isomorphic indecomposable
      $k H$-modules ${M_(i j):1<=i<=e,1<=j<=p^d}$, and $dim M_(i j)=j$ for all
      $i,j$.],
    [If $M in op("Ind") k H$, then $M_D in op("Ind") k D$.],
    [All nonzero submodules of an indecomposable $k D$-module are
      indecomposable.],
  )
] <prop:cyclic-kernel-frobenius-indecomposables>
#idx("Frobenius group", target: [@prop:cyclic-kernel-frobenius-indecomposables])

The same statements hold when $H=D$ and $A=1$; in this case they follow directly
from @prop:cyclic-normal-sylow-indecomposables and the uniseriality of $k D$.

#proof[
  From §@ss:frobenius-groups we may write $H=D times.r A$, and $A$ acts on $D$
  without fixed points, since $C_H lr((D))=D$. Then $A$ is isomorphic to a
  subgroup of $Aut D$, so $A$ is abelian of order $e$, where $e$ divides
  $phi(p^d)=p^(d-1)(p-1)$. Since $|A|$ and $|D|$ are relatively prime because
  $D$ is a Sylow $p$-subgroup of $H$, it follows that $e divides (p-1)$, as
  claimed.

  Now $A$ is abelian group whose order $e$ is prime to $p$, and $k$ is a
  sufficiently large field of characteristic $p$, so the algebra $k A$ is a
  split semisimple $k$-algebra. Let ${delta_1,dots,delta_e}$ be the primitive
  idempotents in the commutative algebra $k A$; then the simple $k A$-modules
  are ${k A dot delta_i:1<=i<=e}$, and
  $ k A=plus.o_(i=1)^e k A dot delta_i=plus.o_(i=1)^e k delta_i, $
  with $dim_k k delta_i=1$ for each $i$. We have therefore
  $
    k H tilde.equiv k H times.o_(k A) k A
    =plus.o_(i=1)^e k H dot delta_i=plus.o_(i=1)^e k D dot delta_i.
  $
  Since $k D dot delta_i$ is a homomorphic image of $k D$, comparing dimensions
  of both sides of the above shows that
  $ dim_k k H dot delta_i=p^d,quad 1<=i<=e, $
  and $k H dot delta_i$ is isomorphic to $k D$ as $k D$-module. Setting
  $ U_i=k H dot delta_i=k D dot delta_i,quad 1<=i<=e, $
  it follows that the ${U_i}$ are indecomposable projective $k H$-modules.
  Further, by @th:p-group-algebra-local and Clifford's Theorem, we know that $D$
  acts trivially on each simple $k H$-module, so the simple $k H$-modules can be
  identified with the simple $k A$-modules ${k delta_i:1<=i<=e}$. By
  @prop:projective-cover-summary, it follows that the ${U_i:1<=i<=e}$ are a
  basic set of projective indecomposable $k H$-modules.

  We now apply the Proposition @prop:cyclic-normal-sylow-indecomposables. Since
  $k H=plus.o_(i=1)^e U_i$, it follows that
  $ T_j^H tilde.equiv product.co_(i=1)^e M_(i j), $
  using the notation of the proof of @prop:cyclic-normal-sylow-indecomposables.
  Comparing dimensions of both
  #source(503)
  sides, we conclude that $dim M_(i j)=dim T_j=j$, and that
  $M_(i j)|_D tilde.equiv T_j$. This completes the proof of (i)–(iii), while
  (iv) is obvious from the formula for $T_j$, so Proposition
  @prop:cyclic-kernel-frobenius-indecomposables is established.
]

#proposition[
  Let $H$ be as in @prop:cyclic-kernel-frobenius-indecomposables, and let
  $(K,R,k)$ be a $p$-modular system such that $K$ is sufficiently large, of
  characteristic zero, and $R H$ is semiperfect. Let $M$ be an indecomposable
  $R H$-lattice such that $overline(M)$ is indecomposable, and let $mu$ be the
  $K$-character of $H$ afforded by $M$. Then $(mu_D,phi)<=1$ for all linear
  characters $phi$ of $D$.
] <prop:cyclic-kernel-lattice-character-multiplicity>
#proof[
  From @cor:modular-system-sufficiently-large-fields, $k$ is sufficiently large
  relative to $H$, so we may apply @prop:cyclic-kernel-frobenius-indecomposables
  to conclude that $overline(M)_D$ and each of its nonzero submodules is
  indecomposable. Therefore every nonzero $R$-pure $R D$-submodule of $M$ is
  indecomposable, since it remains indecomposable after reduction mod $frak(p)$.

  Now let $phi$ be a linear $K$-character of $D$, and define
  $ M_phi={m in M:(x-phi(x))m=0 quad forall x in D}. $
  Then $M_phi=(K M_phi) inter M$, so $M_phi$ is a pure $R$-sublattice of $M$, by
  @prop:pure-sublattices-subspaces. It is also clear that $M_phi$ is an
  $R D$-submodule of $M_D$. If $M_phi=0$, then $(mu_D,phi)_D=0$, since any
  $phi$-eigenvector of $K M$ has a nonzero $R$-multiple in $M$. The assertion
  for $phi$ is then immediate. Otherwise $M_phi in op("Ind") R D$. We next show
  that
  $ rank_R M_phi=(mu_D,phi)_D. $
  Let $V=K M$; then $V$ affords $mu$, and $(mu_D,phi)_D$ is the $K$-dimension of
  the homogeneous component $V_phi$ of $V_D$ affording a multiple of $phi$. Now
  $V_D$ is a semisimple $K D$-module, and since $phi$ is a linear character of
  the abelian group $D$, we have
  $ V_phi={v in V:(x-phi(x))v=0 quad forall x in D}. $
  Then $M_phi=V_phi inter M$, and $V_phi=K M_phi$, so
  $rank_R M_phi=(mu_D,phi)_D$, as claimed. Finally, since
  $M_phi in op("Ind") R D$, it follows that the $R$-rank of $M_phi$ is $<=1$,
  because any $R$-decomposition of $M_phi$ is an $R D$-decomposition, by the
  preceding step. This completes the proof of
  @prop:cyclic-kernel-lattice-character-multiplicity.
]

We shall now apply the preceding results, along with the Green correspondence
@th:green-correspondence, to the character theory of a finite group $G$
containing the configuration of @prop:cyclic-kernel-frobenius-indecomposables.

#proposition[
  Let $D$ be a cyclic self-centralizing Sylow $p$-subgroup of $G$ which is a
  T.I. set, and let $H=N_G lr((D))$, with the cyclic-kernel configuration of
  @prop:cyclic-kernel-frobenius-indecomposables, allowing $H=D$. Let $(K,R,k)$
  be a $p$-modular system with $K$ sufficiently large. Then for every
  indecomposable non-projective $R G$-lattice $M$ for which $overline(M)$ is
  also indecomposable, there exists an indecomposable non-projective
  $R H$-lattice $L$
  #source(504)
  such that
  $
    M divides L^G,quad overline(L) in op("Ind") k H,
    "and" M_H=L plus.o Q "for some" Q in cal(P)(R H).
  $
] <prop:green-correspondence-indecomposable-reduction>
#proof[
  If $H=G$, take $L=M$ and $Q=0$; all the assertions are immediate. We may
  therefore assume $H<G$. By @prop:sa-subgroup-special-classes(i), if $H>D$,
  then $H$ is a Frobenius group with Frobenius kernel $D$, as in
  @prop:cyclic-kernel-frobenius-indecomposables; the case $H=D$ is allowed as
  well. We shall apply the Green Correspondence @th:green-correspondence, to the
  admissible triple of group $(G,H,D)$. The families of subgroups $frak(X)$ and
  $frak(A)$ in @eq:green-subgroup-families then become
  $ frak(X)={attach(D, tl: x) inter D:x in G-H}={1} $
  (since $D$ is a T.I. set), and
  $
    frak(A)={D^*<=D:D^* scripts(lt.eq.not)_G frak(X)}
    ="set of all non-trivial subgroups of" D.
  $
  Therefore an $R G$-lattice $M$ is $O(frak(X))$ if and only if $M$ is
  $(G,1)$-projective, that is (see §@ss:relative-projectivity), if and only if
  $M$ is $R G$-projective. Further, by @lem:family-relative-projectivity-vertex,
  $frak(A)$ contains a vertex of $M$ if and only if $M$ is not $R G$-projective.

  By Theorem~@th:green-correspondence and the above remarks, there exists a
  bijection
  $ [M] arrow.l.r [g[M]]=[L] $
  from isomorphism classes of $R G$-lattices $M$ such that $M in op("Ind") R G$
  and $M in.not cal(P)(R G)$, to isomorphism classes of $R H$-lattices $L=g(M)$,
  such that $L in op("Ind") R H$ and $L in.not cal(P)(R H)$. Moreover, if the
  original $R G$-lattice $M$ corresponds to $g(M)=L$, then we have
  $
    M divides L^G,"and" M_H tilde.equiv L plus.o Q,
    "with" Q in cal(P)(R H).
  $

  By hypothesis, $overline(M) in op("Ind") k G$; further,
  $overline(M) in.not cal(P)(k G)$ by @prop:projective-reduction-summand-lifting
  (with $N_1=0$). We may then apply Green's Theorem~@th:green-correspondence to
  $overline(M)$, to obtain an indecomposable $k H$-module $L_1$ such that
  $L_1 in.not cal(P)(k H)$, and
  $
    overline(M) divides L_1^G,"and"
    overline(M)_H tilde.equiv L_1 plus.o Q_1
    "for some" Q_1 in cal(P)(k H).
  $
  Then
  $ overline(L) plus.o overline(Q) tilde.equiv L_1 plus.o Q_1, $
  and both $overline(Q),Q_1 in cal(P)(k H)$. Thus $L_1$ is the unique
  non-projective indecomposable summand of $overline(L)$. Then necessarily
  $overline(L) tilde.equiv L_1$, since otherwise $overline(L)$ would have a
  non-trivial projective summand, and $L$ would therefore be decomposable by
  @prop:projective-reduction-summand-lifting. This completes the proof of
  @prop:green-correspondence-indecomposable-reduction.
]

We can now combine the preceding results to obtain the following proposition,
which will yield new information about the exceptional characters associated
with the subgroup $D$.

#source(505)
#proposition[
  Let $G$ satisfy the hypotheses of
  @prop:green-correspondence-indecomposable-reduction, and let $mu$ be a
  $K$-character of $G$ such that $mu divides tau$, where $tau$ is the
  $K$-character afforded by some indecomposable projective $R G$-lattice $P$ (as
  in @prop:projective-character-quotient-lattice). Define
  $
    h(mu)=max_(phi,phi' in Irr D)
    {|(mu_D,phi)-(mu_D,phi')|}.
  $
  Then $h(mu)<=1$.
] <prop:projective-character-restriction-height>
#proof[
  If $mu=0$, then $h(mu)=0$ and the assertion is immediate. We may therefore
  assume $mu!=0$. By @prop:projective-character-quotient-lattice, there exists
  an $R$-pure $R G$-sublattice $N$ of $P$ such that $M=P slash N$ affords $mu$,
  and $overline(M) in op("Ind") k G$. There are two cases to consider:
  #case-list(
    numbering: "(i)",
    [#case[
      Suppose $M$ is projective. Then $M=P slash N$ implies $M divides P$, and
      hence $M tilde.equiv P$, since $P$ is indecomposable. Then $mu=tau$, and
      for each linear character $phi$ of $D$, we have
      $
        (tau_D,phi)=|D|^(-1)sum_(x in D) tau(x)phi(x^(-1))
        =|D|^(-1)tau(1)
      $
      by @th:projective-characters-supported-p-regular, since $1$ is the only
      $p'$-element in $D$. In this case clearly $h(mu)=0$.
    ] <case:projective-character-height-zero>],
    [#case[
      We now assume $M$ is not projective, and apply Proposition
      @prop:green-correspondence-indecomposable-reduction. Then
      $ M_H=L plus.o Q,"with" L in op("Ind") R H,Q in cal(P)(R H), $
      and we have
      $ mu_H=lambda+eta, $
      where $lambda$ and $eta$ are the $K$-characters of $H$ afforded by $L$ and
      $Q$, respectively. Now $Q in cal(P)(R H)$, so
      $ (eta_D,phi)-(eta_D,phi')=0 $
      for all $phi in Irr D$, by Case~@case:projective-character-height-zero. By
      @prop:green-correspondence-indecomposable-reduction, it follows that $L$
      satisfies the hypotheses of
      @prop:cyclic-kernel-lattice-character-multiplicity, and by
      @prop:cyclic-kernel-lattice-character-multiplicity we have
      $ 0<=(lambda_D,phi)<=1 quad forall phi in Irr D. $
      Then, for all linear characters $phi$ and $phi'$ of $D$, we obtain
      $
        |(mu_D,phi)-(mu_D,phi')|
        =|(lambda_D,phi)-(lambda_D,phi')+(eta_D,phi)-(eta_D,phi')| \
        =|(lambda_D,phi)-(lambda_D,phi')|<=1,
      $
      as required.
    ] <case:nonprojective-character-height-one>],
  )
]

#source(506)
We now return to the study of the exceptional characters associated with the
subgroup $D$, where $D$ is a cyclic self-centralizing Sylow $p$-subgroup of $G$,
and $D$ is a T.I. set. By @prop:green-correspondence-indecomposable-reduction,
$H=N_G lr((D))$ has cyclic quotient $H slash D$; if $H>D$, it is a Frobenius
group with Frobenius kernel $D$. Letting $D^*=D-{1}$, we have $C_G lr((d))=D$
for all $d in D^*$, so $D$ is a special abelian subgroup in the sense of
§@ss:exceptional-characters-ca-groups.

We first recall some of the information contained in Propositions
@prop:sa-subgroup-special-classes and @prop:exceptional-character-values. We set
$ m=|D|=p^d,quad e=|H:D|,quad n=(m-1) slash e, $
as in @prop:sa-subgroup-special-classes. For the rest of the discussion, we
shall assume that $n>=2$. By @prop:sa-subgroup-special-classes, the set $D^*$ is
the union of a set of exactly $n$ special classes in $H$.

Let $mu_0=1_H,mu_1,dots,mu_(e-1)$ be the $e$ linear characters of $H slash D$,
inflated to $H$; these are exactly the linear characters of $H$ trivial on $D$.
If $e>1$, then $D$ is the derived group of $H$, so these are all the linear
characters of $H$. By @prop:sa-subgroup-special-classes(iii), $H$ has exactly
$n$ distinct irreducible characters ${psi_1,dots,psi_n}$ nontrivial on $D$, all
of degree $e$, induced from non-trivial irreducible characters $phi$ of $D$.
When $e=1$, we have $H=D$, and these $psi_i$ are themselves linear. By
@prop:sa-subgroup-special-classes(iv) a $ZZ$-basis for the virtual characters of
$H$ vanishing off the special classes is given by
$ lambda_i=psi_i-psi_n,quad 1<=i<=n-1, $
together with any one additional character of the form
$ 1_D^H-psi_i,quad 1<=i<=n. $
Then by @prop:sa-subgroup-special-classes(iv) there exist non-trivial
irreducible characters
$ {zeta_1,dots,zeta_n;theta_1,dots,theta_f;chi_1,dots,chi_h} $
of $G$ which, together with the trivial character $1_G$, constitute all
characters in $Irr G$. There also exists a sign $epsilon=plus.minus 1$, and
multiplicities $a$, and $c_j!=0$, $1<=j<=f$, such that
$
  lambda_i^G=(psi_i-psi_n)^G=epsilon(zeta_i-zeta_n),quad 1<=i<=n-1,
$ <eq:green-exceptional-character-differences>
and
$
  Gamma_i=(1_D^H-psi_i)^G
  =1_G-epsilon zeta_i+a sum_(i=1)^n zeta_i+sum_(j=1)^f c_j theta_j,
  quad 1<=i<=n.
$ <eq:green-induced-virtual-character-expansion>
The constants $epsilon,a$ and ${c_j}$ are independent of $i$, $1<=i<=n$, and are
related by the formula (see @prop:exceptional-character-values(iii)).
$
  e=a^2(n-1)+(a-epsilon)^2+sum_(j=1)^f c_j^2.
$ <eq:green-character-multiplicity-square-sum>

#source(507)
The characters ${zeta_1,dots,zeta_n}$ are called _exceptional characters_
(relative to $D$)#idx("exceptional character") #idx(
  "character",
  "exceptional",
)\; the characters ${theta_1,dots,theta_f;chi_1,dots,chi_h}$ are called
_non-exceptional_#idx("non-exceptional character")#idx(
  "character",
  "non-exceptional",
), and are arranged so that the first $f$ characters ${theta_i}$ appear with
non-zero multiplicities ${c_i}$ in the virtual characters $Gamma_i$, $1<=i<=n$,
and the remaining $h$ non-exceptional characters ${chi_j}$ appear with zero
multiplicity in all the ${Gamma_i}$.

Various other facts, from §@ss:exceptional-characters-ca-groups, about the
values of $zeta_i$ and $theta_j$ and $chi_j$ will be quoted when we need them.
We can now state the main result of this subsection.

#theorem[
  Let $G,D,H=N_G lr((D))$, etc., be as in
  @prop:green-correspondence-indecomposable-reduction, and assume that
  $n=(m-1) slash e>=2$. Then the following statements hold:
  #enum(
    numbering: "(i)",
    [The exceptional characters ${zeta_i}$ have the same degree, which is prime
      to $p$. The non-exceptional characters ${theta_j:1<=j<=f}$ have degrees
      satisfying $theta_j lr((1)) equiv plus.minus 1 (mod p)$. The degrees of
      the characters ${chi_j:1<=j<=h}$ are all divisible by $|D|$.],
    [Up to sign, the values of the ${zeta_i:1<=i<=n}$ agree with the values of
      the ${psi_i}$ on the special classes. More precisely, we have
      $ zeta_i|_(D^*)=epsilon psi_i|_(D^*),quad 1<=i<=n. $
      The values of the non-exceptional characters ${theta_j:1<=j<=f}$ on the
      elements of $D^*$ are all $plus.minus 1$. The non-exceptional characters
      ${chi_j:1<=j<=h}$ vanish on $D^*$.],
    [The exceptional characters agree on the elements of $G_(p')$:
      $ zeta_i lr((x))=zeta_j lr((x)),quad forall x in G_(p'),1<=i,j<=n. $
      The values of the non-exceptional characters ${theta_j}$ on $G_(p')$ are
      related to the values of ${zeta_i}$ as follows:
      $
        delta zeta_1 lr((x))=1+sum_(i=1)^f delta_i theta_i lr((x)),
        quad forall x in G_(p'),
      $
      where ${delta,delta_1,dots,delta_f}$ are all $plus.minus 1$, and are
      independent of $x in G_(p')$.],
    [The number of non-exceptional characters ${theta_i}$ is given by $f=e-1$.],
    [The decomposition numbers ${d_(i j)}$ (see @def:decomposition-map-matrix)
      are $0$ or $1$ for all irreducible characters of $G$.],
  )
] <th:green-cyclic-sylow-character-values>

We first prove a crucial preliminary result:

#source(508)
#lemma[
  Let
  $
    Gamma_i=1_G-epsilon zeta_i+a sum_(i=1)^n zeta_i
    +sum_(j=1)^f c_j theta_j,quad 1<=i<=n,
  $
  as in @eq:green-induced-virtual-character-expansion. Then $a=0$ or $epsilon$,
  $|c_j|=1$ for $1<=j<=f$, and $f=e-1$.
] <lem:green-character-multiplicity-bounds>
#proof[
  We first observe that since $R G$ is projective, the regular character of $G$
  is a sum of characters afforded by the indecomposable projective
  $R G$-modules. Hence every irreducible character $zeta$ of $G$ satisfies the
  condition $zeta divides tau$, for some character $tau$ afforded by an
  indecomposable projective $R G$-module, as in
  @prop:projective-character-restriction-height. We first apply
  @prop:projective-character-restriction-height to a non-exceptional character
  $theta_i$, $1<=i<=f$, and obtain
  $
    1>=h(theta_i)
    &=max_(phi,phi' in Irr D){|(phi,(theta_i)_D)-(phi',(theta_i)_D)|} \
    &=max_(phi,phi'){|(phi-phi',(theta_i)_D)|}
    =max_(phi,phi'){|((phi-phi')^G,theta_i)|} \
    &=max{|((1_D^H-psi_j)^G,theta_i)|,
      |((psi_j-psi_(j'))^G,theta_i)|}
    =max{|c_i|,0}=|c_i|
  $
  by @eq:green-exceptional-character-differences and
  @eq:green-induced-virtual-character-expansion, and the definition of the
  characters ${psi_i}$. Since $c_i!=0$ for $1<=i<=f$ by definition, we have
  $|c_i|=1$.

  We next compute $h(zeta_i)$ for an exceptional character. Following the
  calculation above, we note that for all $phi,phi' in Irr D$, $(phi-phi')^G$ is
  up to sign or zero, either $1_D^G-psi_i^G=Gamma_i$, $1<=i<=n$, or
  $(psi_i-psi_j)^G$. Moreover, by @eq:green-exceptional-character-differences
  and @eq:green-induced-virtual-character-expansion, we have
  $
    ((psi_i-psi_j)^G,zeta_i)=epsilon,
    quad ((psi_j-psi_l)^G,zeta_i)=0 "if" i!=j,l,
  $
  $ (Gamma_j,zeta_i)=a "(if" i!=j ") or" a-epsilon "(if" i=j ")." $
  Hence
  $ 1>=h(zeta_i)=max{|epsilon|,|a-epsilon|,|a|}, $
  and we conclude that $a=0$ or $epsilon$.

  We now apply this information to the formula
  @eq:green-character-multiplicity-square-sum, which becomes either
  $ e=1+f "if" a=0,"or" e=(n-1)+f "if" a=epsilon. $
  It therefore suffices to prove that in the second case we have $n=2$. For this
  purpose, we prove that if $(zeta_i,tau)!=0$ for some projective indecomposable
  #source(509)
  character $tau$, then $(sum_(i=1)^n zeta_i,tau)!=0$. We have, for $j!=i$,
  $
    (zeta_i-zeta_j,tau) & =epsilon((psi_i-psi_j)^G, tau) \
                        & =epsilon((xi_i-xi_j)^G, tau)
                          =epsilon(xi_i-xi_j, tau_D)_D,
  $
  where $xi_i$ and $xi_j$ are linear characters of $D$ such that $psi_i=xi_i^H$
  and $psi_j=xi_j^H$. Then, by @th:projective-characters-supported-p-regular, we
  clearly have $(zeta_i-zeta_j,tau)=0$, since $tau$ vanishes on $D^*$, and
  $xi_i lr((1))=xi_j lr((1))$. Thus all exceptional characters have the same
  positive multiplicity in $tau$, so $sum_(i=1)^n zeta_i divides tau$. We now
  assume $a=epsilon$, and obtain, for a linear character $xi$ of $D$ such that
  $xi^H=psi_1$,
  $
    (1_D-xi,sum_(i=1)^n zeta_i|_D)
    =(Gamma_1,sum_(i=1)^n zeta_i)=epsilon(n-1),
  $
  by Frobenius Reciprocity. By @prop:projective-character-restriction-height, it
  follows that
  $ |epsilon(n-1)|<=h(sum_(i=1)^n zeta_i)<=1, $
  and therefore $n=2$, completing the proof.
]

#corollary[
  The multiplicity $a$ in @eq:green-induced-virtual-character-expansion is zero
  unless $n=2$. In that case $a=0$ or $epsilon$, and in the latter case, we may
  interchange $zeta_1$ and $zeta_2$, to obtain the formulas
  @eq:green-exceptional-character-differences and
  @eq:green-induced-virtual-character-expansion, with $epsilon$ replaced by
  $-epsilon$, and $a=0$.
] <cor:green-exceptional-character-sign-choice>
#proof[
  By the proof of Lemma~@lem:green-character-multiplicity-bounds, it suffices to
  consider $n=2$ and $a=epsilon$. For either sign of $epsilon$, formulas
  @eq:green-exceptional-character-differences and
  @eq:green-induced-virtual-character-expansion give
  $ (psi_1-psi_2)^G=epsilon(zeta_1-zeta_2), $
  $
    Gamma_1=1_G+epsilon zeta_2+sum c_j theta_j,
    quad Gamma_2=1_G+epsilon zeta_1+sum c_j theta_j.
  $
  Put $zeta'_1=zeta_2$, $zeta'_2=zeta_1$, $epsilon'=-epsilon$, and
  $a'=a-epsilon=0$. Then
  $ (psi_1-psi_2)^G=epsilon'(zeta'_1-zeta'_2), $
  $
    Gamma_1=1_G-epsilon' zeta'_1+sum c_j theta_j,
    quad Gamma_2=1_G-epsilon' zeta'_2+sum c_j theta_j.
  $
  These are the required formulas with the new sign $epsilon'$ and $a'=0$.
]

#proof(head: emph[Proof of Theorem~@th:green-cyclic-sylow-character-values.])[
  #enum(
    numbering: "(i)",
    [
      By @lem:green-character-multiplicity-bounds, the multiplicities ${c_j}$
      are all $plus.minus 1$, so the degrees
      $theta_j lr((1)) equiv plus.minus 1 (mod p^d)$, because of
      @prop:exceptional-character-values(iv). By
      @lem:green-character-multiplicity-bounds and
      @cor:green-exceptional-character-sign-choice,
      #source(510)
      we may assume that $a=0$, and that
      $ Gamma_1=1_G-epsilon zeta_1+sum_(j=1)^(e-1) c_j theta_j. $
      Then $Gamma_1=(1_D^H-psi_1)^G$ vanishes at the identity, and we obtain
      $ 0=1-epsilon zeta_1 lr((1))+sum_(j=1)^(e-1) c_j theta_j lr((1)). $
      By @prop:exceptional-character-values(iv) again,
      $theta_j lr((1)) equiv c_j (mod p)$, and taking congruences mod $p$, we
      have, since $|c_j|=1$ for $1<=j<=e-1$,
      $ 0 equiv 1-epsilon zeta_1 lr((1))+e-1 (mod p), $
      so $zeta_1 lr((1)) equiv epsilon e (mod p)$. Since $e=|H:D|$ is prime to
      $p$, and all the exceptional characters have the same degree by
      @prop:exceptional-character-values(i), it follows that the degrees
      ${zeta_i lr((1))}$ are all prime to $p$.

      Now let $chi in Irr G$ be distinct from
      ${1_G,zeta_1,dots,zeta_n,theta_1,dots,theta_(e-1)}$. Then by
      @eq:green-induced-virtual-character-expansion we have $(Gamma_i,chi)=0$,
      and hence $(1_D^H-psi_i,chi_H)=0$, $1<=i<=n$. It follows that
      $(1_D-xi,chi_D)=0$ for all non-trivial characters $xi$ of $D$, by the
      definition of the characters ${psi_i}$. Therefore $chi_D$ is a multiple of
      the regular character of $D$, and we have $chi(1) equiv 0 (mod |D|)$,
      completing the proof of (i). (For another proof of the last step, see
      @prop:exceptional-character-values(iv).)
    ],
    [
      By @cor:green-exceptional-character-sign-choice we may assume that $a=0$
      in formula @eq:green-induced-virtual-character-expansion. Now
      ${lambda_1,dots,lambda_(n-1),1_D^H-psi_1}$ form a $ZZ$-basis for the
      elements of $"ch" K H$ vanishing off $D^*$, and we have
      $ (1_D^H-psi_1)^G=1_G-epsilon zeta_1+sum c_j theta_j. $
      We therefore have, for the matrices $(a_(i j))$ and $(b_(i j))$ in
      Theorem~@th:suzuki-special-class-character-values,
      $b_(i j)=epsilon a_(i j)$, $1<=i<=n$, where the indices $j$ correspond to
      the characters ${zeta_1,dots,zeta_n}$ and ${psi_1,dots,psi_n}$,
      respectively. By Theorem~@th:suzuki-special-class-character-values, we
      then obtain $zeta_i|_(D^*)=epsilon psi_i|_(D^*)$, $1<=i<=n$, as required
      in part (ii).

      We have $theta_j lr((x))=plus.minus 1$ for all $x in D^*$ and $1<=j<=e-1$,
      by @prop:exceptional-character-values(iv), and the fact that all the
      multiplicities ${c_j}$ are $plus.minus 1$. Finally, the characters
      ${chi_j:1<=j<=h}$ all satisfy the condition
      $chi_j lr((1)) equiv 0 (mod |G|_p)$ by part (i), and hence vanish on $D^*$
      by @th:gallagher-character-vanishing (see also
      @prop:defect-zero-character-projective-simple).
    ],
    [
      The first statement follows since
      $ zeta_i-zeta_j=epsilon(psi_i-psi_j)^G, $
      #source(511)
      and hence vanishes off the $G$-conjugates of $D^*$, for all $i$ and $j$.
      For the second statement, we know that $Gamma_1$ also vanishes off the
      $G$-conjugates of $D^*$, so that for all $x in G_(p')$ we have
      $
        0=Gamma_1 lr((x))=1-epsilon zeta_1 lr((x))
        +sum_(j=1)^(e-1) c_j theta_j lr((x)),
      $
      (since $a=0$). This completes the proof of (iii), since $|c_j|=1$ for all
      $j$.
    ],
    [
      has been proved in @lem:green-character-multiplicity-bounds.
    ],
    [
      We have already shown in the proof of
      @lem:green-character-multiplicity-bounds that all exceptional characters
      have equal multiplicities in each indecomposable projective character.
      Thus, if $chi$ is any one of the characters
      ${1,sum_(i=1)^n zeta_i,theta_1,dots,theta_(e-1)}$, then $chi divides tau$
      for some indecomposable projective character $tau$. We assert that for any
      such character $chi$, we have $h(chi)>=1$. This follows at once from the
      formulas,
      $ (1_D-xi,1_D)=(Gamma_1,1_G)=1, $
      $ (1_D-xi,(sum zeta_i)_D)=(Gamma_1,sum_(i=1)^n zeta_i)=-epsilon, $
      $ (1_D-xi,(theta_j)_D)=c_j=plus.minus 1, $
      where $xi in Irr D$ and $xi^H=psi_1$, and
      $Gamma_1=1_G-epsilon zeta_1+sum c_j theta_j$, since we have $a=0$. By
      @prop:projective-character-restriction-height, we then have $h(2 chi)>=2$
      for any character $chi$ as above, and hence $2 chi$ is not a
      character-subsum of any indecomposable projective character $tau_i$:
      otherwise @prop:projective-character-restriction-height would give
      $h(2 chi)<=1$. By @th:projective-characters-supported-p-regular, we have
      $tau_i=sum_(j=1)^r d_(j i)zeta^j$. Thus the decomposition numbers
      corresponding to $1_G$ or ${theta_j:1<=j<=e-1}$ are $0$ or $1$. On the
      other hand, by the proof of Lemma
      @lem:green-character-multiplicity-bounds, the multiplicity of any
      exceptional character ${zeta_i:1<=i<=n}$ in one of the ${tau_i}$ is the
      same as the multiplicity of $sum_(i=1)^n zeta_i$, and hence is less than
      $2$. Finally, for the non-exceptional characters ${chi_j:1<=j<=h}$ of
      defect zero (see @prop:defect-zero-character-projective-simple and part
      (i)), the corresponding decomposition numbers are equal to one or zero, by
      @prop:defect-zero-character-projective-simple, completing the proof of the
      theorem.
    ],
  )
]

#remarks(name: [Interpretation of
  Theorem~@th:green-cyclic-sylow-character-values])[
  The information in Theorem~@th:green-cyclic-sylow-character-values can be
  summarized conveniently in terms of the character tables of $H$ and $G$. (For
  a numerical illustration, see the character table of $A_5$, for $p=5$,
  discussed in §@ss:a5-exceptional-characters.)

  In the character table of $H$, the entries in the matrix $upright(bold(A))$
  can be found, in any particular case, from the definition of the ${psi_i}$ as
  induced characters. The matrix $upright(bold(B))$ has all entries equal to
  $1$. The characters $mu_1,dots,mu_(e-1)$ are exactly the nonprincipal
  characters of $H$ trivial on $D$; they are all the nontrivial linear
  characters of $H$ only if $e>1$. In the following abstract schemas the blocks
  for $mu$ and $theta$ are absent when $e=1$; the $psi$-characters then have
  degree $1$.

  #source(512)
  #green-character-table-h
  #green-character-table-g
  #idx("character", "table", target: [@rem:green-character-tables])

  In the table for $G$, the degrees of the characters are described by
  congruences mod $p$, or mod $|D|$, where $|D|=p^d$. We note first that the
  characters ${1_G,zeta_1,dots,zeta_n,theta_1,dots,theta_(e-1)}$ constitute all
  characters of $G$ whose degrees are prime to $p$. Later, in Chapter~9 of
  Volume~II, we shall see that these characters form the principal block of $G$.

  The values of these characters on the $p$-elements are almost lifted from the
  part of the character table of $H$ corresponding to the $p$-elements. Thus,
  the values of the ${zeta_i}$ differ by the sign $epsilon$ from the values of
  the ${psi_i}$ on the $p$-classes. The number of non-exceptional characters
  ${theta_i}$ is equal to the number of nonprincipal characters of $H$ trivial
  on $D$, and their values on the $p$-elements are given by the matrix
  $upright(bold(B))'$ whose $i$-th row is the constant vector $(c_i,dots,c_i)$,
  #source(513)
  where $c_i=(theta_i,Gamma_1)$, $1<=i<=e-1$, and $Gamma_1$ is given by
  @eq:green-induced-virtual-character-expansion. Since $|c_i|=1$ for all $i$,
  the matrix $upright(bold(B))'$ is obtained from the corresponding matrix
  $upright(bold(B))$ in the table for $H$, by changing (at most) the signs of
  the rows. Finally, the other non-exceptional characters ${chi_i}$ vanish on
  the $p$-classes.
] <rem:green-character-tables>
