#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/31-genus.typ": *

== Genus <sec:genus>

Throughout this section, $R$ denotes a Dedekind domain with quotient field $K$,
and $Lambda$ is an $R$-order in a separable f.d. $K$-algebra $A$. To avoid
trivial cases, we assume always that $R!=K$. Let $P$ range over the maximal
ideals of $R$, and let $R_P$ denote the localization of $R$ at $P$, and
$hat(R)_P$ the $P$-adic completion of $R$ (or of $R_P$).

By @th:order-contained-in-maximal-order, there exists a maximal $R$-order
$Lambda'$ in $A$ which contains $Lambda$. Then for each $P$,
$Lambda_P subset.eq Lambda'_P$ and $Lambda'_P$ is a maximal $R_P$-order in $A$.
Thus $Lambda_P$ fails to be a maximal $R_P$-order precisely when
$Lambda_P!=Lambda'_P$. We put
$
  S(Lambda)={P:Lambda_P!="maximal" R_P"-order in" A}
  ={P:Lambda_P!=Lambda'_P}.
$ <eq:nonmaximal-order-primes>
Then $S(Lambda)$ is a finite set of maximal ideals $P$ of $R$, by
Exercise~@exc:lattices-localizations-almost-everywhere, and $S(Lambda)=emptyset$
if and only if $Lambda$ is a maximal order (see
@th:maximal-orders-localization). For example, when $Lambda=R G$ where
$char K divides.not |G|$, the set $S(Lambda)$ is given by
${P:P "contains" |G|}$, by @prop:group-ring-maximality.

Two $Lambda$-lattices $M$ and $N$ are placed in the same _genus_ (notation:
$M or.curly N$) if $M_P tilde.equiv N_P$ as $Lambda_P$-lattices for each
$P$.#idx("genus") As we shall see, if $S(Lambda)!=emptyset$, it suffices to
impose this condition when $P in S(Lambda)$. Further, it is often convenient to
use Roiter's Lemma:#idx(
  "Roiter's Lemma",
) $M or.curly N$ if and only if _for each nonzero ideal_ $I$ _of_ $R$, _there is
a_ $Lambda$-_exact sequence_
$ 0->M->N->T->0, $
_with_ $I+"ann"_R T=R$.

#source(665)
Instead of working with localizations, we could equally well use $P$-adic
completions.

The first basic fact about genera is that if $N_P divides M_P$ for each
$P in S(Lambda)$ (assuming $S(Lambda)!=emptyset$), then there exists a
$Lambda$-lattice $N'$ in the genus of $N$ such that $N' divides M$. Thus,
decomposability is a property of genus. An important consequence of this result
is that one can “add” lattices within a genus, that is, if $L$, $M$ and $N$ are
in the same genus, then
$ L plus.o M tilde.equiv N plus.o N' $
for some lattice $N'$ in the genus. This formula leads to the concept of the
locally free class group $"Cl" Lambda$ of an order. This class group also arises
naturally in algebraic $K$-theory, when one studies $K_0(ZZ G)$ (see Chapter~10
of Volume~II). We shall give an idèle-theoretic version of $"Cl" Lambda$ in this
section, reserving the deeper discussion of the subject for Chapter~11 of
Volume~II.

The section concludes with a beautiful and powerful result due to Roiter (and,
in another form, to Jacobinski): _Let_ $M$ _and_ $N$ _be_ $Lambda$-_lattices in
the same genus, and let_ $F$ _be any faithful_#footnote[
  This means that $"ann"_Lambda F=0$.
] $Lambda$-_lattice. Then_ $N$ _is a direct summand of_ $M plus.o F$.#idx(
  "faithful",
) As a consequence of this theorem, it follows that if $L$ is a $Lambda$-lattice
such that $L_P divides M_P$ for each $P in S(Lambda)$, and if every
$A$-composition factor of $K L$ occurs more often in $K M$ than in $K L$, then
$L$ is a direct summand of $M$.

=== Basic Properties <ss:genus-basic-properties>

For $M$ and $N$ $Lambda$-lattices, we write $M or.curly N$ if
$M_P tilde.equiv N_P$ for each $P$. We say that $M$ and $N$ are in the same
_genus_, or are _locally isomorphic_.#idx("genus")#idx("locally isomorphic") By
@prop:module-isomorphism-completion, $M or.curly N$ if and only if
$hat(M)_P tilde.equiv hat(N)_P$ for each $P$. Put
$ Gamma_M={N:N=Lambda"-lattice",N or.curly M}, $
the _genus_ of $M$.

Our first result shows that the genus of $M$ is determined by the behavior of
$M$ at the primes in the set $S(Lambda)$ defined in @eq:nonmaximal-order-primes.
We have:

#proposition[
  Let $M$ and $N$ be $Lambda$-lattices, and let $S(Lambda)$ be defined as in
  @eq:nonmaximal-order-primes. Then
  #enum(
    numbering: "(i)",
    [$M or.curly N$ implies $K M tilde.equiv K N$ as $A$-modules.],
    [If $S(Lambda)!=emptyset$, then $M or.curly N$ if and only if
      $M_P tilde.equiv N_P$ for all $P in S(Lambda)$.],
    [If $Lambda$ is a maximal order, then $M or.curly N$ if and only if
      $K M tilde.equiv K N$.],
  )
] <prop:genus-nonmaximal-primes>
#proof[
  If $M or.curly N$, then $M_P tilde.equiv N_P$ for each $P$. However, if this
  isomorphism holds for even one choice of $P$, then we obtain
  $K M_P tilde.equiv K N_P$, whence $K M tilde.equiv K N$.
  #source(666)
  This establishes~(i) and part of~(iii). Suppose now that
  $K M tilde.equiv K N$; if $Lambda_P$ is a maximal $R_P$-order, then the
  $Lambda_P$-lattices $M_P$ and $N_P$ have the property that
  $K M_P tilde.equiv K N_P$, whence $M_P tilde.equiv N_P$ by
  Exercise~@exc:dvr-maximal-order-lattice-isomorphism. This completes the proof
  of~(iii). Finally, suppose $S(Lambda)!=emptyset$; by the first step in the
  proof, we deduce that $K M tilde.equiv K N$, whence as above
  $M_P tilde.equiv N_P$ whenever $P in.not S(Lambda)$. But this proves~(ii), and
  establishes the proposition.
]

#corollary[
  Let $L$, $M$ and $N$ be $Lambda$-lattices.
  #enum(
    numbering: "(i)",
    [A $Lambda$-exact sequence $0->L->M->N->0$ is split if and only if, for each
      $P in S(Lambda)$, the $Lambda_P$-exact sequence $0->L_P->M_P->N_P->0$ is
      split.],
    [$N$ is $Lambda$-projective if and only if $N_P$ is $Lambda_P$-projective
      for all $P in S(Lambda)$.],
    [If $G$ is a finite group with $char K divides.not |G|$, then an
      $R G$-lattice $N$ is $R G$-projective if and only if $N_P$ is
      $R_P G$-projective for each $P$ dividing $|G|$.],
  )
] <cor:genus-local-splitting-projectivity>
#proof[
  For~(i), we note that the original sequence splits if and only if it splits at
  each $P$. But for $P in.not S(Lambda)$, $N_P$ is a lattice over the maximal
  $R_P$-order $Lambda_P$, and is therefore $Lambda_P$-projective by
  @th:maximal-orders-are-hereditary. This establishes~(i), and then~(ii),~(iii)
  are obvious consequences.
]

We shall next derive Roiter's criterion for two lattices to lie in the same
genus, and we begin with a preliminary result which is used often. This result
involves simultaneous approximation of some collection of homomorphisms; for
later applications, we need the version dealing with completions rather than
localizations.

#lemma[
  Let $S_0$ be some finite non-empty collection of maximal ideals of $R$, and
  let $M$ and $N$ be $Lambda$-lattices. Suppose that for each $P in S_0$, there
  exist $hat(Lambda)_P$-homomorphisms
  $ f_P:hat(M)_P->hat(N)_P, quad g_P:hat(N)_P->hat(M)_P, $
  such that $f_P g_P=1$ on $hat(N)_P$. Then there exist $Lambda$-homomorphisms
  $ u:M->N, quad v:N->M, $
  such that for each $P in S_0$, $u v in "Aut" hat(N)_P$.
] <lem:simultaneous-lattice-homomorphism-approximation>
#proof[
  For each $P in S_0$, the completion $hat(R)_P$ is a flat $R$-module, by
  @cor:pid-torsionfree-flat. Using @th:change-of-rings, we obtain
  $
    hat(R)_P times.o_R Hom_Lambda lr((M,N)) tilde.equiv
    Hom_(hat(Lambda)_P) lr((hat(M)_P,hat(N)_P)).
  $ <eq:completed-lattice-homomorphisms>
  Let us treat this isomorphism as an identification, so by
  @prop:localization-completion-lattices we see that
  #source(667)
  $Hom(M, N)$ is densely embedded in $Hom(hat(M)_P, hat(N)_P)$ in the $P$-adic
  topology. For each $P in S_0$, we may choose $u_P in Hom(M, N)$ such that
  $ (u_P-f_P)hat(M)_P subset.eq P hat(N)_P. $
  By @eq:chinese-remainder-ideals or @th:strong-approximation, we can find
  elements ${alpha_P:P in S_0}$ in $R$, such that for each $P in S_0$,
  $
    alpha_P equiv 1 ("mod" P), quad alpha_P equiv 0 ("mod" P')
    quad "for all" P' in S_0-{P}.
  $
  Set $u=sum_(P in S_0) alpha_P u_P$; then $u in Hom_Lambda lr((M,N))$, and
  $ (u-f_P)hat(M)_P subset.eq P hat(N)_P quad "for all" P in S_0. $
  Likewise, we may find a map $v in Hom_Lambda lr((N,M))$ such that
  $ (v-g_P)hat(N)_P subset.eq P hat(M)_P quad "for all" P in S_0. $
  Then for $P in S_0$ we have
  $ hat(N)_P=f_P g_P hat(N)_P=u v hat(N)_P+P hat(N)_P. $
  Therefore $hat(N)_P=u v hat(N)_P$ by Nakayama's Lemma, whence
  $u v in "Aut"(hat(N)_P)$ by @prop:surjective-noetherian-endomorphism. This
  completes the proof.
]

We shall use this lemma repeatedly. As its first important application, we
derive the following criterion for two lattices to lie in the same genus:

#lemma(name: "Roiter's Lemma")[
  Let $M$ and $N$ be $Lambda$-lattices. Then $M or.curly N$ if and only if for
  each nonzero ideal $I$ of $R$, there exists a $Lambda$-exact sequence
  $ 0->M->N->T->0 $
  for some $Lambda$-module $T$ such that $I+"ann"_R T=R$.
] <lem:roiter-genus>
#idx("Roiter's Lemma", target: [@lem:roiter-genus])
#proof[
  If the criterion holds, then for each $P$ there is such an exact sequence for
  which $P+"ann"_R T=R$. Then $T_P=0$ by
  Exercise~@exc:localization-zero-annihilator, whence $M_P tilde.equiv N_P$
  because $0->M_P->N_P->T_P->0$ is exact by §@ss:localization. Hence
  $M or.curly N$, as claimed.

  Conversely, suppose that $M or.curly N$, so there exists an $A$-isomorphism
  $phi:K M tilde.equiv K N$. If the ideal $I$ coincides with $R$, we proceed as
  follows: choose a nonzero element $a in R$ such that
  $a dot phi(M) subset.eq N$. Then there is an exact sequence
  $ 0->M arrow.r^(a phi) N->T->0, $
  in which $I+"ann" T=R$, as desired.

  #source(668)
  We are now left with the case where $I subset R$, and we choose $S_0$ to be
  the non-empty set of all maximal ideals of $R$ which contain $I$. Since we are
  assuming that $M or.curly N$, it follows that for each $P in S_0$ we can find
  $hat(Lambda)_P$-isomorphisms
  $ f_P:hat(M)_P tilde.equiv hat(N)_P "and" g_P:hat(N)_P tilde.equiv hat(M)_P. $
  Hence by @lem:simultaneous-lattice-homomorphism-approximation we can find maps
  $u in Hom_Lambda lr((M,N))$, $v in Hom_Lambda lr((N,M))$, such that for each
  $P in S_0$, $v u in "Aut"_(hat(Lambda)_P) lr((hat(M)_P))$ and
  $u v in "Aut"_(hat(Lambda)_P) lr((hat(N)_P))$. Let us now consider the
  $Lambda$-exact sequence
  $ 0->ker u->M arrow.r^u N. $
  By @prop:localization-criteria we have $(ker u)_P=ker u_P=0$ for $P in S_0$.
  Thus $ker u$ is a torsion $R$-module annihilated by some element of the
  multiplicative set $R-P$. But $ker u subset.eq M$, so $ker u$ is
  $R$-torsionfree. This gives $ker u=0$, so we obtain a $Lambda$-exact sequence
  $ 0->M arrow.r^u N->T->0, quad "where" T="cok" u. $
  For each $P in S_0$, the map $u$ gives rise to an isomorphism
  $u_P:hat(M)_P tilde.equiv hat(N)_P$. Therefore $hat(T)_P=0$, so $T_P=0$ by
  @prop:localization-completion-lattices(iii), and thus $P+"ann"_R T=R$. Since
  this holds for each $P$ dividing $I$, we obtain $I+"ann"_R T=R$ as desired,
  completing the proof.
]

As an application of the above, we show how to “add” lattices in the same genus:

#corollary[
  Let $L$, $M$ and $N$ be $Lambda$-lattices in the same genus. Then there exists
  a $Lambda$-lattice $L'$ in the genus such that
  $ M plus.o N tilde.equiv L plus.o L'. $
] <cor:genus-addition>
#proof[
  By Roiter's Lemma, there exists $Lambda$-exact sequences
  $ 0->M arrow.r^f L->T->0, quad 0->N arrow.r^g L->U->0, $
  with $T$ and $U$ $R$-torsion $Lambda$-modules such that
  $ "ann"_R T+"ann"_R U=R. $
  Thus for each maximal ideal $P$ of $R$, either $T_P=0$ or $U_P=0$, that is,
  either $f_P$ or $g_P$ is an isomorphism.

  Now consider the sequence
  $ 0->L'->M plus.o N arrow.r^((f,g)) L->0, $
  #source(669)
  where $L'=ker(f, g)$, and where $(f,g)(m+n)=f(m)+g(n)$, $m in M$, $n in N$.
  The map $(f,g)$ is surjective by @prop:localization-criteria, since for each
  $P$ it induces a surjection $M_P plus.o N_P->L_P$. Thus the sequence is exact.
  By @prop:localization-criteria the sequence is $Lambda$-split, since it splits
  at each $P$. Thus we have $M plus.o N tilde.equiv L plus.o L'$. Finally, at
  each $P$ we obtain
  $
    hat(M)_P plus.o hat(N)_P tilde.equiv hat(L)_P plus.o hat(L)'_P,
    quad hat(M)_P tilde.equiv hat(L)_P,
  $
  whence by @cor:complete-local-module-cancellation we obtain
  $hat(N)_P tilde.equiv hat(L)'_P$. Thus $L' or.curly N$, as desired.
]

In §@ss:ideles-locally-free-class-groups, we shall return to this idea of
“addition” of lattices in a given genus, but first let us continue with
consequences of the preceding lemmas. The following striking result, an analogue
of Schanuel's Lemma (see §@sec:hom-tensor-projective-injective-flat), is due to
Roiter~@bib:Roiter1966a:

#proposition[
  Let $L$, $L'$, $M$ and $M'$ be $Lambda$-lattices, and let $T$ be an
  $R$-torsion $Lambda$-module such that $T_P=0$ for all $P in S(Lambda)$.
  Suppose that there exist a pair of $Lambda$-exact sequences
  $ 0->L'->L arrow.r^f T->0, quad 0->M'->M arrow.r^g T->0. $
  Then there is a $Lambda$-isomorphism
  $ L plus.o M' tilde.equiv L' plus.o M. $
] <prop:genus-schanuel>
#proof[
  Let $W$ be the pullback of the pair of maps $f$, $g$ (see
  §@sec:hom-tensor-projective-injective-flat). Then we obtain a commutative
  diagram of $Lambda$-modules and $Lambda$-homomorphisms, with exact rows and
  columns:
  #genus-pullback()
  At each $P in S(Lambda)$ we have $T_P=0$ by hypothesis. Further, the process
  of localization at $P$ preserves exactness and commutativity. It follows that
  both
  #source(670)
  of the $Lambda$-exact sequences
  $ 0->M'->W->L->0, quad 0->L'->W->M->0, $
  are split at each $P in S(Lambda)$. Hence they are split over $Lambda$ by
  @cor:genus-local-splitting-projectivity. Therefore
  $ W tilde.equiv M' plus.o L, quad W tilde.equiv L' plus.o M, $
  which proves the result.
]

From this result we may derive formulas @eq:genus-absorption and
@eq:genus-exchange below, which demonstrate the failure of the K-S-A Theorem in
the global case. Let $M$ and $N$ be $Lambda$-lattices, and let $X$ be an
extension of $N$ by $M$, so there is a $Lambda$-exact sequence
$ 0->M->X->N->0. $
Each $phi in "End"_Lambda lr((M))$ determines another extension
$attach(X, bl: phi)$ of $N$ by $M$, namely, we choose $attach(X, bl: phi)$ to be
the pushout of $phi$ and the above map $M->X$. We obtain a commutative diagram
with exact rows:
#genus-pushout()
(Indeed if $X$ corresponds to an extension class
$xi in "Ext"_Lambda^1 lr((N,M))$, then $attach(X, bl: phi)$ corresponds to the
class $phi xi$ (see §@sec:ext-tor-cohomology).) From the Snake Lemma
(Exercise~@exc:snake-lemma), we obtain
$ ker phi tilde.equiv ker theta, quad "cok" phi tilde.equiv "cok" theta. $
Suppose now that $phi$ satisfies the condition
$ phi_P in "Aut"_(Lambda_P) lr((M_P)) quad "for all" P in S(Lambda), $
<eq:genus-extension-endomorphism-condition>
where $S(Lambda)!=emptyset$. Then $ker phi_P=0$, that is, $(ker phi)_P=0$ for
each $P in S(Lambda)$; since $ker phi$ is $R$-torsionfree, we see that
$ker phi=0$, whence also $ker theta=0$. Further,
$
  ("cok" theta)_P tilde.equiv ("cok" phi)_P="cok" phi_P=0, quad P in S(Lambda).
$
We thus obtain $Lambda$-exact sequences
$
  0->X arrow.r^theta attach(X, bl: phi)->"cok" phi->0,
  quad 0->M arrow.r^phi M->"cok" phi->0.
$
From @prop:genus-schanuel, we then obtain the following “Absorption Formula”,
due to
#source(671)
Reiner~@bib:Reiner1978:
$ attach(X, bl: phi) plus.o M tilde.equiv X plus.o M. $ <eq:genus-absorption>
In a similar manner, if $Y$ is another extension of $N$ by $M$, we obtain an
exact sequence
$ 0->Y->attach(Y, bl: phi)->"cok" phi->0, $
and hence we deduce the “Exchange Formula”
$ X plus.o attach(Y, bl: phi) tilde.equiv attach(X, bl: phi) plus.o Y, $
<eq:genus-exchange>
also due to Reiner~@bib:Reiner1978. We emphasize that these formulas depend
strongly on the hypothesis @eq:genus-extension-endomorphism-condition.

We show next that decomposability of a $Lambda$-lattice $M$ depends only upon
the local behavior of $M$.

#theorem[
  Let $M$ and $N$ be $Lambda$-lattices such that $hat(N)_P divides hat(M)_P$ for
  each $P in S(Lambda)$. (If $S(Lambda)=emptyset$, assume instead that
  $K N divides K M$.) Then there exists a $Lambda$-lattice $N' in Gamma_N$ such
  that $N' divides M$.
] <th:genus-local-direct-summand>
#proof[
  Assume first that $S(Lambda)!=emptyset$. The hypothesis implies that for each
  $P in S(Lambda)$ there exist maps $f_P$, $g_P$ as in
  @lem:simultaneous-lattice-homomorphism-approximation. Hence we can find maps
  $u$, $v$ with
  #genus-two-maps()
  Put $L=u(M)$, a $Lambda$-sublattice of $N$. Then for $P in S(Lambda)$ we have
  $ hat(N)_P=u(hat(M)_P)=hat(L)_P, $
  so $N or.curly L$ by @prop:genus-nonmaximal-primes. Furthermore, at each
  $P in S(Lambda)$ the surjection $u:hat(M)_P->hat(L)_P$ is split by the map
  $v(u v)^(-1):hat(L)_P->hat(M)_P$, with the inverse taken on $hat(L)_P$. Hence
  the $Lambda$-exact sequence
  $ 0->ker u->M->L->0 $
  splits at each $P in S(Lambda)$, whence it splits globally#footnote[
    This follows from @prop:localization-criteria and the fact that a sequence
    of $Lambda_P$-lattices splits if and only if the corresponding sequence of
    $hat(Lambda)_P$-lattices is split (see
    Exercise~@exc:completion-exact-sequence-splitting).
  ]. Thus $M tilde.equiv L plus.o ker u$, and the result is proved for the case
  where $S(Lambda)!=emptyset$. For the proof when $S(Lambda)=emptyset$, see
  Exercise~@exc:maximal-order-generic-direct-summand.
]

#source(672)
#corollary[
  Let $L$, $M$ and $N$ be $Lambda$-lattices such that $L or.curly (M plus.o N)$.
  Then there exist $Lambda$-lattices $M'$, $N'$ with
  $ L tilde.equiv M' plus.o N', quad M' or.curly M, quad N' or.curly N. $
] <cor:genus-direct-sum-decomposition>

#corollary[
  Let $L$ and $M$ be $Lambda$-lattices such that $L or.curly M^((r))$. Then
  there exists a $Lambda$-lattice $M'$ in the genus of $M$ such that
  $ L tilde.equiv M^((r-1)) plus.o M'. $
] <cor:genus-multiple-decomposition>
#proof[
  From @cor:genus-direct-sum-decomposition, we obtain
  $ L tilde.equiv M_1 plus.o dots plus.o M_r, $
  where each $M_i or.curly M$. Now use @cor:genus-addition repeatedly:
  $ M_1 plus.o M_2 tilde.equiv M plus.o M'_2, quad "where" M'_2 or.curly M, $
  $ M'_2 plus.o M_3 tilde.equiv M plus.o M'_3, quad "where" M'_3 or.curly M, $
  and so on.
]

In @th:genus-local-direct-summand we saw that if $M$ and $N$ are
$Lambda$-lattices such that $N$ is a local direct summand of $M$, then some $N'$
in the genus of $N$ is a global direct summand of $M$. We shall see in
§@ss:roiter-theorem-genera that, _under suitable hypotheses_, a much deeper
result holds: if $N$ is a local direct summand of $M$, then $N$ is also a global
direct summand of $M$.

To conclude this subsection, we remark that genus can also be studied by using
semilocal rings. Let $S(Lambda)!=emptyset$, and set
$ tilde(R)=op("⋂", limits: #true)_(P in S(Lambda)) R_P, $
so $tilde(R)$ is the ring of quotients $S^(-1)R$, where $S$ is the
multiplicative set
$ S=R-op("⋃", limits: #true)_(P in S(Lambda)) P. $
The maximal ideals of $tilde(R)$ are ${P tilde(R):P in S(Lambda)}$, and
$tilde(R)$ is semilocal. Put $tilde(Lambda)=tilde(R)Lambda$, an $tilde(R)$-order
in $A$; each $Lambda$-lattice $M$ gives rise to a $tilde(Lambda)$-lattice
$tilde(M)=tilde(R)M$.

#proposition[
  Two $Lambda$-lattices $M$ and $N$ are in the same genus if and only if
  $tilde(M) tilde.equiv tilde(N)$ as $tilde(Lambda)$-modules.
] <prop:genus-semilocal-isomorphism>
#proof[
  For each $P in S(Lambda)$, $M_P tilde.equiv (tilde(M))_(P tilde(R))$ by
  transitivity of the construction of modules of quotients. Hence if
  $tilde(M) tilde.equiv tilde(N)$, then $M_P tilde.equiv N_P$ for each
  $P in S(Lambda)$, and therefore $M or.curly N$. Conversely, if $M or.curly N$
  then $tilde(M) or.curly tilde(N)$ as $tilde(Lambda)$-lattices. By Roiter's
  #source(673)
  Lemma we can then find a $tilde(Lambda)$-exact sequence
  $ 0->tilde(M)->tilde(N)->T->0 $
  in which $T$ is an $tilde(R)$-torsion module for which $"ann"_(tilde(R)) T$ is
  coprime to each of the ideals ${P tilde(R):P in S(Lambda)}$. This implies that
  $T=0$, so $tilde(M) tilde.equiv tilde(N)$, as desired.
]

By @prop:localized-module-finite-model, every $tilde(Lambda)$-lattice is
expressible as $tilde(M)$ for some $Lambda$-lattice $M$. The preceding result
shows that the study of genera of $Lambda$-lattices is equivalent to the study
of $tilde(Lambda)$-lattices. For $V$ a f.g. left $A$-module, let
$ sigma(V) tilde.equiv {M:M tilde.equiv "full left" Lambda"-lattice in" V}, $
and let $g(V)$ be the number of genera in $sigma(V)$. Then $g(V)$ is precisely
the number of $tilde(Lambda)$-isomorphism classes in the set $sigma(V)$. We have
shown above that each $tilde(Lambda)$-lattice $X$ is determined up to
isomorphism by the isomorphism classes ${X_P:P in S(Lambda)}$. If $h_P lr((V))$
denotes the number of $Lambda_P$-isomorphism classes in the set $sigma(V)$, the
above discussion yields the formula
$ g(V)=product_(P in S(Lambda)) h_P lr((V)), $
due to Maranda~@bib:Maranda1955 and Takahashi~@bib:Takahashi1959. Note that
$g(V)$ is finite whenever $K$ is a global field. (If $Lambda$ is a maximal
order, we find readily that $g(V)=1$ for each $V$.)

In practice, the use of $tilde(Lambda)$-lattices for working with genera
produces some simplifications in proofs (see, for example, Lee~@bib:Lee1964 and
Pu~@bib:Pu1965). However, the method does not seem to be of major significance.
We may remark also that the K-S-A Theorem need not be valid for
$tilde(Lambda)$-lattices (see §@sec:krull-schmidt-discrete-valuations).

=== Idèles and Class Groups <ss:ideles-locally-free-class-groups>

In this subsection only, we change notation and use the subscript $P$ to denote
$P$-adic completion rather than localization at $P$. As usual let $R$ be a
Dedekind domain with quotient field $K$. Let $Gamma$ be an $R$-order in a f.d.
separable $K$-algebra $B$, and let $M$ be a left $Gamma$-lattice. We put
$ A="End"_B K M, quad Lambda="End"_Gamma M, $
where these endomorphism rings are viewed as acting on the opposite side from
scalars. Then $Lambda$ is an $R$-order in the f.d. $K$-algebra $A$, and by
Exercise~@exc:separable-module-endomorphism-algebra, $A$ is a separable
$K$-algebra. We view $M$ as a bimodule $attach(M, bl: Gamma, br: Lambda)$. Our
aim is to establish the relationship between $Gamma$-lattices in the genus of
$M$, and left ideals of $Lambda$.

For any $Gamma$-lattice $N$ in the genus of $M$, we have $K N tilde.equiv K M$
as $B$-modules, by @prop:genus-nonmaximal-primes. Replacing $N$ by an isomorphic
copy, if need be, we may assume that $N$
#source(674)
is a full $Gamma$-lattice in $K M$. Thus, in studying $Gamma$-lattices in the
genus of $M$, we may restrict our attention to the full $Gamma$-lattices in
$K M$.

Given any full $Gamma$-lattice $N$ in $K M$, we note that each
$phi in Hom_Gamma lr((N,M))$ extends to an element of $Hom_B lr((K N,K M))$, and
is therefore given by right multiplication by an element of $A$. Therefore
$
  N tilde.equiv M "as" Gamma"-lattices" <=>N=M x "for some" x in A^dot,
$ <eq:genus-lattice-unit-orbit>
where $A^dot$ is the group of units of $A$. Furthermore, for each maximal ideal
$P$ of $R$, the completion $N_P$ is a full $Gamma_P$-lattice in $K_P M$. We have
$N or.curly M$ if and only if $N_P tilde.equiv M_P$ for each $P$, that is, if
and only if for each $P$, $N_P=M_P alpha_P$ for some $alpha_P in (A_P)^dot$.
Furthermore, since $M_P=N_P$ a.e. (see
Exercise~@exc:lattices-localizations-almost-everywhere), we may choose
$alpha_P in (Lambda_P)^dot$ a.e. (or even $alpha_P=1$ a.e., if desired).

By §@sec:dedekind-domains we have
$
  N=K M inter (op("⋂", limits: #true)_P N_P)
  =K M inter (op("⋂", limits: #true)_P M_P alpha_P).
$
This suggests that we should introduce the _idèle group_ $J(A)$ _relative to_
$R$, defined by#idx("idele group")
$
  J(A)={(alpha_P) in product_P (A_P)^dot:alpha_P in (Lambda_P)^dot "a.e."}.
$ <eq:idele-group>
We note at once that $J(A)$ does not depend on the choice of the $R$-order
$Lambda$ in $A$, since if $Lambda'$ is another $R$-order in $A$, then
$Lambda_P=Lambda'_P$ a.e. Thus, up to isomorphism, every $Gamma$-lattice $N$ in
the genus of $M$ is given by
$
  N=K M inter (op("⋂", limits: #true)_P M_P alpha_P),
  quad "where" (alpha_P) in J(A).
$
For each $alpha=(alpha_P) in J(A)$, we define
$
  Lambda alpha=A inter {op("⋂", limits: #true)_P Lambda_P alpha_P}
  =op("⋂", limits: #true)_P {A inter Lambda_P alpha_P}.
$
By @prop:localization-completion-lattices, $Lambda alpha$ is a full left
$Lambda$-lattice in $A$ such that $(Lambda alpha)_P=Lambda_P alpha_P$ for each
$P$. Thus $Lambda alpha$ is isomorphic to a left ideal of $Lambda$, and
$Lambda alpha$ is in the same genus as $Lambda$ (as $Lambda$-lattices). We shall
call $Lambda alpha$ a _locally free_ (rank~1) $Lambda$-lattice, or a _locally
free fractional_ $Lambda$-_ideal_ in $A$.#idx("locally free")

We note next that $N=M dot Lambda alpha$, for $alpha in J(A)$ as above, since
for each $P$ we have
$
  N_P=M_P alpha_P=M_P Lambda_P alpha_P=M_P dot (Lambda alpha)_P
  =(M dot Lambda alpha)_P.
$
Thus, each full $Gamma$-lattice $N$ in $K M$, such that $N or.curly M$, is of
the form $N=M dot Lambda alpha$
#source(675)
for some $alpha in J(A)$. Conversely, every $M dot Lambda alpha$ is such an $N$.
We remark that
$ Lambda alpha=Hom_Gamma lr((M,N)), $
since these two expressions are $R$-lattices in $A$ having the same completion
at each $P$:
$
  (Lambda alpha)_P=Lambda_P alpha_P, quad
  {Hom_Gamma lr((M,N))}_P=Hom_(Gamma_P) lr((M_P,M_P alpha_P))
  ="End"_(Gamma_P) lr((M_P)) dot alpha_P=Lambda_P alpha_P.
$
(Remark: $N or.curly M$ implies by @cor:genus-addition that $N divides M^((2))$.
By @prop:morita-summand-equivalence, the summands of $M^((2))$ correspond
bijectively with the summands of $Lambda^((2))$, with
$
  N arrow.l.r Hom_Gamma lr((M,N)), quad
  N=M times.o_Lambda Hom_Gamma lr((M,N)).
$
We have just encountered a special case of this correspondence.)

Now let $alpha,beta in J(A)$, and form the left $Gamma$-lattices
$M dot Lambda alpha$, $M dot Lambda beta$. These are $Gamma$-isomorphic if and
only if
$ M dot Lambda beta=M dot Lambda alpha dot x "for some" x in A^dot. $
This latter condition is equivalent to the assertion that for some $x in A^dot$,
$ M_P beta_P=M_P alpha_P x quad "for all" P, $
that is, for all $P$ we have
$ beta_P=u_P alpha_P x "for some" u_P in (Lambda_P)^dot. $

We introduce two subgroups of the idèle group $J(A)$. The image of $A^dot$ in
$J(A)$ is the group of _principal idèles_, denoted by $u(A)$.#idx(
  "idele",
  "principal",
)#idx("principal idele") (A principal idèle is an idèle of the form $(x)$,
having $P$-th component $x$ for all $P$, where $x in A^dot$.) Next let
$U(Lambda)$ be the group of _unit idèles_, defined by#idx("idele", "unit")#idx(
  "unit idele",
)
$ U(Lambda)=product_P (Lambda_P)^dot subset.eq J(A). $
We have just shown that $M dot Lambda beta tilde.equiv M dot Lambda alpha$ if
and only if $beta in U(Lambda) dot alpha dot u(A)$. We collect our results in
the following result, due to Takahashi~@bib:Takahashi1959 and
Fröhlich~@bib:Frohlich1975 (see also Drozd~@bib:Drozd1969a and
Faddeev~@bib:Faddeev1965a):

#theorem[
  Let $Gamma$ be an $R$-order, $M$ a left $Gamma$-lattice, and let
  $Lambda="End"_Gamma lr((M))$, $A=K Lambda$, where $M$ is viewed as bimodule
  $attach(M, bl: Gamma, br: Lambda)$. Then there is a bijection between the set
  of isomorphism classes of left $Gamma$-lattices in the genus of $M$, and the
  set of double cosets $U(Lambda) dot alpha dot u(A)$ of the idèle group $J(A)$.
  The
  #source(676)
  double coset containing an idèle $alpha$ corresponds to the isomorphism class
  of the $Gamma$-lattice
  $
    M dot Lambda alpha=K M inter {op("⋂", limits: #true)_P M_P alpha_P},
    quad "where" alpha=(alpha_P) in J(A).
  $
] <th:genus-idele-double-cosets>

We are now ready to take up once more the methods of “addition” of lattices in
the same genus, and we can now give a much more enlightening version of
@cor:genus-addition. In the notation of this subsection, let
$alpha,beta in J(A)$, and consider the locally free fractional $Lambda$-ideals
$Lambda alpha$, $Lambda beta$ defined above. Then $Lambda alpha$ and
$Lambda beta$ are left $Lambda$-lattices in the genus of $Lambda$, so by
@cor:genus-addition we know that
$
  Lambda alpha plus.o Lambda beta tilde.equiv Lambda plus.o Lambda gamma
  "for some" gamma in J(A).
$
Our problem is to determine $gamma$ in terms of $alpha$ and $beta$. The analogy
with Steinitz's Theorem~@th:steinitz might be useful here; this theorem tells us
that if $I$ and $J$ are nonzero fractional $R$-ideals of $K$, then
$ I plus.o J tilde.equiv R plus.o I J quad "as" R"-lattices". $
This suggests that there should be some multiplicative version of
@cor:genus-addition. Indeed, we shall now prove the following result, due to
Fröhlich~@bib:Frohlich1975; his proof used properties of reduced norms, and the
more direct proof given here is due to Reiner (see
Reiner-Roggenkamp~@bib:Reiner1979):

#theorem[
  For $alpha$ and $beta in J(A)$, we have
  $
    Lambda alpha plus.o Lambda beta tilde.equiv Lambda plus.o Lambda alpha beta.
  $
] <th:idele-lattice-multiplication>
#proof[
  We shall begin by replacing $alpha$ by $r u alpha$, and $beta$ by $beta x$,
  for suitably chosen elements $r in R$ ($r!=0$), $u in U(Lambda)$, and
  $x in u(A)$. These changes will not affect the isomorphism classes of the
  $Lambda$-lattices $Lambda alpha$, $Lambda beta$ and $Lambda alpha beta$. First
  choose $r$ so that $r alpha$ is an _integral idèle_, that is,
  $r alpha_P in Lambda_P$ for each $P$.#idx("idele", "integral")#idx(
    "integral idele",
  ) Then pick $u$ so that $r u_P alpha_P=1$ a.e. Changing notation, we assume
  from now on that $alpha_P in Lambda_P$ for each $P$, and that $alpha_P=1$ a.e.

  Now let $S_0={P:alpha_P!=1}$; if $S_0=emptyset$, then $alpha=1$ and the result
  is obvious for this case. We may therefore consider the case where the finite
  set $S_0$ is non-empty. Let $t$ be a positive integer, to be chosen later; the
  choice will depend on $alpha$ but not on $beta$. For each $P in S_0$, $A$ is
  dense in the $P$-adic completion $A_P$. Therefore by the Strong Approximation
  Theorem~@th:strong-approximation we can find an element $x in u(A)$ such that
  $ beta_P x equiv 1 "mod" P^t Lambda_P quad "for each" P in S_0, $
  and such that $beta x$ is an integral idèle. Replacing $beta$ by $beta x$ and
  changing
  #source(677)
  notation, we may hereafter assume that $beta$ is an integral idèle for which
  $ beta_P equiv 1 "mod" P^t Lambda_P quad "for each" P in S_0. $

  Some preliminary comments may be useful before we describe how to choose $t$.
  We wish to consider the commutator $beta alpha beta^(-1)alpha^(-1)$, and to
  make its $P$-th component
  $ beta_P alpha_P beta_P^(-1)alpha_P^(-1) $
  close to~1 (in $Lambda_P$) for each $P in S_0$. This will guarantee that the
  above $P$-th component lies in $(Lambda_P)^dot$ for each $P in S_0$. For fixed
  $alpha_P$, the above expression is a continuous function of $beta_P$ relative
  to the $P$-adic topology. Hence if we take $beta_P$ sufficiently close to~1,
  we can make the above expression near $1 dot alpha_P dot 1 dot alpha_P^(-1)$,
  that is, it will also be close to~1.

  To be explicit, we first choose a positive integer $k$ such that for each
  $P in S_0$ we have $alpha_P^(-1) in P^(-k)Lambda_P$. Note that for each $P$,
  both $alpha_P$ and $beta_P$ lie in $Lambda_P$, since $alpha$ and $beta$ are
  integral idèles. We now take $t=k+1$. Then for $P in S_0$ we may write
  $ beta_P=1+lambda pi^t $
  for some $lambda in Lambda_P$, where $pi$ is a prime element of $R_P$. But
  then
  $
    beta_P^(-1)=(1+lambda pi^t)^(-1)=1-lambda pi^t+lambda^2 pi^(2 t)-dots
    =1+lambda_1 pi^t
  $
  for some $lambda_1 in Lambda_P$. We therefore obtain
  $
    beta_P alpha_P beta_P^(-1)alpha_P^(-1)
    & =(1+lambda pi^t)alpha_P lr((1+lambda_1 pi^t))alpha_P^(-1)
    \ & =(alpha_P+lambda alpha_P pi^t) lr((alpha_P^(-1)+lambda_2 pi^(t-k)))
  $
  for some $lambda_2 in Lambda_P$ (note that we have used the fact that
  $alpha_P^(-1) in pi^(-k)Lambda_P$). Multiplying, we have
  $ beta_P alpha_P beta_P^(-1)alpha_P^(-1)=1+lambda_3 pi^(t-k)=1+pi lambda_3 $
  for some $lambda_3 in Lambda_P$. Since $pi Lambda_P subset.eq "rad" Lambda_P$
  by §@sec:radicals, it follows that the commutator
  $beta_P alpha_P beta_P^(-1)alpha_P^(-1) in (Lambda_P)^dot$. This holds for
  each $P in S_0$, and therefore
  $
    Lambda_P beta_P alpha_P=Lambda_P alpha_P beta_P
    quad "for each" P in S_0,
  $
  <eq:idele-commuting-local-ideals>
  a result which is crucial in the rest of the proof.

  Since $alpha$ and $beta$ are integral idèles, both $Lambda alpha$ and
  $Lambda beta$ are left ideals of $Lambda$, and therefore
  $Lambda alpha+Lambda beta subset.eq Lambda$. We shall show that indeed
  $Lambda alpha+Lambda beta=Lambda$; by §@sec:dedekind-domains, it
  #source(678)
  suffices to show that
  $ Lambda_P alpha_P+Lambda_P beta_P=Lambda_P quad "for each" P. $
  This surely holds for $P in.not S_0$, for then $alpha_P=1$; but it also holds
  when $P in S_0$, since then $beta_P equiv 1 "mod" P Lambda_P$, so
  $beta_P in (Lambda_P)^dot$. We have thus shown that
  $Lambda alpha+Lambda beta=Lambda$, so there is a surjection
  $f:Lambda alpha plus.dot Lambda beta->Lambda$ of the external direct sum
  $Lambda alpha plus.dot Lambda beta$ onto $Lambda$, where $f$ is defined by
  using the inclusions $Lambda alpha subset.eq Lambda$,
  $Lambda beta subset.eq Lambda$. Setting $L=ker f$, we obtain an exact sequence
  of $Lambda$-lattices
  $ 0->L->Lambda alpha plus.dot Lambda beta arrow.r^f Lambda->0. $
  <eq:idele-ideal-sum-sequence>
  If $(a,b) in ker f$, we have $a=-b$; therefore
  $
    L tilde.equiv Lambda alpha inter Lambda beta
    =inter (Lambda inter Lambda_P alpha_P inter Lambda_P beta_P).
  $
  We claim that $Lambda alpha inter Lambda beta=Lambda alpha beta$, that is,
  $
    Lambda_P alpha_P inter Lambda_P beta_P=Lambda_P alpha_P beta_P
    quad "for all" P.
  $
  For $P in S_0$ we have $beta_P in (Lambda_P)^dot$, so
  $
    Lambda_P alpha_P inter Lambda_P beta_P=Lambda_P alpha_P
    =Lambda_P beta_P alpha_P=Lambda_P alpha_P beta_P
  $
  by @eq:idele-commuting-local-ideals. For $P in.not S_0$ we have $alpha_P=1$,
  so
  $
    Lambda_P alpha_P inter Lambda_P beta_P=Lambda_P beta_P
    =Lambda_P alpha_P beta_P.
  $
  This proves that $L tilde.equiv Lambda alpha beta$, as claimed. But
  @eq:idele-ideal-sum-sequence splits, so
  $Lambda alpha plus.o Lambda beta tilde.equiv Lambda plus.o Lambda alpha beta$,
  and the theorem is proved.
]

#corollary[
  For $alpha,beta in J(A)$,
  $
    Lambda plus.o Lambda alpha beta tilde.equiv Lambda plus.o Lambda beta alpha.
  $
] <cor:idele-stable-commutativity>

We may now obtain the formula for “addition” within a genus as an immediate
consequence of @th:idele-lattice-multiplication. Let $M$ be a left
$Gamma$-lattice, and let $L$, $N$ be $Gamma$-lattices in the genus of $M$. Using
the notation of @th:genus-idele-double-cosets, we may write
$
  L=M dot Lambda alpha, quad N=M dot Lambda beta "for some" alpha,beta in J(A).
$
Now there is a surjection of $Gamma$-lattices:
$
  M times.o_Lambda Lambda alpha->L, quad "given by"
  m times.o xi mapsto m xi, quad "for" m in M,xi in Lambda alpha.
$
This map is injective, since it is injective at each $P$. Thus we have
$ M times.o_Lambda Lambda alpha tilde.equiv M dot Lambda alpha=L. $
#source(679)
From @th:idele-lattice-multiplication we obtain
$
  (M times.o Lambda alpha) plus.o (M times.o Lambda beta)
  tilde.equiv (M times.o Lambda) plus.o (M times.o Lambda alpha beta),
$
where $times.o$ is $times.o_Lambda$. From this result, we obtain
$ L plus.o N tilde.equiv M plus.o M dot Lambda alpha beta, $
which proves @cor:genus-addition in a stronger form:
$
  M dot Lambda alpha plus.o M dot Lambda beta tilde.equiv
  M plus.o M dot Lambda alpha beta, quad alpha,beta in J(A).
$ <eq:genus-idele-addition>
It should be remarked that the above proof is in the same spirit as the proof of
the isomorphism $I plus.o J tilde.equiv R plus.o I J$ in Steinitz's Theorem,
given in @bib:CurtisReiner1962[CR] §22, p.~150.

#example[
  Let us consider the idèle group $J(K)$ relative to the Dedekind domain $R$. By
  definition,
  $ J(K)={(alpha_P) in product_P (K_P)^dot:alpha_P in (R_P)^dot "a.e."}. $
  Here, $(K_P)^dot$ is just the multiplicative group consisting of all nonzero
  elements of the $P$-adic field $K_P$. Then the group of unit idèles is given
  by
  $ U(R)=product_P (R_P)^dot, $
  and $u(K)$ is the group of principal idèles. Since $J(K)$ is a commutative
  group, the double cosets $U(R) dot alpha dot u(K)$ in $J(K)$ coincide with the
  cosets of $J(K)$ relative to the subgroup $U(R) dot u(K)$. Hence by
  @th:genus-idele-double-cosets, applied to the special case where
  $Gamma=Lambda=R$, $M=R$, we obtain a bijection between the set of ideal
  classes in $R$ and the set of cosets of $J(K)$ relative to $U(R) dot u(K)$.
  Indeed, @eq:genus-idele-addition asserts that there is an isomorphism
  $ J(K) slash (U(R) dot u(K)) tilde.equiv "Cl"(R), $
  <eq:idele-ideal-class-group>
  where $"Cl"(R)$ denotes the ideal class group of $R$.#idx("ideal class group")
  This isomorphism carries the coset $alpha dot U(R) dot u(K)$ containing the
  element $alpha in J(K)$ onto the ideal class $[R alpha]$, where
  $ R alpha=op("⋂", limits: #true)_P (K inter R_P alpha_P). $
  In short, $R alpha$ is the fractional $R$-ideal in $K$ whose $P$-th component
  is $R_P alpha_P$ for each $P$. If we set
  $ R_P alpha_P=pi_P^(n(P))R_P, quad "where" pi_P="prime element of" R_P, $
  #source(680)
  then $n(P)=0$ a.e., and
  $ R alpha=product_P P^(n(P)). $
  (Of course, the isomorphism @eq:idele-ideal-class-group is well known, and is
  the starting point for the idèle-theoretic treatment of ideal theory and class
  field theory for global fields.)
] <exm:commutative-idele-class-group>

As a direct consequence of @th:genus-idele-double-cosets and the above example,
we obtain the following result of Maranda~@bib:Maranda1955 (see also
Takahashi~@bib:Takahashi1959):

#theorem[
  Let $R$ be a Dedekind domain whose quotient field $K$ is a global field. Let
  $Gamma$ be an $R$-order in a separable $K$-algebra $B$, and let $M$ be a full
  left $Gamma$-lattice in the left $B$-module $V$. Suppose that $V$ is
  absolutely simple, that is, $"End"_B V tilde.equiv K$. Then the number of
  $Gamma$-isomorphism classes in the genus of $M$ equals the class number of
  $R$, that is, the order of the class group $"Cl"(R)$.
] <th:absolutely-simple-genus-class-number>
#idx("Maranda's Theorem", target: [@th:absolutely-simple-genus-class-number])
#proof[
  In the notation of @th:genus-idele-double-cosets, we have $A=K$. Since
  $Lambda$ is an $R$-order in $A$, we obtain $Lambda=R$. Therefore each
  $Gamma$-lattice $N$ in $K M$ in the genus of $M$ may be written as
  $N=M dot R alpha$ for some $alpha in J(K)$. In fact, $R alpha$ is a fractional
  $R$-ideal $frak(a)$ in $K$, so $N=M frak(a)$. By
  @th:genus-idele-double-cosets, for $alpha,beta in J(K)$,
  $
    M dot R alpha tilde.equiv M dot R beta <=>
    beta in U(Lambda) dot alpha dot u(K)
    <=> R alpha tilde.equiv R beta.
  $
  Thus, the number of isomorphism classes of $N$'s equals the number of ideal
  classes of $R$.
]

Suppose now that $Lambda$ is an arbitrary $R$-order in a separable $K$-algebra
$A$. By analogy with Example~@exm:commutative-idele-class-group above, we wish
to introduce a _locally free class group_ $"Cl"(Lambda)$, whose elements are
“classes” of locally free fractional $Lambda$-ideals.#idx("class group")#idx(
  "locally free class group",
) Thus, $"Cl"(Lambda)$ consists of classes $[Lambda alpha]$, $alpha in J(A)$,
with “addition” of classes given by the formula
$ [Lambda alpha]+[Lambda beta]=[Lambda alpha beta] "for" alpha,beta in J(A). $
(For the case $Lambda=R$, we get the usual ideal class group $"Cl"(R)$ in this
way.) In the proof of Steinitz's Theorem, one of the crucial steps is the use of
exterior powers to show that the Steinitz class of an $R$-lattice is indeed an
isomorphism invariant of the $R$-lattice (see
@prop:commutative-order-steinitz-invariants). Unfortunately, this technique is
no longer available when the order $Lambda$ is not commutative, and the
isomorphism classes of $Lambda alpha$ and $Lambda beta$ do _not_ (generally
speaking) determine the isomorphism class of $Lambda alpha beta$. Indeed, from
Theorem~@th:idele-lattice-multiplication we know that the isomorphism classes of
$Lambda alpha$ and $Lambda beta$ determine the isomorphism class of
$Lambda plus.o Lambda alpha beta$. However, an example due to Swan~@bib:Swan1962
(see Chapter~11 of Volume~II) shows that
#source(681)
one may have
$
  Lambda plus.o Lambda gamma tilde.equiv Lambda plus.o Lambda gamma',
  quad Lambda gamma tilde.equiv.not Lambda gamma',
$
for suitable choice of $Lambda$, and of $gamma,gamma' in J(A)$.

To overcome this difficulty, it is customary to introduce the concept of stable
isomorphism: two projective $Lambda$-lattices $M$ and $N$ are called _stably
isomorphic_ if#idx("stable isomorphism")
$ M plus.o Lambda^((k)) tilde.equiv N plus.o Lambda^((k)) $
for some $k$. (We shall see later that when $K$ is an algebraic number field,
this occurs if and only if $M plus.o Lambda tilde.equiv N plus.o Lambda$; see
Chapter~10 of Volume~II). Each $Lambda alpha$ is locally free, hence
$Lambda$-projective by @prop:projectivity-localization. We now let
$[Lambda alpha]$ denote the stable isomorphism class of $Lambda alpha$. (By
Exercise~@exc:genus-direct-sum-cancellation, we know that any projective
$Lambda$-lattice $M$ which is stably isomorphic to some $Lambda alpha$ must lie
in the genus of $Lambda$; thus $M tilde.equiv Lambda beta$ for some $beta$.)

#definition[
  Let $Lambda$ be an $R$-order in a separable $K$-algebra $A$, and let $J(A)$ be
  the idèle group of $A$ relative to $R$. For each $alpha in J(A)$, let
  $Lambda alpha$ be the locally free fractional $Lambda$-ideal in $A$ which
  corresponds to $alpha$, and let $[Lambda alpha]$ denote its stable isomorphism
  class. The _locally free ideal class group_ of $Lambda$, denoted by
  $"Cl"(Lambda)$, consists of all classes $[Lambda alpha]$, $alpha in J(A)$,
  with addition defined by
  $ [Lambda alpha]+[Lambda beta]=[Lambda alpha beta], quad alpha,beta in J(A). $
  The zero element is $[Lambda]$, and the negative of $[Lambda alpha]$ is
  $[Lambda alpha^(-1)]$. Thus, $"Cl"(Lambda)$ is an additive abelian group.
] <def:locally-free-ideal-class-group>
#idx("class group", target: [@def:locally-free-ideal-class-group])
#idx("locally free class group", target: [@def:locally-free-ideal-class-group])

The order of $"Cl"(Lambda)$ equals the number of stable isomorphism classes
$[Lambda alpha]$, and is therefore at most equal to the number of ordinary
isomorphism classes of full left $Lambda$-lattices in $A$. If $K$ is a global
field, this latter number is finite by the Jordan-Zassenhaus Theorem. This shows
that $"Cl"(Lambda)$ is a finite group whenever $K$ is a global field. We shall
return to the question of calculating $"Cl"(Lambda)$ explicitly in Chapter~11 of
Volume~II.

=== Roiter's Theorem on Genera <ss:roiter-theorem-genera>

Throughout this subsection, let $K$ be a global field, and $Lambda$ an $R$-order
in a separable $K$-algebra $A$. In this situation, we know that the
Jordan-Zassenhaus Theorem is valid (see §@sec:jordan-zassenhaus). Furthermore,
for each maximal ideal $P$ of $R$, the residue class field $R slash P$ is
finite. This is proved in @bib:CurtisReiner1962[CR] §20 when $K$ is an algebraic
number field; for the function field case, see Weiss~@bib:Weiss1963, Chapter~5.
We return here to our earlier convention of using the subscript $P$ to denote
localization at $P$, rather than completion. If $L$, $M$ and $N$ are left
$Lambda$-lattices in
#source(682)
the same genus, then we saw in @cor:genus-addition that $L$ is a direct summand
of $M plus.o N$. In this subsection we shall present a deep generalization of
this result, due to Roiter~@bib:Roiter1966a. The result can also be obtained
from Jacobinski's theory of genera, to be developed later (see Chapter~11 of
Volume~II).

Recall that a $Lambda$-lattice $F$ is called _faithful_ if, for
$lambda in Lambda$, $lambda F=0$ implies $lambda=0$.#idx("faithful") Roiter's
elegant result is as follows:

#theorem[
  Let $M$ and $N$ be $Lambda$-lattices in the same genus, and let $F$ be any
  faithful $Lambda$-lattice. Then $N divides (M plus.o F)$, and indeed
  $ M plus.o F tilde.equiv N plus.o F' $
  for some $Lambda$-lattice $F'$ such that $F' or.curly F$.
] <th:roiter-genus-faithful-summand>
#idx("Roiter's Theorem", target: [@th:roiter-genus-faithful-summand])

All of the difficulty lies in proving that $N divides (M plus.o F)$, since the
second assertion is then an easy consequence of this fact (see
Exercise~@exc:genus-direct-sum-cancellation). Since $Lambda$ is itself a
faithful $Lambda$-lattice, the theorem implies that
$ N or.curly M=>N divides (M plus.o Lambda) $
(compare with Exercise~@exc:nonprincipal-ideal-local-direct-summand, and
Theorem~@th:roiter-local-direct-summand below). The proof of Roiter's Theorem is
based on several lemmas. We follow the treatment in Swan-Evans~@bib:Swan1970.

#lemma[
  Let $M$ and $N$ be $Lambda$-lattices in the same genus, and let $frak(a)$ be a
  nonzero ideal of $R$. Then there exists a $Lambda$-exact sequence
  $ 0->M->N->T->0, $
  where $T$ is an $R$-torsion $Lambda$-module such that:
  #enum(
    numbering: "(i)",
    [$frak(a)+"ann" T=R$, and],
    [$T tilde.equiv product.co_(i=1)^k T_i$ for some finite collection of simple
      $Lambda$-modules ${T_i}$, such that
      $ "ann" T_i+"ann" T_j=R quad "for" i!=j, quad 1<=i,j<=k. $],
  )
  Here, $"ann"$ means $"ann"_R$.
] <lem:roiter-coprime-simple-cokernel>
#proof[
  Let $n=dim_K K M$ be the $R$-rank of $M$. By the Jordan-Zassenhaus Theorem,
  there are finitely many isomorphism classes of $Lambda$-lattices of rank $n$;
  let ${M_i:1<=i<=q}$ be representatives of these classes.

  Let $S$ be any simple left $Lambda$-module; then $P S=0$ for some maximal
  ideal $P$ of $R$. For if this is not the case, then $P S=S$ for each $P$,
  whence $P dot S_P=S_P$, so $S_P=0$ for each $P$ by Nakayama's Lemma; this
  implies that $S=0$, a contradiction.

  #source(683)
  We now consider all embeddings of $M_i$ into $M_j$, such that the factor
  module is a simple $Lambda$-module. Each such embedding corresponds to an
  exact sequence
  $ 0->M_i arrow.r^f M_j->S_f->0, $ <eq:roiter-simple-quotient-embeddings>
  where $S_f$ is a simple left $Lambda$-module and the subscript $f$ is merely
  an index to show that $S_f$ depends on $f$. Here, $i$ and $j$ range
  independently from~1 to $q$, including the cases where $i=j$.

  For a given ordered pair of indices $(i,j)$, we consider all possible
  sequences of the form @eq:roiter-simple-quotient-embeddings. We shall call
  $(i,j)$ a _good_ pair if the set of ideals
  $ {"ann" S_f:"all" f} $
  is infinite; otherwise, we call the pair $(i,j)$ _bad_. For each bad pair
  $(i,j)$, there are only finitely many ideals in the set ${"ann" S_f}$, and
  each of these is a maximal ideal of $R$ by the earlier comments. We now put
  $
    frak(b)=product_((i,j) "bad") {product_f "ann" S_f},
    quad "a nonzero ideal of" R.
  $
  In the inner product, $"ann" S_f$ ranges over the distinct prime ideals of $R$
  which occur as annihilators of simple factor modules $S_f=M_j slash f(M_i)$.
  Since $M or.curly N$, by Roiter's Lemma there exists a $Lambda$-exact sequence
  $ 0->M->N arrow.r^phi Y->0, $
  with $Y$ an $R$-torsion $Lambda$-module such that
  $ frak(a)frak(b)+"ann" Y=R. $
  Since $Y$ is a finite $Lambda$-module#footnote[
    The finiteness of $Y$ follows from the fact that $K$ is a global field, so
    $R slash frak(a)$ is finite for each nonzero ideal $frak(a)$ of $R$ (see
    introductory remarks for this subsection).
  ], it has a $Lambda$-composition series:
  $ Y=Y_0 supset Y_1 supset dots supset Y_r=0. $
  Put $N_l=phi^(-1)(Y_l)$, $0<=l<=r$. Then we obtain a chain
  $
    N=N_0 supset N_1 supset dots supset N_r=M,
    quad N_l slash N_(l+1)="simple" Lambda"-module".
  $
  Consider the sequence $0->N_1->N_0->N_0 slash N_1->0$; we have
  $N_1 tilde.equiv M_i$, $N_0 tilde.equiv M_j$ for some pair $(i,j)$, and thus
  we have an exact sequence of the form @eq:roiter-simple-quotient-embeddings,
  with $S=N_0 slash N_1$. But $S$ is a composition factor of $Y$, so
  $"ann" S+frak(b)=R$; this implies at once that $(i,j)$ is a good pair! But
  then there exist embeddings $N_1->N_0$ such that $"ann"(N_0 slash N_1)$ ranges
  over an infinite set of primes. In particular, we
  #source(684)
  may find an exact sequence
  $ 0->N_1->N_0->T_1->0, $
  where $T_1$ is a simple $Lambda$-module such that
  $ "ann" T_1+frak(a)=R. $
  Repeating this argument for the pair $N_1$ and $N_2$, we obtain an exact
  sequence
  $ 0->N_2->N_1->T_2->0, $
  with
  $ "ann" T_2+frak(a) dot "ann" T_1=R, quad T_2 "simple". $
  Continuing in this manner, we arrive at an exact sequence
  $ 0->M->N->T->0 $
  with $T$ an $R$-torsion $Lambda$-module, such that the $Lambda$-composition
  factors of $T$ are ${T_1,T_2,dots,T_r}$, and where
  $
    "ann" T_i+"ann" T_j=R, quad "ann" T_i+frak(a)=R,
    quad 1<=i,j<=r, quad i!=j.
  $
  But then the Primary Decomposition Theorem~@th:primary-decomposition-dedekind
  gives $T tilde.equiv product.co_(i=1)^r T_i$, which completes the proof of the
  lemma.
]

#lemma[
  Let $Lambda$ be an $R$-order in $A$, and let $alpha in R$ be a nonzero element
  such that $alpha Lambda' subset.eq Lambda subset.eq Lambda'$, where $Lambda'$
  is a maximal $R$-order in $A$. Let
  $ T=product.co_1^r T_i, quad T_i="simple" Lambda"-module", $
  where
  $
    "ann" T_i+"ann" T_j=R, quad "ann" T_i+R alpha=R,
    quad 1<=i,j<=r, quad i!=j.
  $
  Then for each faithful $Lambda$-lattice $F$, there exists a surjection of $F$
  onto $T$.
] <lem:faithful-lattice-simple-quotients>
#proof[
  We shall find surjections $phi_i:F->T_i$, $1<=i<=r$. Then $sum_(i=1)^r phi_i$
  yields a map $F->T$ which is surjective at each maximal ideal $P$ of $R$, and
  hence is surjective (by §@sec:dedekind-domains), as desired.

  #source(685)
  Changing notation, let $T$ be a simple $Lambda$-module such that $"ann" T=P$,
  where $P$ is a maximal ideal of $R$ such that $P+alpha R=R$. Then
  $P+"ann"(Lambda' slash Lambda)=R$, whence $Lambda'_P=Lambda_P$, so $Lambda_P$
  is a maximal order. Since $F$ is a faithful $Lambda$-module, it follows that
  $K F$ is a faithful $A$-module, whence $A divides (K F)^((m))$ for some $m$.
  Then $Lambda_P divides F_P^((m))$ by
  Exercise~@exc:maximal-order-generic-direct-summand. But $T$ is a factor module
  of $Lambda_P slash P Lambda_P$, since $P dot T=0$ and $T$ is simple. Hence $T$
  is also a factor module of $F_P^((m)) slash P F_P^((m))$. This latter quotient
  is isomorphic to $F^((m)) slash P F^((m))$, so there exists a surjection
  $psi:F^((m))->T$. Then $psi$ must map at least one of the summands of
  $F^((m))$ onto $T$, since $T$ is simple. Hence there is a surjection of $F$
  onto $T$, as claimed.
]

We may now prove Roiter's Theorem~@th:roiter-genus-faithful-summand.#idx(
  "Roiter's Theorem",
) Let $M$ and $N$ be $Lambda$-lattices in the same genus, and let $alpha in R$
be a nonzero element such that
$alpha Lambda' subset.eq Lambda subset.eq Lambda'$ as in
@lem:faithful-lattice-simple-quotients. By @lem:roiter-coprime-simple-cokernel,
there exists a $Lambda$-exact sequence
$ 0->M->N->T->0 $
where
$
  "ann" T+alpha R=R, quad T tilde.equiv product.co_1^r T_i
  "as in" #[@lem:roiter-coprime-simple-cokernel] "(ii)".
$
By @lem:faithful-lattice-simple-quotients, we can find an exact sequence
$ 0->F'->F arrow.r^phi T->0, quad "where" F'=ker phi. $
If $Lambda=Lambda'$, then $N$ is $Lambda$-projective, and then
$M plus.o F tilde.equiv N plus.o F'$ by Schanuel's Lemma. If $Lambda!=Lambda'$,
then for each $P$ such that $Lambda_P!=Lambda'_P$ we have $alpha in P$, so
$"ann" T+P=R$ and therefore $T_P=0$. The desired isomorphism now follows from
@prop:genus-schanuel, which completes the proof of Roiter's Theorem.

To illustrate the power of Roiter's Theorem, let us derive two important and
beautiful consequences, which were proved independently by
Roiter~@bib:Roiter1966a and Jacobinski~@bib:Jacobinski1968b:

#theorem[
  Let $M$ and $N$ be $Lambda$-lattices, and suppose that $N_P divides M_P$ for
  each $P in S(Lambda)$, where $S(Lambda)$ is defined by
  @eq:nonmaximal-order-primes. Assume that every $A$-composition factor of $K N$
  occurs strictly more often in $K M$ than in $K N$. Then $N divides M$ as
  $Lambda$-lattices.
] <th:roiter-local-direct-summand>
#idx("Jacobinski's Theorem", target: [@th:roiter-local-direct-summand])
#proof[
  By @th:genus-local-direct-summand, $M=N' plus.o L$ for some $Lambda$-lattice
  $N'$ in the genus of $N$, and some $Lambda$-lattice $L$. Let
  $I="ann"_Lambda M$; then $I$ is a two-sided ideal of $Lambda$, and
  $Lambda_1=Lambda slash I$ is an $R$-order which acts faithfully on $M$ (see
  §@sec:lattices-orders). We claim that $L$ is also a faithful
  $Lambda_1$-lattice. Indeed, we have
  $ K M=K N' plus.o K L tilde.equiv K N plus.o K L. $
  #source(686)
  Since $A$ is semisimple, each of the above modules is isomorphic to the direct
  sum of its composition factors. By hypothesis, every composition factor of
  $K N$ is also a composition factor of $K L$. Hence for $y in K Lambda_1$,
  $ y dot K L=0=>y dot K N=0=>y dot K M=0=>y=0, $
  which shows that $K L$ is a faithful $K Lambda_1$-module. This implies at once
  that $L$ is a faithful $Lambda_1$-lattice.

  Applying @th:roiter-genus-faithful-summand to the order $Lambda_1$ in place of
  $Lambda$, we obtain
  $ N' plus.o L tilde.equiv N plus.o L' $
  for some $Lambda_1$-lattice $L'$ in the genus of $L$. Therefore
  $M tilde.equiv N plus.o L'$ as $Lambda$-lattices, and the proof is complete.
]

Let $Gamma_M$ denote the genus of a $Lambda$-lattice $M$, and let $g(M)$ be the
number of $Lambda$-isomorphism classes in $Gamma_M$. Under our hypothesis that
$K$ is a global field, it follows at once from the Jordan-Zassenhaus Theorem
that $g(M)$ is finite for each $M$. We shall now show that there exists a
constant $g_0$, depending on $Lambda$ but not on $M$, such that $g(M)<=g_0$ for
each $M$. The result is due to Roiter~@bib:Roiter1966a and
Jacobinski~@bib:Jacobinski1968b, and we give Roiter's proof below. (There is
also a proof by Drozd~@bib:Drozd1969a which uses adèles; see also
Platonov~@bib:Platonov1969.)

Let $M_1,dots,M_g$ be a full set of non-isomorphic $Lambda$-lattices in the
genus $Gamma_M$ of a given $Lambda$-lattice $M$. We choose a nonzero
$alpha in R$ such that $alpha Lambda' subset.eq Lambda subset.eq Lambda'$, where
$Lambda'$ is a maximal $R$-order in $A$ containing $Lambda$. We may view each
$M_i$ as embedded in $M$, and we can find $Lambda$-exact sequences
$ 0->M_i->M->U_i->0, quad 1<=i<=g, $
such that
$
  "ann" U_i+"ann" U_j=R, quad "ann" U_i+R alpha=R
  "for" 1<=i,j<=g, quad i!=j,
$
and such that for each $i$, $U_i$ is a finite direct sum of simple
$Lambda$-modules ${T_(i j)}$, with
$ "ann" T_(i j)+"ann" T_(i k)=R quad "for" j!=k, $
(see the proof of @lem:roiter-coprime-simple-cokernel). Now put
$N=M_1 inter dots inter M_g subset.eq M$. Then there is a $Lambda$-monomorphism
$ psi:M slash N->product.co_(i=1)^g (M slash M_i), $
and we claim $psi$ is an isomorphism. It suffices to show that $psi_P$ is
surjective for each $P$, where the subscript denotes localization at the maximal
ideal $P$ of $R$. If $(M slash M_i)_P=0$ for each $i$, then surely $psi_P$ is
surjective. On the other hand, if (say) $(M slash M_1)_P!=0$, then
$P divides "ann" U_1$, whence $P+"ann" U_j=R$ for $j>1$, and then
#source(687)
$(M slash M_j)_P=0$ for $j>1$. Thus we have
$ N_P=(M_1)_P inter dots inter (M_g)_P=(M_1)_P, $
so $psi_P$ is surjective, as desired. This completes the proof that
$ M slash N tilde.equiv product.co (M slash M_i). $
We thus have a $Lambda$-exact sequence
$ 0->N->M->product.co_(i=1)^g U_i->0. $
We note also that $N or.curly M$, since $N_P=M_P$ whenever
$P supset.eq R alpha$.

On the other hand, by @lem:faithful-lattice-simple-quotients there is also a
$Lambda$-exact sequence
$ 0->L_0->Lambda->product.co_(i=1)^g U_i->0, $
so we can find a $Lambda$-homomorphism $theta$ for which the following diagram
commutes:
#genus-projective-lift()
Let $L=M inter K dot theta(Lambda)$; then $L$ is an $R$-pure $Lambda$-sublattice
of $M$, and
$ "rank"_R L<="rank"_R Lambda=dim_K A. $
From the above diagram we obtain $M=N+theta(Lambda)=N+L$, since
$L supset.eq theta(Lambda)$. Therefore
$M slash L tilde.equiv N slash (L inter N)$, so there is an exact sequence of
$Lambda$-lattices #named-equation(name: [$(xi)$])[
  $ 0->L inter N->N arrow.r^h M slash L->0. $
] <eq:roiter-genus-bound-extension>
Here, $xi in "Ext"(M slash L,L inter N)$, where $"Ext"$ means $"Ext"_Lambda^1$.
For each $i$, $1<=i<=g$, there is an inclusion map $mu_i:N->M_i$, and then
$M=N+L=M_i+L$. We obtain a commutative diagram with exact rows:
#genus-extension-inclusions()
#source(688)
Here, $xi_i in "Ext"(M slash L,L inter M_i)$; the commutativity of the diagram
gives $xi_i=f_i xi$ by §@ss:ext-tor.

Applying $Hom_Lambda lr((ast,L inter M_i))$ to the exact sequence
@eq:roiter-genus-bound-extension, we obtain a long exact sequence
$
  dots->Hom(N, L inter M_i) arrow.r^(h^*) Hom(L inter N, L inter M_i)
  arrow.r^∂ "Ext"(M slash L,L inter M_i)->dots.
$
By §@ss:ext-tor we have $xi_i=∂(f_i)$, so the isomorphism class of $M_i$ is
determined by the isomorphism class of $L inter M_i$ and by the choice of $f_i$.
Since $(mu_i)_P$ is an isomorphism whenever $P supset.eq R alpha$, so is
$(f_i)_P$, and therefore $(L inter M_i) or.curly (L inter N)$ for each $i$. The
number of possible isomorphism classes of $L inter M_i$, as $i$ varies, is
therefore $<=g(L inter N)$. Since
$ "rank"_R lr((L inter N))<="rank"_R L<=dim_K A, $ <eq:roiter-genus-bound-rank>
it follows from the Jordan-Zassenhaus Theorem that there exists a constant
$g_1$, independent of $N$, for which $g(L inter N)<=g_1$ for all $N$. Therefore
$g(M)<=g_1 g_2$, where $g_2$ is an upper bound for the order of the image of $∂$
in $"Ext"(M slash L,L inter M_i)$.

Let $tilde(R)$ be as in the proof of @prop:genus-semilocal-isomorphism. Then
$f_i$ induces an isomorphism $tilde(L) inter tilde(N) tilde.equiv tilde(L) inter
tilde(M)_i$, and by @prop:extension-localization-nonmaximal-primes we obtain a
commutative diagram
#genus-bound-connecting-maps()
in which the vertical maps are isomorphisms. Thus
$ |"im" ∂|=|"im" ∂'|=|"im" tilde(∂)|. $
Since $alpha dot "im" tilde(∂)=0$ by @cor:uniform-order-ext-annihilator, we have
$
  |"im" tilde(∂)|<=|"End"(tilde(L) inter tilde(N)):
  alpha dot "End"(tilde(L) inter tilde(N))|.
$
This index is finite, bounded independently of $N$ because of
@eq:roiter-genus-bound-rank. If $g_2$ is an upper bound, then we have
$g(M)<=g_1 g_2$, and we have thus proved:

#theorem[
  Let $K$ be a global field, $A$ a separable $K$-algebra, and $Lambda$ any
  $R$-order in $A$. Let $g(M)$ denote the number of $Lambda$-isomorphism classes
  in the genus of a given $Lambda$-lattice $M$. Then there exists a positive
  integer $g_0$, depending on $Lambda$ but not on $M$, such that $g(M)<=g_0$ for
  all $M$.
] <th:uniform-genus-class-number-bound>
#idx("Roiter's Theorem", target: [@th:uniform-genus-class-number-bound])
#idx("Jacobinski's Theorem", target: [@th:uniform-genus-class-number-bound])

#remarks(numbered: true)[
  #enum(
    numbering: "(i)",
    [We may improve our bound $g_2$ above as follows: let $D=L inter N$, and put
      $tilde(D)=tilde(R) times.o_R D$. By
      @cor:extension-isomorphism-automorphism-orbits, the isomorphism class of
      the extension of $M slash L$ by $L inter M_i$ corresponding to $f_i$ is
      unchanged if we replace $tilde(f)_i$ by $tilde(f)_i theta$, with
      $theta in "Aut"_Lambda D$. We may therefore choose $g_2$ to be an upper
      bound for
      #source(689)
      the index of the image of $"Aut"_Lambda D$ in the group of units of the
      ring $"End"(tilde(D)) slash alpha dot "End"(tilde(D))$. This procedure is
      needed in §@ss:matrix-order-drozd-turcin, for example.],
    [Roiter conjectured that $g(M)<=g(Lambda)$ for all $M$. The Drozd-Turčin
      example in §@ss:matrix-order-drozd-turcin shows that this conjecture is
      false. Roggenkamp also gave a counterexample, based on Swan's
      counterexample to “cancellation” of lattices.],
    [Roiter raised the following question: given a $Lambda$-lattice $M$, is
      every lattice in the genus of $M$ isomorphic to a maximal sublattice? This
      question was answered by Drozd~@bib:Drozd1969b and
      Jacobinski~@bib:Jacobinski1970. It is easy to find counterexamples when
      the $K$-algebra $A$ has more than one simple component, so we may restrict
      our attention to the case where $A$ is simple. Drozd and Jacobinski proved
      that the answer is affirmative in this case, under the hypothesis that $M$
      is an Eichler lattice (see the discussion following
      @def:genus-cancellation below). We shall treat this question in detail in
      Chapter~11 of Volume~II.],
    [Let $M$ be a left $Gamma$-lattice, where $Gamma$ is an $R$-order in a f.d.
      $K$-algebra $B$ which need not be semisimple. Drozd~@bib:Drozd1971
      investigated the number $g(M)$ of $Gamma$-isomorphism classes in the genus
      of $M$. Set
      $
        Lambda="End"_Gamma M, quad A=K Lambda, quad overline(A)=A slash "rad" A,
        quad overline(Lambda)=Lambda slash (Lambda inter "rad" A),
      $
      so $overline(Lambda)$ is an $R$-order in the semisimple $K$-algebra
      $overline(A)$. Theorem~@th:genus-idele-double-cosets carries over
      unchanged, as does the relation between $Gamma$-lattices in the genus of
      $M$ and locally free left ideals of $Lambda$.

      Each locally free left ideal $L$ of $Lambda$ gives rise to a locally free
      ideal $overline(L)$ of $overline(Lambda)$, namely
      $overline(L)=L slash (Lambda inter "rad" A)L$. The correspondence
      $L arrow.l.r overline(L)$ is a bijection from the genus of $Lambda$ to the
      genus of $overline(Lambda)$.

      Assume now that $K$ is an algebraic number field, so $g(overline(Lambda))$
      is finite. It follows that $g(Lambda)$ is finite, and therefore so is
      $g(M)$. Drozd gave an example to show that there need not be a uniform
      upper bound on $g(M)$, where $M$ ranges over all $Gamma$-lattices. Thus,
      the analogue of @th:uniform-genus-class-number-bound need not be valid for
      orders in non-semisimple algebras.],
  )
] <rem:genus-bounds-nonseparable-algebras>

#exercises-heading

#exercise[
  Let $R$ be a d.v.r., $hat(R)$ its completion, and let $Lambda$ be an
  $R$-order. Show that an exact sequence of $Lambda$-lattices #named-equation(
    name: [$(xi)$],
  )[
    $ 0->L->M arrow.r^f N->0 $
  ] <eq:completion-splitting-source-sequence>
  is split if and only if the corresponding sequence of $hat(Lambda)$-lattices
  #named-equation(name: [$(hat(xi))$])[
    $ 0->hat(L)->hat(M) arrow.r^(hat(f)) hat(N)->0 $
  ] <eq:completion-splitting-completed-sequence>
  is split.

  #source(690)
  #hint([@exc:completion-exact-sequence-splitting])[
    If the latter sequence is split, then by
    @lem:simultaneous-lattice-homomorphism-approximation we can find $v:N->M$
    such that $hat(f)hat(v) in "Aut" hat(N)$. This implies that
    $f v in "Aut" N$, so $v(f v)^(-1)$ is the desired splitting of $f$.

    Another proof is as follows: From @th:ext-flat-change-of-rings we have
    $
      hat(R) times.o_R "Ext"_Lambda^1 lr((N,L)) tilde.equiv
      "Ext"_(hat(Lambda))^1 lr((hat(N),hat(L))),
    $
    and in the embedding
    $"Ext"_Lambda^1 lr((N,L))->"Ext"_(hat(Lambda))^1 lr((hat(N),hat(L)))$, the
    sequence @eq:completion-splitting-source-sequence maps onto the sequence
    @eq:completion-splitting-completed-sequence. Hence
    $#[@eq:completion-splitting-source-sequence]=0$ if and only if
    $#[@eq:completion-splitting-completed-sequence]=0$.
  ]
] <exc:completion-exact-sequence-splitting>

#exercise[
  Let $Lambda$ be a maximal order, and let $M$ and $N$ be $Lambda$-lattices such
  that $K N divides K M$. Show that there exists a $Lambda$-lattice $N'$ with
  $N' or.curly N$ and $N' divides M$.

  #hint([@exc:maximal-order-generic-direct-summand])[
    We may write $K M tilde.equiv K(N plus.o L)$ for some $Lambda$-lattice $L$,
    by @cor:full-order-lattice-existence. Then $M_P tilde.equiv N_P plus.o L_P$
    for every $P$, by Exercise~@exc:dvr-maximal-order-lattice-isomorphism. Now
    use the proof of @th:genus-local-direct-summand.
  ]
] <exc:maximal-order-generic-direct-summand>

#exercise[
  Let $L$, $L'$, $M$ and $M'$ be $Lambda$-lattices such that
  $ L plus.o M tilde.equiv L' plus.o M', quad L or.curly L'. $
  Prove that $M or.curly M'$.
] <exc:genus-direct-sum-cancellation>

#exercise[
  Let $frak(a)$ be a nonprincipal ideal of the Dedekind domain $R$. Show that
  $frak(a)$ is a local direct summand of $R$ (that is, $frak(a)_P divides R_P$
  for each maximal ideal $P$ of $R$), but that $frak(a)$ is not a direct summand
  of $R$. Prove that $frak(a) divides R^((2))$, however.
] <exc:nonprincipal-ideal-local-direct-summand>

#exercise[
  Let $M_1$ and $M_2$ be $Lambda$-lattices such that every $A$-composition
  factor of $K M_2$ is also a composition factor of $K M_1$. Let $g(M)$ denote
  the number of $Lambda$-isomorphism classes in the genus of the
  $Lambda$-lattice $M$. Prove that
  $ g(M_1 plus.o M_2)<=g(M_1). $

  #hint([@exc:genus-class-number-direct-sum-bound])[
    Let $N or.curly (M_1 plus.o M_2)$, so $M_2$ is a local summand of $N$. By
    @th:roiter-local-direct-summand we obtain $N tilde.equiv M'_1 plus.o M_2$
    for some $M'_1 or.curly M_1$, which implies the result.
  ]
] <exc:genus-class-number-direct-sum-bound>

#exercise[
  Let $hat(R)$ be the completion of a d.v.r. $R$, and let $M$ and $N$ be
  $Lambda$-lattices, where $Lambda$ is an $R$-order. Show that if
  $hat(N) divides hat(M)$, then $N divides M$.

  #hint([@exc:completion-lattice-summand-descent])[
    Use @eq:completed-lattice-homomorphisms. See also
    Exercise~@exc:module-summand-completion.
  ]
] <exc:completion-lattice-summand-descent>

#exercise[
  Let $0->L->M->N->0$ be an exact sequence of $Lambda$-lattices, and let
  $M' in Gamma_M$. Show that there exist lattices $L' in Gamma_L$,
  $N' in Gamma_N$, and a commutative diagram with exact rows
  #genus-exercise-inclusions()
  such that
  #enum(
    numbering: "(i)",
    [$alpha$, $beta$, $gamma$ are $Lambda$-monomorphisms with $R$-torsion
      cokernels, and],
    [For each $P in S(Lambda)$, the maps $alpha_P$, $beta_P$ and $gamma_P$ are
      $Lambda_P$-isomorphisms.],
  )

  #source(691)
  #hint([@exc:genus-exact-sequence-subobjects])[
    If $S(Lambda)!=emptyset$, then~(ii) implies~(i), since if $alpha_P$ is an
    isomorphism for even one choice of $P$, then
    $ (ker alpha)_P=0, quad ("cok" alpha)_P=0, $
    whence $ker alpha=0$ and $"cok" alpha$ is an $R$-torsion $Lambda$-module.
    Now let $S_0=S(Lambda)$ if $S(Lambda)!=emptyset$, and let $S_0={P_0}$ for
    some maximal ideal $P_0$ of $R$ when $S(Lambda)=emptyset$. It suffices to
    prove~(ii) with $S(Lambda)$ replaced by $S_0$. By @lem:roiter-genus, there
    exists a $Lambda$-monomorphism $beta$ with $beta_P$ an isomorphism for each
    $P in S_0$. Let $phi:M->N$ be the quotient map. Put
    $N'=(phi beta)(M') subset.eq N$, and let $gamma$ be the inclusion map. There
    is then an induced map $alpha:L'->L$ giving rise to the above commutative
    diagram. For each $P in S_0$, $alpha_P$ and $gamma_P$ are isomorphisms,
    which implies that $L' or.curly L$, $N' or.curly N$.
  ]
] <exc:genus-exact-sequence-subobjects>

#exercise[
  Let $0->L->M->N->0$ be an exact sequence of $Lambda$-lattices, and let
  $M' in Gamma_M$. Show that there exist lattices $L' in Gamma_L$,
  $N' in Gamma_N$, and a commutative diagram with exact rows
  #genus-exercise-overobjects()
  such that
  #enum(
    numbering: "(i)",
    [$lambda$, $mu$, $nu$ are $Lambda$-monomorphisms with $R$-torsion cokernels,
      and],
    [For each $P in S(Lambda)$, the maps $lambda_P$, $mu_P$ and $nu_P$ are
      $Lambda_P$-isomorphisms.],
  )

  #hint([@exc:genus-exact-sequence-overobjects])[
    Let $S_0$ be as in Exercise~@exc:genus-exact-sequence-subobjects, and choose
    a monomorphism $mu$ such that $mu_P$ is an isomorphism for each $P in S_0$.
    Replacing $M'$ by an isomorphic copy if need be, we may assume that
    $K M=K M'$ and that $M_P=M'_P$ for each $P in S_0$. Define
    $L'=K L inter M'$, an $R$-pure sublattice of $M'$, and let $N'=M' slash L'$.
    The map $mu$ induces maps $lambda$, $nu$, with $lambda_P$ and $nu_P$
    isomorphisms for $P in S_0$. This implies that~(i) holds as well as~(ii).
  ]
] <exc:genus-exact-sequence-overobjects>

#exercise[
  Keep the notation of the preceding exercise. Show that if
  $M tilde.equiv L plus.o N$ then $M' tilde.equiv L' plus.o N'$. This gives a
  slightly different proof of @cor:genus-direct-sum-decomposition.
] <exc:genus-split-extension-invariance>

#exercise[
  Let $L$ and $M$ be $Lambda$-lattices in the same genus, and let $Lambda'$ be
  any $R$-order in $A$ containing $Lambda$. Prove that
  $
    M plus.o (Lambda' times.o_Lambda L) tilde.equiv
    L plus.o (Lambda' times.o_Lambda M)
  $
  as $Lambda$-modules.

  #hint([@exc:genus-overorder-tensor-exchange])[
    There is an exact sequence of two-sided $Lambda$-modules
    $0->Lambda->Lambda'->U->0$, with $U$ an $R$-torsion module. Let
    $0->L->M->T->0$ be a $Lambda$-exact sequence such that $T_P=0$ whenever
    $P in S(Lambda)$ or whenever $U_P!=0$. In the $Lambda$-exact sequence
    $ Lambda times.o T arrow.r^phi Lambda' times.o T->U times.o T->0 $
    we have $ker phi_P=0$, $(U times.o T)_P=0$ for all $P$, whence
    $Lambda' times.o T tilde.equiv T$. Then
    $ Lambda' times.o L arrow.r^psi Lambda' times.o M->T->0 $
    is exact, and $ker psi_P=0$ for all $P$, so $psi$ is monic. The proof of
    @prop:genus-schanuel still applies here.#ed-note[
      The original hint applies the lattice statement directly to tensor
      modules, which can have $R$-torsion. For example, for
      $Lambda={(a,b) in ZZ^2:a equiv b (mod 2)}$, $Lambda'=ZZ^2$, and $L=ZZ$ via
      the first projection, $Lambda' times.o_Lambda L tilde.equiv
      ZZ plus.o (ZZ slash 2 ZZ)$. The local pullback argument below avoids a
      torsionfreeness assumption on these tensor modules.
    ] Form the pullback of $M->T$ and $Lambda' times.o_Lambda M->T$. At
    $P in S(Lambda)$, we have $T_P=0$, so both pullback rows split. Outside
    $S(Lambda)$, the order $Lambda_P$ is maximal, hence $Lambda'_P=Lambda_P$;
    the tensor modules there are the original projective lattices. Thus both
    rows split at every maximal ideal. Their extension classes vanish globally
    by localization of $"Ext"^1$ for finitely presented modules. The two
    splittings give the desired isomorphism, without assuming that the tensor
    modules are lattices.
  ]
] <exc:genus-overorder-tensor-exchange>

#source(692)
#exercise[
  Keep the above notation. Show that the kernel of the surjection
  $Lambda' times.o L->Lambda' L$ is precisely the $R$-torsion submodule of
  $Lambda' times.o L$. Deduce that
  $ M plus.o Lambda' L tilde.equiv L plus.o Lambda' M. $

  #hint([@exc:genus-overorder-product-exchange])[
    Use Exercise~@exc:overorder-tensor-product-kernel and the fact that
    isomorphisms preserve $R$-torsion submodules.
  ]
] <exc:genus-overorder-product-exchange>

#exercise[
  Let $Lambda$ be an $R$-order in a separable $K$-algebra $A$, and let $Lambda'$
  be a maximal $R$-order in $A$ containing $Lambda$. Let $X$ be a
  $Lambda'$-lattice such that $K X tilde.equiv A^((r))$. Show that there exists
  a projective $Lambda$-lattice $M$ for which
  $ Lambda' times.o_Lambda M tilde.equiv X, quad K M tilde.equiv A^((r)). $

  #hint([@exc:projective-lattice-maximal-overorder-lift])[
    We may assume that $Lambda'!=Lambda$, so $S(Lambda)!=emptyset$. By
    @prop:genus-nonmaximal-primes, $X or.curly (Lambda')^((r))$; hence by
    Roiter's Lemma there is a $Lambda'$-lattice $Y$ isomorphic to $X$, such that
    $Y_P=(Lambda'_P)^((r))$ for each $P in S(Lambda)$, with
    $Y subset.eq A^((r))$. Choosing $M=Y inter Lambda^((r))$, we have
    $ M_P=Y_P inter Lambda_P^((r))=Lambda_P^((r)) $
    for each $P in S(Lambda)$. Then $M$ is a projective $Lambda$-lattice by
    @cor:genus-local-splitting-projectivity, and has the desired properties.
  ]
] <exc:projective-lattice-maximal-overorder-lift>

#exercise[
  Let $R$ be a Dedekind domain with quotient field $K$, and let $I$ be a
  fractional $R$-ideal in $K$. Let ${P_1,dots,P_n}$ be some given set of
  distinct maximal ideals of $R$. Show that there exists an $x in K^dot$ such
  that $I x$ is an ideal in $R$ which is coprime to each $P_j$.

  #hint([@exc:ideal-class-coprime-representative])[
    The $R$-module $I$ is in the same genus as $R$, so by Roiter's
    Lemma~@lem:roiter-genus there exists an exact sequence of $R$-modules
    $ 0->I arrow.r^theta R->T->0, $
    in which $T$ is an $R$-torsion module such that
    $ "ann"_R T+P_j=R, quad 1<=j<=n. $
    Then $theta$ is right multiplication by some $x in K^dot$, and $I x$ has the
    desired properties.

    The above result asserts that every ideal class of $R$ contains an integral
    ideal coprime to any preassigned finite collection of maximal ideals of $R$.
    The proof given in @bib:CurtisReiner1962[CR] (18.20) is essentially a
    special case of the proof of Roiter's Lemma. Likewise, the proof of
    Steinitz's identity $I plus.o J tilde.equiv R plus.o I J$ for $I$ and $J$
    fractional ideals (see @th:steinitz) above, is a special case of
    @prop:genus-schanuel and @th:idele-lattice-multiplication.
  ]
] <exc:ideal-class-coprime-representative>

