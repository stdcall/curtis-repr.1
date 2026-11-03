#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/30-local-theory.typ": *

== Local Theory <sec:local-theory>

The local theory deals with representations of groups and orders over some
commutative local ring $R$. Usually, $R$ will be a d.v.r., and in many cases we
impose the further requirement that $R$ be complete. A particularly important
local result is that the K-S-A Theorem holds for $Lambda$-lattices, where
$Lambda$ is an
#source(641)
$R$-order, with $R$ complete. This fact, as well as other basic facts proved in
the introductory sections
§§@sec:radicals–@sec:idempotents-krull-schmidt-projective-covers, is reviewed at
the beginning of this section.

In §@ss:reduction-mod-prime-powers, we prove Maranda's Theorems and related
results. Let $Lambda$ be an $R$-order, where $R$ is a d.v.r. with maximal ideal
$P$ and residue class field $overline(R)=R slash P$. (This represents a change
from the notation in Chapter~@ch:modular-representations.) The first main result
is that a $Lambda$-lattice $M$ is projective if and only if $M slash P M$ is
$(Lambda slash P Lambda)$-projective. Furthermore, if $M$ and $N$ are projective
$Lambda$-lattices, then $M tilde.equiv N$ if and only if
$M slash P M tilde.equiv N slash P N$. Maranda's Theorems generalize these
facts, and show that an arbitrary $Lambda$-lattice is determined, as to
isomorphism, decomposability, etc., by its behavior mod $P^k$ for some
sufficiently large $k$, depending on $Lambda$ but not on $M$. This result on
decomposability may be viewed as a generalization of Hensel's Lemma (see
Exercise~@exc:hensel-factorization), or of the Theorem on Lifting Idempotents
@th:lifting-idempotents.

Section~@ss:extension-ground-ring-local-theory takes up the technique of ground
ring extension. If $R subset.eq S$ are complete d.v.r.'s, with quotient fields
$K$ and $L$, respectively, then each $Lambda$-lattice $M$ gives to an
$S Lambda$-lattice $S M$. We prove the Reiner-Zassenhaus Theorem, which says
that $S M$ determines $M$ up to isomorphism. We next investigate the
decomposition of $S M$ into indecomposable $S Lambda$-modules, and show how this
is related to the decomposition of
$ overline(S) times.o_(overline(R)) {E(M) slash rad E(M)}, $
where $overline(R)$ and $overline(S)$ are the residue class fields of $R$ and
$S$, respectively, and $E(M)=End M$. This enables us to decide whether the
$Lambda$-lattice $M$ is absolutely indecomposable. It also implies that for each
$M$, we can find an $S$ such that $S M$ is a direct sum of absolutely
indecomposable lattices. Indeed, we can find an $S$ which works for all $M$'s
simultaneously, provided we permit $dim_K L$ to be infinite.

In §@ss:representations-mod-prime-powers, we give a brief introduction to the
theory of representations of orders by matrices with entries in $R slash P^k$.
This theory is rather undeveloped, and is surprisingly difficult.

We fix the following notation for the entire section:
$
  cases(
    #[$R=$ commutative local noetherian ring],
    #[$P=$ unique maximal ideal of $R$],
    #[$overline(R)=R slash P=$ residue class field of $R$],
    #[$Lambda=R$-algebra, f.g. as $R$-module],
    #[$frak(P)(Lambda)=$ set of f.g. projective left $Lambda$-modules],
    #[$hat(R)=$ $P$-adic completion of $R$,
      $hat(Lambda)=hat(R) times.o_R Lambda$],
  )
$ <eq:local-theory-standing-notation>

In most of the main results in §@sec:local-theory, the ring $R$ is assumed to be
a d.v.r. (discrete valuation ring), with prime element $pi$ and quotient field
$K$. However, we shall first give a review of basic material in the more general
setting @eq:local-theory-standing-notation, and then afterward shall restrict
our attention to the case where $R$ is a d.v.r.

#source(642)
In §§@sec:radicals–@sec:idempotents-krull-schmidt-projective-covers we have
already developed some of the basic machinery needed to study representations of
groups and orders over a local ring $R$. For convenience, we list here some of
the major earlier results. At the end of the listing, we shall give
cross-references to where these results are established in
§§@sec:radicals–@sec:idempotents-krull-schmidt-projective-covers. Most of the
results will be vital for this section, and were also used extensively in
§§@sec:brauer-characters–@sec:cartan-brauer-triangle of
Chapter~@ch:modular-representations.

#lemma(name: "Nakayama's Lemma")[
  Let $M$ be a f.g. $R$-module, with $R$ as in
  @eq:local-theory-standing-notation. Let $L$ be an $R$-submodule of $M$ such
  that $L+P M=M$. Then $L=M$.
] <lem:local-theory-nakayama>
#idx("Nakayama's Lemma", target: [@lem:local-theory-nakayama])

#proposition[
  We set $overline(Lambda)=Lambda slash P Lambda$, a f.d. $overline(R)$-algebra.
  Then
  #enum(
    numbering: "(i)",
    [$(rad Lambda)^k subset.eq P Lambda subset.eq rad Lambda$ for some $k>=1$.],
    [$Lambda slash rad Lambda tilde.equiv
      overline(Lambda) slash rad overline(Lambda)="semisimple artinian ring"$.],
    [$hat(Lambda) slash rad hat(Lambda) tilde.equiv Lambda slash rad Lambda$,
      $rad hat(Lambda)=hat(R) times.o_R rad Lambda$, and
      $rad Lambda=Lambda inter rad hat(Lambda)$.],
  )
] <prop:local-theory-radical-completion>

#theorem[
  Let $R$ be a complete local ring, and let $overline(Lambda)=Lambda slash N$,
  where $N$ is any two-sided ideal of $Lambda$ contained in $rad Lambda$. Then
  the following statements hold:
  #enum(
    numbering: "(i)",
    [Each decomposition $Lambda=plus.o.big_(i=1)^n Lambda e_i$ into
      indecomposable left ideals generated by idempotents ${e_i}$, yields a
      corresponding decomposition
      $overline(Lambda)=plus.o.big_(i=1)^n overline(Lambda) e_i$ into
      indecomposable left ideals. Conversely, every such decomposition of
      $overline(Lambda)$ arises in this way from a decomposition of $Lambda$.],
    [In (i), $Lambda e_i$ is the projective cover of $overline(Lambda) e_i$ for
      each $i$, and $Lambda e_i tilde.equiv Lambda e_j$ if and only if
      $overline(Lambda) e_i tilde.equiv overline(Lambda) e_j$.],
  )
] <th:local-theory-idempotent-decompositions>

#proposition[
  Let $R$ be a complete local ring, and let $M$ be a f.g. left $Lambda$-module.
  Then $M$ is indecomposable if and only if $End_Lambda M$ is a local ring.
] <prop:local-theory-indecomposable-endomorphism>

#theorem(name: "K-S-A Theorem", title: [Krull-Schmidt-Azumaya])[
  Let $R$ be a complete local ring, and let $M$ be a f.g. left $Lambda$-module.
  Then $M$ is expressible as a finite direct sum of indecomposable
  $Lambda$-modules, with the summands unique up to isomorphism and order of
  occurrence.
] <th:complete-local-krull-schmidt>
#idx(
  "Krull-Schmidt-Azumaya Theorem",
  target: [@th:complete-local-krull-schmidt],
)

#corollary[
  Keep the above hypotheses, and let $L$, $M$ and $N$ be f.g. left
  $Lambda$-modules. Then for each $k>=1$,
  $
    L^((k)) tilde.equiv M^((k)) ==> L tilde.equiv M,
    L plus.o M tilde.equiv L plus.o N ==> M tilde.equiv N.
  $
] <cor:complete-local-module-cancellation>

#proposition[
  For $M,N in frak(P)(Lambda)$, we have
  $ M tilde.equiv N <==> M slash P M tilde.equiv N slash P N. $
] <prop:local-projective-isomorphism-reduction>

#source(643)
#proposition[
  Let $R$ be a d.v.r. with prime element $pi$ and field of quotients $K$, and
  let $hat(R)$, $hat(K)$, etc., denote $P$-adic completions. Let $M$ be a f.g.
  $R$-module. Then:
  #enum(
    numbering: "(i)",
    [The map $M -> hat(M)$ is an embedding, and $M$ is dense in $hat(M)$ in the
      $P$-adic topology of $hat(M)$.],
    [$M slash P^k M tilde.equiv hat(M) slash P^k hat(M)$ for $k>=1$.],
    [For each $M in frak(P)(R)$ we have $M=K M inter hat(M)$, where we write
      $K M$ for $K times.o_R M$, after identifying $M$ with $1 times.o M$.],
    [Let $V$ be a $K$-space, $hat(V)$ its completion. There is a bijection
      $M <-> T$, given by
      $ M=V inter T, T=hat(M), $
      between the set of full $R$-lattices $M$ in $V$ and the set of full
      $hat(R)$-lattices $T$ in $hat(V)$.],
  )
] <prop:dvr-completion-module-lattice-correspondence>

#corollary[
  Let $R$ be a d.v.r. with quotient field $K$, and let $Lambda$ be an $R$-order
  in a f.d. $K$-algebra $A$. Let $M$ be a left $Lambda$-lattice, and let
  $hat(Lambda)$, $hat(M)$, etc., denote $P$-adic completions. Then:
  #enum(
    numbering: "(i)",
    [The map $M -> hat(M)$ embeds $M$ into the $hat(Lambda)$-lattice $hat(M)$,
      and $M=K M inter hat(M)$.],
    [Let $V$ be a f.g. $A$-module, $hat(V)=hat(K) times.o_K V$ its $P$-adic
      completion. There is a bijection $M <-> T$, given by
      $ M=V inter T, T=hat(M), $
      between the set of full $Lambda$-lattices $M$ in $V$ and the set of full
      $hat(Lambda)$-lattices $T$ in $hat(V)$.],
  )
] <cor:dvr-completion-order-lattice-correspondence>


_Cross-references._ For @lem:local-theory-nakayama, see @lem:nakayama. For
@prop:local-theory-radical-completion, see
@prop:finite-algebra-local-base-radical and Exercise~@exc:radical-completion.
For @th:local-theory-idempotent-decompositions, see
@th:complete-ring-idempotent-decompositions and
@rem:semiperfect-projective-cover-context(ii). Prop.
@prop:local-theory-indecomposable-endomorphism is given in
@prop:indecomposable-local-endomorphism-ring, and
@th:complete-local-krull-schmidt is deduced from it in
@th:krull-schmidt-azumaya. Cor. @cor:complete-local-module-cancellation follows
easily; see @cor:krull-schmidt-cancellation and
Exercise~@exc:krull-schmidt-power-cancellation. For
@prop:local-projective-isomorphism-reduction, see
@prop:projective-isomorphism-modulo-radical (or
@prop:projective-isomorphism-classes-quotient(iv)). Swan~@bib:Swan1960 gives a
special case of this result. Proposition
@prop:dvr-completion-module-lattice-correspondence is given in
@prop:localization-completion-lattices and §@ss:modules-dedekind-domains.
Finally, @cor:dvr-completion-order-lattice-correspondence is an immediate
consequence of @prop:dvr-completion-module-lattice-correspondence. See
§@sec:dedekind-domains for the definitions of “$Lambda$-lattice”, “full”, etc.
The result @cor:dvr-completion-order-lattice-correspondence was pointed out by
Heller~@bib:Heller1961a.

=== Reduction mod $P^k$ <ss:reduction-mod-prime-powers>

We now proceed toward the Maranda Theorems. As usual, the notation $M divides N$
means that $M$ is isomorphic to a direct summand of $N$. We begin with:

#theorem(title: [Reiner~@bib:Reiner1956])[
  Let $R$ be a d.v.r. with prime element $pi$, and let $Lambda$ be an $R$-order,
  and $M$ a f.g. left $Lambda$-lattice. Put $overline(R)=R slash P$,
  $overline(Lambda)=Lambda slash P Lambda$,
  #source(644)
  $overline(M)=M slash P M$. Then
  $
    M "is" Lambda "-projective" <==>
    overline(M) "is" overline(Lambda) "-projective".
  $
] <th:dvr-projectivity-reduction>
#idx("Reiner's Theorem", target: [@th:dvr-projectivity-reduction])
#proof[
  If $M divides Lambda^((k))$ then $overline(M) divides overline(Lambda)^((k))$;
  hence if $M$ is $Lambda$-projective, it is clear that $overline(M)$ is
  $overline(Lambda)$-projective. We give two proofs of the converse.

  (I) Assume $overline(M)$ is $overline(Lambda)$-projective, say
  $overline(M) divides overline(F)$, where $F=Lambda^((k))$. Consider the
  commutative diagram
  #projectivity-reduction-diagram()
  where $arrow.r^pi$ means multiplication by $pi$, and the map $overline(theta)$
  is surjective. The rows are exact, since $F$ and $M$ are $R$-torsionfree. Now
  $F$ is $Lambda$-free, so the surjection $overline(theta)$ lifts to a
  $Lambda$-homomorphism $theta:F -> M$. Then $theta(F)+pi M=M$, so $theta(F)=M$
  by Nakayama's Lemma~@lem:local-theory-nakayama. Let $N=ker theta$; then we
  obtain a commutative diagram
  #projectivity-kernel-diagram()
  in which $rho$ is the inclusion map, and the top row is exact. Since the top
  row is $R$-split, applying $overline(R) times.o_R *$ to it yields the
  exactness of the bottom row (see Exercise~@exc:quotient-tensor-module).

  Now $overline(M)$ is $overline(Lambda)$-projective, so we can find a map
  $psi:overline(F) -> overline(N)$ such that $psi overline(rho)=1$ on
  $overline(N)$. Lifting $psi$ to a $Lambda$-map $psi':F -> N$, we obtain a
  commutative diagram
  #projectivity-splitting-diagram()
  with $psi' rho in End_Lambda lr((N))$. Since $psi' rho equiv 1$ (mod $P$), it
  follows from Exercise~@exc:automorphism-modulo-maximal-ideal that
  $psi' rho in Aut_Lambda lr((N))$, whence the inclusion $rho$ is split by the
  map $(psi' rho)^(-1) psi'$. But then $M$ is a direct summand of $F$, so $M$ is
  $Lambda$-projective.

  #source(645)
  (II) Assume $overline(M)$ is $overline(Lambda)$-projective, say
  $overline(M) divides overline(Lambda)^((k))$. Since
  $ 0 -> Lambda arrow.r^pi Lambda -> overline(Lambda) -> 0 $
  is exact, we obtain
  $ op("Ext")_Lambda^2 lr((overline(Lambda),*))=0 $
  by §@ss:ext-tor, whence also $op("Ext")_Lambda^2 lr((overline(M),*))=0$ by
  @rem:ext-properties(iv). Now let $X$ be any f.g. left $Lambda$-module, so
  $op("Ext")_Lambda^1 lr((M,X))$ is f.g./$R$. From the $Lambda$-exact sequence
  $0 -> M arrow.r^pi M -> overline(M) -> 0$ we obtain an exact sequence
  $
    op("Ext")_Lambda^1 lr((M,X)) arrow.r^pi
    op("Ext")_Lambda^1 lr((M,X)) -> op("Ext")_Lambda^2 lr((overline(M),X))
  $
  (see @th:ext-long-exact-sequence). Thus, multiplication by $pi$ is a
  surjective endomorphism of the f.g. $R$-module $op("Ext")_Lambda^1 lr((M,X))$,
  so this module must equal $0$ by Nakayama's Lemma. In particular, consider a
  surjection $f:Lambda^((n)) -> M$, and set $X=ker f$. Then $X$ is
  f.g./$Lambda$, and the exact sequence
  $ 0 -> X -> Lambda^((n)) -> M -> 0 $
  is $Lambda$-split because $op("Ext")_Lambda^1 lr((M,X))=0$. Therefore
  $M divides Lambda^((n))$, so $M$ is projective as claimed.
]

Nakayama~@bib:Nakayama1957 (remarks at end of §3) proved the result for the
special case of group rings. There is also a proof via binding homomorphisms in
@bib:CurtisReiner1962[CR (77.1)]. For the case of group rings, the result also
follows from @prop:projective-reduction-summand-lifting.

The preceding result shows the close connection between a $Lambda$-lattice $M$
and the $overline(Lambda)$-module $overline(M)$, where bars denote reduction mod
$P$. We saw further (in @prop:local-projective-isomorphism-reduction) that for
$M,N in frak(P)(Lambda)$, $M tilde.equiv N$ if and only if
$overline(M) tilde.equiv overline(N)$. We shall now discuss the Maranda
Theorems, which establish analogous relations between $M$ and $M slash P^k M$,
even when $M$ is not $Lambda$-projective. For these theorems, it will be
necessary to restrict our attention to the case where $R$ is a discrete
valuation ring, and $Lambda$ is an $R$-order in a separable algebra. We fix the
following notation, to be used for the remainder of this subsection unless
otherwise specified:
$
  cases(
    #[$R=$ d.v.r. with prime element $pi$, $P=pi R$],
    #[$K=$ quotient field of $R$],
    #[$A=$ f.d. separable $K$-algebra],
    #[$Lambda=$ $R$-order in $A$],
    #[$hat(R),hat(K),hat(A),hat(Lambda)$, etc., denote $P$-adic completions],
  )
$ <eq:maranda-standing-notation>

#source(646)
The reader should keep in mind the case where $Lambda=R G$, $A=K G$, with $G$ a
finite group such that $char K divides.not |G|$. As shown in
@th:group-order-annihilates-bimodule-cohomology, we then have
$
  |G| dot op("Ext")_Lambda^1 lr((M,N))=0
  "for all" Lambda "-lattices" M "and" N.
$
For the general case where $A$ is any separable $K$-algebra, we proved in
@cor:uniform-order-ext-annihilator that there exists a nonzero ideal $frak(c)$
of $R$ such that
$
  frak(c) dot op("Ext")_Lambda^1 lr((M,N))=0
  "for all" Lambda "-lattices" M "and" N.
$
Indeed, by @th:order-contained-in-maximal-order the order $Lambda$ is contained
in some maximal $R$-order $Lambda'$ in $A$. We may then choose a nonzero
$alpha in R$ such that $alpha Lambda' subset.eq Lambda$, and then by
@th:central-conductor-ext-annihilator we obtain
$
  alpha dot op("Ext")_Lambda^1 lr((M,N))=0
  "for all" Lambda "-lattices" M "and" N.
$

The above discussion shows that under hypotheses @eq:maranda-standing-notation,
there exists a nonnegative integer $k_0$ such that
$
  pi^(k_0) op("Ext")_Lambda^1 lr((M,N))=0
  "for all" Lambda "-lattices" M "and" N.
$
<eq:maranda-extension-exponent>
Further, when $Lambda=R G$ we may choose $k_0$ so that $pi^(k_0) || |G|$ in $R$,
that is, $k_0$ is the largest $k$ such that $|G| in pi^k R$. In particular, we
pick $k_0=0$ whenever $|G|$ is a unit of $R$.

Keeping the above notation, we prove a result due to Maranda, as generalized by
D. G. Higman~@bib:Higman1960:

#theorem(title: [Maranda~@bib:Maranda1953])[
  Let $M$ and $N$ be $Lambda$-lattices, and let $k>=0$. Define
  $Lambda_k=Lambda slash pi^k Lambda$, $M_k=M slash pi^k M$, and so on; thus,
  $M_k$ is an $R_k$-free $Lambda_k$-module. Then:
  #enum(
    numbering: "(i)",
    [If $M tilde.equiv N$ as $Lambda$-modules, then $M_k tilde.equiv N_k$ as
      $Lambda_k$-modules for each $k>=0$.],
    [If $M_k tilde.equiv N_k$ for some $k>=k_0+1$, then $M tilde.equiv N$.],
  )
] <th:maranda-lattice-isomorphism>
#idx("Maranda's Theorem", target: [@th:maranda-lattice-isomorphism])
#proof[
  Assertion (i) is obvious. For (ii), let $k$ be fixed, $k>=k_0+1$, and assume
  that $phi:M_k tilde.equiv N_k$ is a $Lambda_k$-isomorphism. In the diagram
  #maranda-reduction-diagram()
  we can lift $phi$ to some $f in Hom_R lr((M,N))$, since $M$ is $R$-projective.
  Likewise, we can lift $phi^(-1)$ to some $g in Hom_R lr((N,M))$. Then
  $g f in End_R lr((M))$ is such that
  #source(647)
  $g f equiv 1$ mod $pi^k$, that is,
  $ (g f)(m)-m in pi^k M "for all" m in M. $

  Since $f$ lifts $phi$, we have
  $ (x f-f x)M subset.eq pi^k N "for all" x in Lambda. $
  We may therefore define a map $F_x in Hom_R lr((M,N))$ for each $x in Lambda$,
  by setting
  $ x f-f x=pi^k F_x, x in Lambda. $
  Each $F_x$ is well defined since $N$ is $R$-torsionfree. We obtain at once
  $ pi^k lr((F_(x y)-x F_y-F_x y))=0 "for all" x,y in Lambda, $
  and we may cancel the factor $pi^k$ since $Hom_R lr((M,N))$ is
  $R$-torsionfree. But then the map $F in Hom_R lr((Lambda,Hom_R lr((M,N))))$,
  defined by $x mapsto F_x$, $x in Lambda$, is a derivation from $Lambda$ into
  $Hom_R lr((M,N))$ (see §@sec:extensions-lattices). Thus $F$ determines an
  element of $op("Ext")_Lambda^1 lr((M,N))$. It follows from
  @eq:maranda-extension-exponent that $pi^(k_0) F$ is an inner derivation, that
  is, there exists an $h in Hom_R lr((M,N))$ such that
  $ pi^(k_0) F_x=x h-h x,x in Lambda. $
  Multiplying by $pi^(k_1)$, where $k_1=k-k_0>=1$, we obtain
  $ x f-f x=pi^(k_1)(x h-h x),x in Lambda. $
  Therefore $f-pi^(k_1) h$ commutes with each $x in Lambda$, and is thus an
  element of $Hom_Lambda lr((M,N))$. Since $f$ is an $R$-isomorphism of $M$ onto
  $N$, so is $f-pi^(k_1) h$ by Exercise~@exc:automorphism-modulo-maximal-ideal.
  Thus $f-pi^(k_1) h$ is a $Lambda$-isomorphism of $M$ onto $N$, and the theorem
  is proved.
]

#remarks[
  #enum(
    numbering: "(i)",
    [If one drops the hypothesis that $A$ be separable, one obtains the
      following modification of @th:maranda-lattice-isomorphism, due to
      Reiner~@bib:Reiner1979a:
      $ M_k tilde.equiv N_k "for each" k>=1 ==> M tilde.equiv N. $
      To prove this, consider the $R$-module $frak(D)$ of all derivations from
      $Lambda$ into $Hom_R lr((M,N))$; clearly $frak(D)$ is f.g./$R$. For each
      $k>=1$, let $phi_k$ be a $Lambda_k$-isomorphism of $M_k$ onto $N_k$. As in
      the preceding proof, we can find an $R$-isomorphism
      $theta_k:M tilde.equiv N$ such that
      $ (theta_k x-x theta_k)M subset.eq pi^k N "for all" x in Lambda. $
      #source(648)
      Set
      $ theta_k x-x theta_k=pi^k D_k lr((x)),x in Lambda,k>=1. $
      Then $D_k in frak(D)$ for each $k$.

      Now let $frak(D)_0$ be the $R$-submodule of $frak(D)$ generated by
      $D_1,D_2,...$. Since $frak(D)$ is f.g./$R$ and $R$ is noetherian, it
      follows that $frak(D)_0$ is also f.g./$R$. Hence there exists a positive
      integer $k$ such that
      $
        D_k=alpha_1 D_1+...+alpha_(k-1) D_(k-1)
        "for some" alpha_1,...,alpha_(k-1) in R.
      $
      Then
      $
        pi^(-k)(theta_k x-x theta_k)
        =sum_(i=1)^(k-1) alpha_i pi^(-i)(theta_i x-x theta_i)
        "for" x in Lambda.
      $
      Setting
      $ theta'=theta_k-sum_(i=1)^(k-1) alpha_i pi^(k-i) theta_i, $
      we obtain $theta' x=x theta'$ for all $x in Lambda$. Thus $theta'$ is a
      $Lambda$-homomorphism from $M$ into $N$. But $theta' equiv theta_k$ (mod
      $pi$), so $theta'$ is an $R$-isomorphism $M tilde.equiv N$ by
      Exercise~@exc:automorphism-modulo-maximal-ideal. Hence $M tilde.equiv N$
      as $Lambda$-modules, as claimed.],
    [Keep the hypotheses @eq:maranda-standing-notation, and assume further that
      the field $overline(R)$ is finite. Then for $k=k_0+1$, the ring $R_k$ is
      also finite, and so there are only a finite number of $Lambda_k$-modules
      of given $R_k$-rank. Hence by @th:maranda-lattice-isomorphism, we obtain
      the important result that there are only a finite number of isomorphism
      classes of $Lambda$-lattices of given $R$-rank. (See also
      @th:local-jordan-zassenhaus.)],
  )
] <rem:maranda-lattice-finiteness>

The following frequently used result is closely related to Maranda's Theorem:

#theorem[
  Let $R$ be a d.v.r. with quotient field $K$, and let bars denote reduction mod
  $pi$. Let $G$ be a finite group such that $|G|$ is invertible in $R$, and let
  $M$ and $N$ be $R G$-lattices. Then $M$ and $N$ are projective $R G$-lattices,
  and
  $
    K M tilde.equiv K N <==> M tilde.equiv N <==>
    overline(M) tilde.equiv overline(N).
  $
] <th:invertible-group-order-lattice-isomorphism>
#proof[
  The second equivalence follows from Maranda's Theorem, since by
  @th:group-order-annihilates-bimodule-cohomology we may choose $k_0=0$ in this
  case. However, it is not necessary to use Maranda's Theorem for the proof, and
  instead we may proceed as follows. The hypothesis implies that $overline(R) G$
  is a semisimple $overline(R)$-algebra. If $K M tilde.equiv K N$, then
  $overline(M)$ and $overline(N)$ have the same composition factors (see
  @prop:lattice-reduction-composition-factors), and therefore
  #source(649)
  $overline(M) tilde.equiv overline(N)$. Further, $overline(M)$ is
  $overline(R) G$-projective, whence $M$ is $R G$-projective by
  @th:dvr-projectivity-reduction. But then $overline(M) tilde.equiv overline(N)$
  implies $M tilde.equiv N$ by @prop:local-projective-isomorphism-reduction.
  This completes the proof. (See also Exercises @exc:prime-to-p-projective-lifts
  and @exc:invertible-group-order-projective-lattice.)
]

Returning to the general case, we establish a fundamental relation between
$Lambda$-modules and their completions:

#proposition[
  Let $R$ be a d.v.r. with prime element $pi$, and let $Lambda$ be any
  $R$-algebra, f.g./$R$ as module. Let $M$ and $N$ be f.g. left
  $Lambda$-modules, and let $hat(Lambda)$, $hat(M)$, etc., denote $P$-adic
  completions. Then
  $
    M tilde.equiv N "as" Lambda "-modules" <==>
    hat(M) tilde.equiv hat(N) "as" hat(Lambda) "-modules".
  $
] <prop:module-isomorphism-completion>
#proof[
  In the special case where $Lambda$ is an $R$-order in a separable $K$-algebra,
  and $M$, $N$ are $Lambda$-lattices, the result follows from Maranda's Theorem.
  Choose $k=k_0+1$, and use the fact (see
  @prop:dvr-completion-module-lattice-correspondence) that
  $ M slash P^k M tilde.equiv hat(M) slash P^k hat(M). $
  Then, applying Maranda's Theorem to both $Lambda$ and $hat(Lambda)$, we obtain
  $
    M tilde.equiv N <==> M slash P^k M tilde.equiv N slash P^k N
    <==> hat(M) slash P^k hat(M) tilde.equiv hat(N) slash P^k hat(N)
    <==> hat(M) tilde.equiv hat(N).
  $
  In the general case where $Lambda$ is an $R$-algebra, we have (by
  @th:change-of-rings)
  $
    hat(R) times.o_R Hom_Lambda lr((M,N)) tilde.equiv
    Hom_(hat(Lambda)) lr((hat(M),hat(N))),
  $
  and $Hom_Lambda lr((M,N))$ is dense in $Hom_(hat(Lambda)) lr((hat(M),hat(N)))$
  in the $P$-adic topology. Now let $f_1:hat(M) tilde.equiv hat(N)$ be a
  $hat(Lambda)$-isomorphism, and let $g_1=(f_1)^(-1)$. We may choose
  $f in Hom_Lambda lr((M,N))$ such that $f equiv f_1$ (mod $pi$), that is,
  $(f-f_1)(M) subset.eq pi hat(N)$. Likewise, we may choose
  $g in Hom_Lambda lr((N,M))$ with $g equiv g_1$ (mod $pi$). Then
  $g f in End_Lambda lr((M))$ satisfies $g f equiv 1$ (mod $pi$), so
  $ (g f)(m)-m in pi hat(M) "for all" m in M. $
  But $M inter pi hat(M)=pi M$ by
  @prop:dvr-completion-module-lattice-correspondence, whence $M=(g f)M+pi M$.
  Thus $g f in Aut_Lambda lr((M))$. Likewise $f g in Aut_Lambda lr((N))$, so
  $f:M tilde.equiv N$ as desired.
]

Let us continue our investigation of the connections between $Lambda$-modules
and $hat(Lambda)$-modules. We may ask whether indecomposable $Lambda$-lattices
yield indecomposable $hat(Lambda)$-lattices, and also whether every
$hat(Lambda)$-lattice is the completion of some $Lambda$-lattice. Simple
examples show that these questions may have a negative answer. For instance, let
$R$ be a d.v.r., and let $f(X) in R[X]$ be a monic irreducible polynomial, such
that in $hat(R)[X]$ there is a factorization $f(X)=product f_i lr((X))$ into at
least two distinct irreducible factors. Let
#source(650)
$Lambda=R[X] slash (f(X))$; then $Lambda$ is an $R$-order in the field
$K[X] slash (f(X))$, and
$
  hat(Lambda)=hat(R)[X] slash (f(X))=
  hat(R)[X] slash lr((product f_i lr((X)))).
$
However, the ring $hat(R)[X] slash (f_i lr((X)))$ is a $hat(Lambda)$-lattice
which is not the completion of any $Lambda$-lattice, as is clear from a
consideration of ranks. Furthermore, if we choose $f(X)$ so that for $i!=j$, the
ideal $(f_i lr((X)),f_j lr((X)))$ of $hat(R)[X]$ coincides with $hat(R)[X]$,
then
$ hat(Lambda) tilde.equiv product.co_i hat(R)[X] slash (f_i lr((X))). $
Thus, $hat(Lambda)$ is decomposable even though $Lambda$ is indecomposable.

There is, however, one important case where such behavior cannot occur. We shall
prove:

#theorem(title: [Heller~@bib:Heller1961a])[
  Let $R$ be a d.v.r. with quotient field $K$, and let $Lambda$ be an $R$-order
  in a semisimple $K$-algebra. Let $hat(Lambda)$, $hat(A)$, etc., denote
  $P$-adic completions. Suppose that for each simple left $A$-module $S$, the
  $hat(A)$-module $hat(S)$ is also simple#footnote[
    This hypothesis certainly holds whenever $K$ is a splitting field for $A$
    (see @def:splitting-field).
  ]. Then:
  #enum(
    numbering: "(i)",
    [Every $hat(Lambda)$-lattice is isomorphic to the completion of a
      $Lambda$-lattice.],
    [A $Lambda$-lattice $M$ is indecomposable if and only if its completion
      $hat(M)$ is indecomposable as $hat(Lambda)$-lattice.],
    [The K-S-A Theorem is valid for $Lambda$-lattices.],
  )
] <th:heller-completion-krull-schmidt>
#idx("Heller's Theorem", target: [@th:heller-completion-krull-schmidt])
#proof[
  Since $A=plus.o.big S_i$ is a direct sum of simple $A$-modules $S_i$, we have
  $hat(A)=plus.o.big hat(S)_i$, a direct sum of simple $hat(A)$-modules; thus
  $hat(A)$ is a semisimple $hat(K)$-algebra. Each f.g. left $hat(A)$-module is
  then isomorphic to a direct sum $product.co hat(S)_i^((n_i))$, hence is
  isomorphic to the completion of some $A$-module (namely
  $product.co S_i^((n_i))$).

  Now let $T$ be any left $hat(Lambda)$-lattice, and form the $hat(A)$-module
  $hat(K) T$. Then $hat(K) T tilde.equiv hat(K) V$ for some f.g. $A$-module $V$,
  where
  $ hat(K) T=hat(K) times.o_(hat(R)) T, hat(K) V=hat(K) times.o_K V. $
  Replacing $T$ by its isomorphic image in $hat(K) V$, we may assume that
  $hat(K) T=hat(K) V$, so $T$ is a full $hat(Lambda)$-lattice in $hat(K) V$. If
  we set $M=V inter T$, then by @cor:dvr-completion-order-lattice-correspondence
  $M$ is a full $Lambda$-lattice in $V$ such that $hat(M)=T$. Thus, the
  hypothesis implies that every $hat(Lambda)$-lattice is the completion of a
  $Lambda$-lattice.

  Suppose now that $M$ is an indecomposable $Lambda$-lattice, and that
  $hat(M)=T_1 plus.o T_2$, where the ${T_i}$ are nonzero $hat(Lambda)$-lattices.
  Then we may write $T_i=hat(M)_i$ for some $Lambda$-lattice $M_i$, $i=1,2$.
  Therefore $hat(M) tilde.equiv hat(M)_1 plus.o hat(M)_2$, whence
  $M tilde.equiv M_1 plus.o M_2$ by @prop:module-isomorphism-completion. This is
  a contradiction, and establishes (ii).

  #source(651)
  Finally, let $M$ be an arbitrary $Lambda$-lattice, and let $M=product.co M_i$
  with each $M_i$ indecomposable. Then $hat(M)=product.co hat(M)_i$ gives a
  decomposition of $hat(M)$ into indecomposable $hat(Lambda)$-lattices
  ${hat(M)_i}$. By the K-S-A Theorem, the ${hat(M)_i}$ are uniquely determined
  up to isomorphism and order of occurrence. Hence the same holds true for the
  ${M_i}$ by @prop:module-isomorphism-completion, and the theorem is proved.
]
#idx("Heller's Theorem")

Let us give an illustration of Heller's Theorem. Let $R$ be the localization of
$ZZ$ at the prime $p$, and let $G$ be a cyclic group of order $p^n$. Then (see
Exercise~@exc:rational-cyclic-group-wedderburn):
$
  QQ G tilde.equiv product.co_(r=0)^n K_r,
  "where" K_r=QQ[x] slash (Phi_(p^r)(x)),
$
and $Phi_(p^r)(x)$ is the cyclotomic polynomial of order $p^r$ and degree
$phi(p^r)$. If $hat(QQ)$ denotes the $p$-adic completion of $QQ$, then the proof
of @bib:CurtisReiner1962[CR (21.13)] shows that each $Phi_(p^r)(x)$ is
irreducible over $hat(QQ)$. Hence
$
  hat(QQ) G tilde.equiv product.co_(r=0)^n hat(QQ) times.o_QQ K_r,
  hat(QQ) times.o K_r=hat(QQ)[x] slash (Phi_(p^r)(x)),
$
so each simple $QQ G$-module $K_r$ yields a simple $hat(QQ) G$-module
$hat(K)_r$. By Heller's Theorem, we may conclude that every $hat(R) G$-lattice
is the completion of an $R G$-lattice, and that indecomposability is preserved
in passing to completions. Further, the K-S-A Theorem holds for $R G$-lattices.
For Jones' generalization of this result, and for further remarks about the
K-S-A Theorem, see §@sec:krull-schmidt-discrete-valuations, especially
@th:krull-schmidt-odd-p-group-lattices.

Let us return to the situation in @th:maranda-lattice-isomorphism where $Lambda$
is an $R$-order in a separable $K$-algebra. As we saw there, the isomorphism
class of $M$ is completely determined by the structure of $M$ mod $pi^(k_0+1)$.
There are two further results of this nature, valid when $R$ is assumed to be a
complete d.v.r. The first result is due to Maranda~@bib:Maranda1953; here, we
present Heller's~@bib:Heller1961a simplification and strengthening of the
result, as follows:

#theorem[
  Let $Lambda$ be an $R$-order in a separable $K$-algebra, where $R$ is a
  complete d.v.r. Let $k_0>=0$ be such that @eq:maranda-extension-exponent
  holds, and let $M$ be a $Lambda$-lattice such that $M slash pi^k M$ is
  decomposable for some $k>=k_0+1$. Then $M$ is also decomposable.
] <th:maranda-lattice-decomposability>
#idx("Maranda's Theorem", target: [@th:maranda-lattice-decomposability])
#proof[
  Put $M_k=M slash pi^k M$; since $M_k$ is decomposable, there exists a
  nontrivial idempotent $phi in End_Lambda M_k$. As in the proof of
  @th:maranda-lattice-isomorphism, we can find a map $f in End_Lambda M$ such
  that $f$ and $phi$ coincide mod $pi^(k_1)$, where $k_1=k-k_0>=1$. Then
  $ (f^2-f)M subset.eq pi^(k_1) M subset.eq pi M, $
  <eq:maranda-almost-idempotent>
  so we may write $f^2-f=pi f_1$ for some $f_1 in End_Lambda M$. Put
  $ E=End_Lambda M, overline(E)=E slash pi E, $
  <eq:maranda-endomorphism-reduction>
  #source(652)
  and let bars denote images mod $pi$. Then $overline(f)^2=overline(f)$ in
  $overline(E)$, and we claim that $overline(f)!=0,1$. Indeed, if
  $overline(f)=0$ then $f in pi E$, whence $f(M) subset.eq pi M$; this implies
  that $phi(M_k) subset.eq pi M_k$, and so
  $ phi(M_k)=phi^2(M_k)=phi^3(M_k)=...=0, $
  <eq:maranda-idempotent-not-nilpotent>
  a contradiction. Thus $overline(f)!=0$; a similar argument (using $1-phi$ in
  place of $phi$) shows that $overline(f)!=1$.

  We have thus obtained a non-trivial idempotent $overline(f) in overline(E)$.
  Since $R$ is complete by hypothesis, we can apply the Theorem on Lifting
  Idempotents~@th:lifting-idempotents to find a non-trivial idempotent in $E$
  which lifts $overline(f)$. But $E=End_Lambda lr((M))$, so $M$ must be
  decomposable, as claimed.
]

As in Remark~@rem:maranda-lattice-finiteness(i), we may drop the hypothesis that
$A$ be separable. We obtain (see Reiner~@bib:Reiner1979a): _Let $Lambda$ be any
$R$-order, where $R$ is a complete d.v.r., and let $M$ be a $Lambda$-lattice
such that $M slash pi^k M$ is decomposable (as
$(Lambda slash pi^k Lambda)$-module) for each $k>0$. Then $M$ is also
decomposable._

Maranda~@bib:Maranda1953 also established the following result (see
@bib:CurtisReiner1962[CR (76.11)] for a proof):

#theorem[
  Let $Lambda$ be an $R$-order in a separable $K$-algebra, where $R$ is a
  complete d.v.r., and let $k_0$ be as in @eq:maranda-extension-exponent. Let
  $k>2k_0$, and let $R_k=R slash pi^k R$, $Lambda_k=Lambda slash pi^k Lambda$
  and so on. Let $M$ be a $Lambda$-lattice such that $M_k$ contains a
  $Lambda_k$-sublattice $X$ which is an $R_k$-direct summand of $M_k$. Then $M$
  contains a $Lambda$-sublattice $L$ which is an $R$-direct summand of $M$, and
  is such that $L$ and $X$ are isomorphic mod $pi^(k-k_0)$.
] <th:maranda-sublattice-lifting>
#idx("Maranda's Theorem", target: [@th:maranda-sublattice-lifting])

The Maranda Theorems reduce the problem of studying $R$-representations of an
$R$-order $Lambda$ to the problem of studying the $R_k$-free $Lambda_k$-modules,
where $R_k=R slash pi^k R$ and $k$ is sufficiently large. Unfortunately, in many
cases this latter problem is at least as difficult as the original one. The case
$k=1$ leads to the subject of modular representation theory, which is of course
well developed. However, relatively little is known about the cases where $k>1$,
and so Maranda's Theorems have not turned out to be of great practical value in
the study of integral representations over a local ring. For a discussion of
known results when $k>1$, see §@ss:representations-mod-prime-powers.

#remarks(name: "Notes")[
  #enum(
    numbering: "(1)",
    [Let $R$ be a complete d.v.r. with prime element $pi$, and let $Lambda$,
      $Lambda'$ be $R$-orders in separable $K$-algebras. Then
      $Lambda tilde.equiv Lambda'$ as $R$-orders if and only if
      $
        Lambda slash pi^k Lambda tilde.equiv Lambda' slash pi^k Lambda'
        "as" R "-algebras"
      $
      for some sufficiently large value of $k$. This result, due to D. G.
      Higman~@bib:Higman1959, follows from the type of reasoning used to prove
      @prop:module-isomorphism-completion. For further results of this nature,
      see D. G. Higman~@bib:Higman1960.],
    [#source(653)
      A variant of Maranda's Theorem~@th:maranda-lattice-isomorphism is given in
      Nazarova-Roiter~@bib:Nazarova1967a.],
  )
] <rem:local-order-isomorphism-reduction-notes>

=== Extension of the Ground Ring <ss:extension-ground-ring-local-theory>

Suppose first that $R$ is an arbitrary Dedekind domain, contained in a larger
Dedekind domain $S$. Given an $R$-order $Lambda$, we may form the $S$-order
$S times.o_R Lambda$, which we write as $S Lambda$ after identifying $Lambda$
with its image $1 times.o Lambda$ in $S times.o_R Lambda$. Each $Lambda$-lattice
$M$ determines an $S Lambda$-lattice $S M$ ($=S times.o_R M$), whose isomorphism
type is uniquely determined by that of $M$, since an isomorphism
$f:M tilde.equiv N$ of $Lambda$-lattices induces an $S Lambda$-isomorphism
$1 times.o f:S times.o M tilde.equiv S times.o N$. We shall consider here the
converse question: does the isomorphism class of $S M$ determine that of $M$? We
shall also study the decomposition of $S M$ into indecomposable summands.

Let us begin with a simple example, where we choose $Lambda=R$. If $frak(a)$ and
$frak(b)$ are nonzero ideals in $R$, then $frak(a) tilde.equiv frak(b)$ as
$R$-modules if and only if $frak(a)$ and $frak(b)$ lie in the same ideal class
(see §@ss:ideal-class-groups-global-fields). Further,
$S times.o_R frak(a) tilde.equiv S frak(a)$, and
$S frak(a) tilde.equiv S frak(b)$ if and only if the $S$-ideals $S frak(a)$ and
$S frak(b)$ lie in the same ideal class of $S$. It may well happen that
$S frak(a)$ and $S frak(b)$ lie in the same class, even though $frak(a)$ and
$frak(b)$ do not. For example (see the proof of
@th:integral-form-principalizing-extension), we can choose $S$ so that _each_
ideal $frak(a)$ of $R$ generates a principal ideal $S frak(a)$ of $S$. Thus, the
isomorphism $S frak(a) tilde.equiv S frak(b)$ does not imply that
$frak(a) tilde.equiv frak(b)$, in general. Even when $R$ is a P.I.D., one can
give examples of an $R$-order $Lambda$, and $Lambda$-lattices $M$ and $N$, such
that (for suitable $S$) $S M tilde.equiv S N$ as $S Lambda$-lattices, but $M$ is
not $Lambda$-isomorphic to $N$ (see Berman-Gudivok~@bib:Berman1962,
Jacobinski~@bib:Jacobinski1968a).

This situation changes drastically when $R$ and $S$ are d.v.r.'s, which we shall
assume from now on. Specifically, let $R$ be the valuation ring of a discrete
valuation $v$ on $K$, let $P=pi R$ be the maximal ideal of $R$, and
$overline(R)$ its residue class field. Let $L$ denote an extension field of $K$,
where $dim_K L$ may possibly be infinite, and suppose that the valuation $v$ can
be extended to a discrete valuation $w$ on $L$. Let $S$ be its valuation ring,
$P_1$ the maximal ideal of $S$, and $overline(S)=S slash P_1$. We shall call the
d.v.r. $S$ an _extension_ of the d.v.r. $R$ in this case. Clearly
$ R=K inter S, P=R inter P_1, $
and $overline(S)$ is an extension field of $overline(R)$.

Our first result, due to Reiner-Zassenhaus~@bib:Reiner1961, is as follows:

#theorem[
  Let $R$ and $S$ be d.v.r.'s, with $S$ an extension of $R$. Let $M$ and $N$ be
  $Lambda$-lattices, where $Lambda$ is an $R$-order in a f.d. $K$-algebra $A$.
  Then $M tilde.equiv N$ if and only if
  $S times.o_R M tilde.equiv S times.o_R N$ as $(S times.o_R Lambda)$-lattices.
] <th:reiner-zassenhaus-local-extension-isomorphism>
#idx(
  "Reiner-Zassenhaus Theorem",
  target: [@th:reiner-zassenhaus-local-extension-isomorphism],
)
#proof[
  _Step 1._ Assume to begin with that $dim_K L$ is finite. The following
  argument is valid for the more general situation in which $Lambda$ is any
  $R$-algebra, f.g./$R$ as module, and where $M$ and $N$ are any f.g. left
  $Lambda$-modules (not necessarily lattices).

  #source(654)
  Put
  $ M_1=S times.o_R M, N_1=S times.o_R N, $
  and let $hat(R)$, $hat(M)$, $hat(Lambda)$ denote $P$-adic completions, and
  $hat(S)$, $hat(M)_1$, etc., $P_1$-adic completions. Then $hat(S)$ is a free
  $hat(R)$-module of finite rank, since $dim_K L$ is finite. Suppose that
  $hat(S)$ is $hat(R)$-free on $n$ generators. We have
  $
    hat(M)_1=hat(S) times.o_S M_1 tilde.equiv hat(S) times.o_R M
    tilde.equiv hat(S) times.o_(hat(R))(hat(R) times.o_R M)
    tilde.equiv hat(S) times.o_(hat(R)) hat(M),
  $
  so $hat(M)_1 tilde.equiv hat(M)^((n))$ as left $hat(Lambda)$-modules. If
  $M_1 tilde.equiv N_1$, then $hat(M)_1 tilde.equiv hat(N)_1$, and so
  $hat(M)^((n)) tilde.equiv hat(N)^((n))$ as $hat(Lambda)$-modules. Therefore
  $hat(M) tilde.equiv hat(N)$ by @cor:complete-local-module-cancellation, so
  $M tilde.equiv N$ by @prop:module-isomorphism-completion, and we have shown
  that $M tilde.equiv N$ if and only if $M_1 tilde.equiv N_1$.

  _Step 2._ Assume now that $M$ and $N$ are $Lambda$-lattices, where $Lambda$ is
  an $R$-order, and set $overline(R)=R slash P$, $overline(S)=S slash P_1$, so
  $overline(S)$ is an extension field of $overline(R)$. We shall imitate the
  proof of the Noether-Deuring Theorem given in Exercises
  @exc:isomorphism-determinant-polynomial–@exc:noether-deuring. We may write
  $S M$ for $S times.o_R M$, after the usual identification of $M$ with
  $1 times.o M$. If we assume that $S M tilde.equiv S N$, then $M$ and $N$ have
  the same $R$-rank, which we denote by $n$. Each element of $Hom_R lr((M,N))$
  can then be represented by an $n times n$ matrix over $R$. Let
  $bold(upright(X))_1,...,bold(upright(X))_r$ be an $R$-basis for
  $Hom_Lambda lr((M,N))$. Since
  $
    S times.o_R Hom_Lambda lr((M,N)) tilde.equiv
    Hom_(S Lambda) lr((S M,S N)),
  $
  the matrices ${bold(upright(X))_i}$ are also an $S$-basis for
  $Hom_(S Lambda) lr((S M,S N))$. Define
  $
    f(t_1,...,t_r)=det(t_1 bold(upright(X))_1+...+t_r bold(upright(X))_r)
    in R[t_1,...,t_r],
  $
  as in Exercise~@exc:isomorphism-determinant-polynomial. Since
  $S M tilde.equiv S N$, there exist elements $alpha_i in S$ with
  $f(alpha_1,...,alpha_r)$ a unit in $S$. Let $overline(f)$ be the polynomial
  obtained from $f$ by reducing each coefficient mod $P$. If $alpha_i in S$ maps
  onto $overline(alpha)_i in overline(S)$, the above discussion shows that
  $ overline(f)(overline(alpha)_1,...,overline(alpha)_r)!=0, $
  and therefore $overline(f)$ is not the zero polynomial in
  $overline(R)[t_1,...,t_r]$. Clearly $overline(f)$ has degree at most $n$.

  If $"card" overline(R)>n$, there exist elements $beta_1,...,beta_r in R$ such
  that $overline(f)(overline(beta)_1,...,overline(beta)_r)!=0$, and then
  $sum beta_i bold(upright(X))_i$ is the desired $Lambda$-isomorphism of $M$
  onto $N$. On the other hand, if $"card" overline(R)<=n$ we may choose a finite
  extension field $K'$ of $K$, with a valuation ring $R'$ containing $R$, such
  that the residue class field of $R'$ has more than $n$ elements (see
  Weiss~@bib:Weiss1963, Prop. 3-2-12 or @bib:Reiner1975[MO (5.8)], for the case
  where $R$ is a complete d.v.r.; for the general case, use the fact that
  passage to completions does not affect residue class fields). We can then find
  elements $gamma_i in R'$ for which $f(gamma_1,...,gamma_r)$ is a unit in $R'$,
  and therefore $R' M tilde.equiv R' N$ as $R' Lambda$-lattices. But then
  $M tilde.equiv N$ as $Lambda$-lattices by Step 1, completing the proof.
]

#source(655)
For the remainder of this subsection, we shall assume that $R$ and $S$ are
complete d.v.r.'s, with $S$ an extension of $R$. For each $R$-module $M$, the
map $M -> S times.o_R M$ is an embedding (see
Exercise~@exc:dedekind-extension-tensor-injective), and we always identify $M$
with $1 times.o M$, so $S times.o_R M$ may be written as $S M$. Now let $Lambda$
be any $R$-algebra, f.g./$R$ as module, and let $M$ be a f.g. left
$Lambda$-module. We wish to study the decomposition of the $S Lambda$-module
$S M$ into a direct sum of indecomposable submodules. The entire discussion
depends on the relationship given in @prop:morita-summand-equivalence between
decompositions of a module and decompositions of its endomorphism ring. We
follow the treatment in Reiner~@bib:Reiner1966.

Given the f.g. left $Lambda$-module $M$, set
$ E=E(M)=End_Lambda M, tilde(E)=tilde(E)(M)=E(M) slash rad E(M). $
<eq:local-extension-endomorphism-quotient>
Then $E$ is an $R$-algebra, f.g./$R$ as module, and $tilde(E)$ is a f.d.
semisimple $overline(R)$-algebra, by @prop:finite-algebra-local-base-radical.
View $M$ as a bimodule $attach(M, bl: Lambda, br: E)$, with $E$ acting on the
right. By @prop:morita-summand-equivalence, each decomposition
$M=plus.o.big M_i$ into indecomposable submodules gives rise to a decomposition
$E=plus.o.big L_i$ into indecomposable left ideals. If $pi_i:M -> M_i$ is the
idempotent in $E$ given by the projection of $M$ onto its $i$-th summand $M_i$,
then again by @prop:morita-summand-equivalence we have (for each $i$)
$ M_i=M pi_i=M L_i,L_i=E pi_i, $
$ End_Lambda M_i tilde.equiv End_E L_i tilde.equiv pi_i E pi_i. $
Further, $M_i tilde.equiv M_j$ if and only if $L_i tilde.equiv L_j$.

On the other hand, let $J$ be any two-sided ideal of $E$ contained in $rad E$,
and let $E'=E slash J$, $L'_i=$ image of $L_i$ in $E'$. By
@prop:projective-isomorphism-classes-quotient the decomposition
$E=plus.o.big L_i$ corresponds to a decomposition $E'=plus.o.big L'_i$ into
indecomposable left ideals $L'_i$ of $E'$, with $L_i tilde.equiv L_j$ if and
only if $L'_i tilde.equiv L'_j$. Further, since
$ E slash rad E tilde.equiv E' slash rad E', $
it follows readily from @prop:radical-idempotent-corner that for each $i$,
$ tilde(E)(L_i) tilde.equiv tilde(E)(L'_i), $
where $tilde(E)(L_i)=End_E lr((L_i)) slash rad End_E lr((L_i))$, and
$tilde(E)(L'_i)$ is defined analogously. We shall apply this machinery to the
$S Lambda$-module $S M$, rather than to $M$ itself, in order to prove the
following basic result:

#theorem[
  Let $R$ and $S$ be complete d.v.r.'s, with $S$ an extension of $R$, and let
  $Lambda$ be an $R$-algebra, f.g./$R$ as module. For each f.g. left
  $Lambda$-module $M$, define $tilde(E)(M)$ by
  @eq:local-extension-endomorphism-quotient, and form the $overline(S)$-algebra
  $ overline(S) times.o_(overline(R)) tilde(E)(M). $
  #source(656)
  Then:
  #enum(
    numbering: "(i)",
    [Each decomposition of the $S Lambda$-module $S M=plus.o.big N_j$ as a
      direct sum of indecomposable submodules corresponds to a decomposition
      $ overline(S) times.o_(overline(R)) tilde(E)(M)=plus.o.big L_j $
      into indecomposable left ideals.],
    [Further, $N_i tilde.equiv N_j$ if and only if $L_i tilde.equiv L_j$. For
      each $j$, we have
      $ tilde(E)(N_j) tilde.equiv tilde(E)(L_j). $],
    [In particular, if $tilde(E)(M) tilde.equiv overline(R)$ then $S M$ is
      indecomposable for every $S$, and
      $tilde(E)(S M) tilde.equiv overline(S)$.],
  )
] <th:local-extension-indecomposable-endomorphism-correspondence>
#proof[
  We have
  $ E(S M)=End_(S Lambda) lr((S M)) tilde.equiv S times.o_R E(M) $
  by @th:change-of-rings. We choose
  $ J=P_1 E(S M)+S times.o rad E, "where" E=E(M). $
  Then $J$ is a two-sided ideal of $E(S M)$ contained in $rad E(S M)$, so
  $E(S M)$ decomposes into indecomposable left ideals in the same way as the
  factor ring $E(S M) slash J$. But
  $
    E(S M) slash J tilde.equiv (S times.o_R E(M)) slash J
    tilde.equiv overline(S) times.o_(overline(R)) tilde(E)(M).
  $
  Assertions (i)–(iii) are then immediate consequences of the discussion
  preceding the theorem.
]

In @prop:indecomposable-local-endomorphism-ring we showed that the
$Lambda$-module $M$ is indecomposable if and only if $E(M)$ is a local ring, or
equivalently, if and only if $tilde(E)(M)$ is a division algebra over
$overline(R)$. We have just seen that if $M$ is an indecomposable
$Lambda$-module for which $tilde(E)(M)=overline(R)$, then $M$ remains
indecomposable under ground ring extension; that is, $S times.o_R M$ is an
indecomposable $(S times.o_R Lambda)$-module for each complete d.v.r. $S$ which
is an extension of $R$. Let us make the following definition:

#definition[
  Let $R$ be a complete d.v.r., and let $Lambda$ be any $R$-algebra, f.g./$R$ as
  module. An indecomposable f.g. left $Lambda$-module $M$ is called _absolutely
  indecomposable_ if $S M$ is an indecomposable $S Lambda$-module, for each
  complete d.v.r. $S$ which is an extension of $R$.
] <def:absolutely-indecomposable-local-module>
#idx(
  "absolutely indecomposable",
  target: [@def:absolutely-indecomposable-local-module],
)

#source(657)
We have thus shown that $M$ is absolutely indecomposable whenever
$tilde(E)(M) tilde.equiv overline(R)$. The reader should compare this fact with
@th:absolute-simplicity-centralizer, which is in fact a special case of the
theorem above. It may well happen, however, that $M$ is absolutely
indecomposable even when $tilde(E)(M)!=overline(R)$. This phenomenon is related
to questions of inseparability (see @th:absolute-indecomposability-inseparable
below), and to bypass this difficulty let us restrict our attention to the case
where the field $overline(R)$ is perfect. (This is the situation which arises
most frequently in practice, since $overline(R)$ is usually a finite field. See
§@ss:green-indecomposability, for example, where these results are used to prove
indecomposability of induced modules in certain situations.)

We are now ready to prove:

#theorem[
  Let $overline(R)$ be a perfect field, and let $M$ be a f.g. indecomposable
  $Lambda$-module. Then $M$ is absolutely indecomposable if and only if
  $tilde(E)(M) tilde.equiv overline(R)$.
] <th:absolute-indecomposability-residue-endomorphism>
#idx(
  "Reiner's Theorem",
  target: [@th:absolute-indecomposability-residue-endomorphism],
)
#proof[
  We need only show that if $tilde(E)(M)!=overline(R)$, then $S M$ is
  decomposable for some choice of $S$. Now $tilde(E)(M)$ is a division algebra
  whose center contains $overline(R)$, and thus $tilde(E)(M)$ is a separable
  $overline(R)$-algebra, because $overline(R)$ is perfect (see
  §@ss:separable-algebras-modules). We can therefore find a finite extension
  field $F$ of $overline(R)$ such that $F times.o_(overline(R)) tilde(E)(M)$ is
  a split semisimple $F$-algebra, by @lem:separable-split-extension. But any
  such algebra has a nontrivial decomposition into simple left ideals, except
  when the algebra coincides with $F$ itself. This latter case cannot arise
  because $tilde(E)(M) supset overline(R)$. Thus, as soon as we can find a
  complete d.v.r. $S$ for which $overline(S)=F$, then $S M$ is decomposable (by
  @th:local-extension-indecomposable-endomorphism-correspondence), and the
  theorem is proved.

  To complete the proof, we need only make use of the following result, which
  holds whether or not $overline(R)$ is perfect:
]

#proposition[
  Let $R$ be a complete d.v.r. with quotient field $K$ and residue class field
  $overline(R)$, and let $K'$ be an algebraic closure of $K$. Then there is a
  one-to-one inclusion-preserving correspondence $L <-> F$ between the set of
  fields $L$ such that
  $ K subset.eq L subset.eq K', L="finite unramified extension of" K, $
  and the set of fields $F$ which are finite separable over $overline(R)$. If
  $S$ is the valuation ring in $L$ obtained by extending the valuation from $K$
  to $L$, then $S$ is a complete d.v.r. and the residue class field of $S$
  equals $F$.
] <prop:unramified-extension-residue-correspondence>

For a proof, see Weiss~@bib:Weiss1963, Th. 3-2-11 or Serre~@bib:Serre1962, Ch.
III, §5. If $pi$ denotes a prime element of $R$, then the condition that $L$ be
unramified over $K$ means that $pi$ is also a prime element of $S$, and that
$overline(S)$ is separable over $overline(R)$ (this latter condition holds
automatically when $overline(R)$ is perfect). For further discussion of
ramification, see §@ss:dedekind-ideal-theory.

Let us record an important consequence of the above reasoning, already used in
§@sec:vertices-sources.

#source(658)
#corollary[
  Let $overline(R)$ be a perfect field, and let $M$ be any f.g. left
  $Lambda$-module. Then there exists a complete d.v.r. $S$, whose quotient field
  $L$ is a finite unramified extension of $K$, such that $S M=plus.o.big N_i$,
  where each $N_i$ is an absolutely indecomposable $S Lambda$-module, and where
  $tilde(E)(N_i) tilde.equiv overline(S)$ for each $i$.
] <cor:absolute-indecomposable-unramified-extension>
#proof[
  The $overline(R)$-algebra $tilde(E)(M)$ is separable over $overline(R)$, so by
  @lem:separable-split-extension and
  @prop:unramified-extension-residue-correspondence we can find $S$, as in the
  statement of @cor:absolute-indecomposable-unramified-extension, for which
  $overline(S) times.o_(overline(R)) tilde(E)(M)$ is a split semisimple
  $overline(S)$-algebra. This algebra is then a direct sum of absolutely simple
  left ideals ${L_i}$, and we have
  $tilde(E)(L_i)=E(L_i) tilde.equiv overline(S)$. By
  @th:local-extension-indecomposable-endomorphism-correspondence, there is a
  corresponding decomposition $S M=plus.o.big N_i$ into indecomposable
  $S Lambda$-modules, with $tilde(E)(N_i) tilde.equiv tilde(E)(L_i)$. Each $N_i$
  is absolutely indecomposable as $S Lambda$-module, by
  @th:absolute-indecomposability-residue-endomorphism, and the proof is
  complete.
]

It is often convenient to find a complete d.v.r. $S$ such that for _every_ f.g.
indecomposable $Lambda$-module $M$, the $S Lambda$-module $S M$ splits into a
direct sum of absolutely indecomposable submodules. Given an $M$, we can always
choose an $S$ depending on $M$ by
@cor:absolute-indecomposable-unramified-extension. The following discussion is
an adaptation of the results given in
@prop:unramified-extension-residue-correspondence. Let $R$ be a complete d.v.r.
with perfect residue class field $overline(R)$, and let $Omega$ denote the
algebraic closure of $overline(R)$, and $K'$ an algebraic closure of $K$. By
@prop:unramified-extension-residue-correspondence, each finite extension $F$ of
$overline(R)$ in $Omega$ is the residue class field $overline(S)$ of a d.v.r.
$S$ in some finite unramified extension $L$ of $K$ in $K'$. Let $K_0$ be the
union of all of these $L$'s. The $P$-adic valuation $v$ on $K$ extends uniquely
to $K_0$ (and indeed to $K'$), and the valuation ring $R_0$ of $K_0$ is then a
d.v.r. with prime element $pi$, where $P=pi R$. The residue class field
$overline(R)_0=R_0 slash pi R_0$ is the union of all of the fields $F$, and
coincides with $Omega$. (The field $K_0$ is called the _maximal unramified
extension_ of $K$.) Then $K_0$ is algebraic over $K$, and each subfield $L$ of
$K_0$ finite over $K$ is an unramified extension of $K$. If the residue class
field $overline(R)$ is finite, then $K_0$ can be obtained from $K$ by adjoining
all $m$-th roots of unity, where $m$ ranges over all integers not divisible by
$char overline(R)$.

It may occur, however, that the d.v.r. $R_0$ is not complete, and usually
$dim_K K_0=infinity$. Let $S_0$ denote the $pi$-adic completion of $R_0$, and
$L_0$ the quotient field of $S_0$. Then $S_0$ is a complete d.v.r. for which
$
  overline(S)_0=S_0 slash pi S_0 tilde.equiv R_0 slash pi R_0 tilde.equiv Omega,
$
and $S_0$ is an extension of the d.v.r. $R$. Of course, $S_0$ need not be a f.g.
$R$-module.

We are now ready to prove

#proposition[
  Let $overline(R)$ be perfect, and let $S_0$ be the complete d.v.r. defined
  above. Then for each f.g. indecomposable $Lambda$-module $M$, the
  $S_0 Lambda$-module $S_0 M$ is a direct sum of absolutely indecomposable
  submodules.
] <prop:universal-unramified-absolute-decomposition>
#proof[
  For each $M$, choose $S$ as in
  @cor:absolute-indecomposable-unramified-extension so that $S M$ is a direct
  sum of absolutely indecomposable $S Lambda$-modules. Since $S_0$ contains $S$,
  the result is
  #source(659)
  clear from the identifications
  $ S_0 Lambda tilde.equiv S_0(S Lambda), S_0 M tilde.equiv S_0(S M). $
]

The results so far obtained may be viewed as generalizations of the theorems in
§@sec:separable-algebras-splitting-fields concerning the behavior of modules
under ground field extensions. Indeed, many of the proofs in
§@sec:separable-algebras-splitting-fields can be obtained from those given here,
by choosing $R=overline(R)=K$, $S=overline(S)=L$, in the proofs in this section.
In particular, our earlier result @cor:group-algebra-multiplicity-free-extension
has the following interesting analogue in integral representation theory:

#theorem(title: [Reiner~@bib:Reiner1966])[
  Let $R$ and $S$ be complete d.v.r.'s, with $S$ an extension of $R$, and
  suppose that $overline(R)$ is a finite field. Then for each indecomposable
  f.g. $Lambda$-module $M$, the $S Lambda$-module $S M$ is a direct sum of
  non-isomorphic indecomposable submodules.
] <th:finite-residue-extension-multiplicity-free>
#idx(
  "Reiner's Theorem",
  target: [@th:finite-residue-extension-multiplicity-free],
)
#proof[
  Since $M$ is indecomposable, $tilde(E)(M)$ must be a division algebra over
  $overline(R)$. Since $overline(R)$ is finite, so is $tilde(E)(M)$, and
  therefore $tilde(E)(M)$ is a field by Wedderburn's Theorem (see
  @bib:CurtisReiner1962[CR (68.9)]). Then
  $overline(S) times.o_(overline(R)) tilde(E)(M)$ is a commutative algebra, and
  is semisimple by @cor:separable-extension-semisimplicity. It is therefore a
  direct sum of fields, no two of which are isomorphic as ideals of
  $overline(S) times.o tilde(E)(M)$. The desired result now follows from
  @th:local-extension-indecomposable-endomorphism-correspondence.
]

In case $overline(R)$ is not assumed perfect, we have the following result (see
Reiner~@bib:Reiner1966 for proof):

#theorem[
  Let $M$ be any f.g. left $Lambda$-module. Then $M$ is absolutely
  indecomposable if and only if $tilde(E)(M)$ is a field which is purely
  inseparable over $overline(R)$.
] <th:absolute-indecomposability-inseparable>

For further results concerning behavior of modules under ground ring extensions,
see Bialnicki-Birula~@bib:BialnickiBirula1970, Roggenkamp~@bib:Roggenkamp1972,
Huppert~@bib:Huppert1975.

=== Representations mod $P^k$ <ss:representations-mod-prime-powers>

Let $Lambda$ be an $R$-order in a $K$-algebra $A$, where for the moment $R$ is
an arbitrary Dedekind domain. Given a nonzero ideal $frak(a)=product P^(e(P))$
in $R$, we wish to consider representations of $Lambda$ by matrices with entries
in the residue class ring $R slash frak(a)$. This is equivalent to studying f.g.
$Lambda$-modules which are free as $(R slash frak(a))$-modules. For each such
module $M$, we may decompose $M$ into its $P$-primary parts ${M_P}$ with $P$
ranging over the prime ideal divisors of $frak(a)$. Thus, the problem of
classifying $M$ reduces to the case in which $frak(a)$ is a power of a prime
ideal. (Of course, if each $M_P$ is known, then we can find an
$(R slash frak(a))$-free module $M$ with prescribed $P$-primary parts ${M_P}$,
provided that the number of elements in a free $(R slash P^(e(P)))$-basis of
$M_P$ is independent of $P$.)

#source(660)
Further, in finding representations of $Lambda$ over $R slash P^e$, there is no
harm in replacing $R$ by its localizations $R_P$, since this does not affect the
residue class ring. Changing notation, we may now assume that $R$ is a d.v.r.
with maximal ideal $P$. For $k>=1$, set
$ R_k=R slash P^k,Lambda_k=Lambda slash P^k Lambda. $

By a $Lambda_k$-lattice we mean a f.g. left $Lambda_k$-module which is
$R_k$-free. Every exact sequence of $Lambda_k$-lattices is split over $R_k$.
Further, the ring $R_k$ is self-injective (see
Exercise~@exc:pid-quotient-self-injective), so every $Lambda_k$-lattice is
injective as $R_k$-module. It follows that if $N subset.eq M$ are
$Lambda_k$-lattices, then so is $M slash N$. We note also that any direct
summand of a $Lambda_k$-lattice is $R_k$-projective, hence $R_k$-free since
$R_k$ is local. Thus, direct summands of $Lambda_k$-lattices are again
$Lambda_k$-lattices.

Suppose now that $Lambda=R G$, where $G$ is a finite group of order $n$, with
$n$ a unit in $R$. Then every exact sequence of $Lambda_k$-lattices
$ 0 -> L -> M -> N -> 0 $
is $Lambda_k$-split, since it is $R_k$-split, and we can mimic the proof of
Maschke's Theorem. Therefore every $Lambda_k$-lattice is $Lambda_k$-projective.
It follows from @th:local-theory-idempotent-decompositions and
@prop:local-projective-isomorphism-reduction that the correspondence
$M mapsto overline(M)=M slash P M$ gives an isomorphism-preserving bijection
between the set of $Lambda_k$-lattices $M$ and the set of f.g. projective
$overline(Lambda)$-modules $overline(M)$, where
$overline(Lambda)=Lambda slash P Lambda$. Further, since the K-S-A Theorem holds
for $Lambda_k$-lattices, each such lattice is uniquely a direct sum of copies of
lattices ${M_1,...,M_r}$, where these are a full set of non-isomorphic
indecomposable projective $Lambda_k$-lattices.

The case where $n in P$ is much more interesting and difficult, assuming that
$k>1$. (The case $k=1$ is the usual one of finding modular representations of
$G$.) We shall describe the results of
Drobotenko-Drobotenko-Zhilinskaya-Pogorilyak~@bib:Drobotenko1965, as simplified
by Hannula~@bib:Hannula1968, which deal with the case in which $G$ is cyclic of
prime order $p$. Here, $R$ may be any d.v.r. in which $p$ is a prime element.
Let $k>1$, and assume $p$ odd for simplicity. Given a $Lambda_k$-lattice $M$,
put $overline(M)=M slash p M$, viewed as a $overline(Lambda)$-module. Let
$ S_i=overline(R)[lambda] slash (lambda^i),1<=i<=p, $
where $lambda=1-x$, and $x$ is a generator of $G$. These ${S_i}$ give all of the
indecomposable $overline(Lambda)$-modules, and $overline(M)$ is a direct sum of
copies of these ${S_i}$. Let us show at once that $overline(M)$ is a sum of
types $S_1$, $S_(p-1)$ and $S_p$, and no others. Indeed suppose $p>3$ and
$S_t divides overline(M)$, where $2<=t<=p-2$. Choose $m in M$ so that
$
  {overline(m),lambda overline(m),...,lambda^(t-1) overline(m)}
  =overline(R) "-basis of" S_t.
$
Then ${m,lambda m,...,lambda^(t-1) m}$ is part of an $R_k$-basis for $M$ (see
Exercise~@exc:projective-local-free). We
#source(661)
have $lambda overline(m) in.not lambda^2 overline(M)$. But
$ lambda^p m=lambda^2 dot lambda^(p-2) m in p lambda^2 M $
since $t<=p-2$. Then
$
  0=(x^p-1)m=((1-lambda)^p-1)m
  =(-lambda^p+p lambda^(p-1)-...-p lambda)m,
$
which implies that $p lambda m in p lambda^2 M$, and therefore (since $k>1$)
$lambda overline(m) in lambda^2 overline(M)$, a contradiction.

If $overline(M)$ is a sum of copies of $S_i$, we say $M$ has _type i_. If $M$
has type $p$, then $overline(M) tilde.equiv overline(Lambda)^((n))$ for some
$n$, so $overline(M)$ is $overline(Lambda)$-projective. As in
@th:dvr-projectivity-reduction it follows that $M$ is $Lambda_k$-projective, and
indeed $M tilde.equiv Lambda_k^((n))$.

Now let $M$ be any $Lambda_k$-lattice, and let $S_p divides overline(M)$; then
$M$ contains the $Lambda_k$-lattice $N$ as direct summand, where
$
  N=plus.o.big_(i=0)^(p-1) R_k lambda^i m,
  "and" S_p=overline(Lambda) overline(m).
$
Thus $N tilde.equiv Lambda_k$; but then the exact sequence of
$Lambda_k$-lattices
$ 0 -> N -> M -> M slash N -> 0 $
is $R_k$-split, hence also $Lambda_k$-split. (To see this, let
$M^*=Hom_(R_k) lr((M,R_k))$ be the contragredient of $M$. Then
$M^(**) tilde.equiv M$, and also $Lambda_k^* tilde.equiv Lambda_k$. The sequence
$ 0 -> (M slash N)^* -> M^* -> N^* -> 0 $
is then $Lambda_k$-split, whence so is the original one, by taking
contragredients once more. See Exercise~@exc:contragredient-exact-split.) We
therefore have a $Lambda_k$-decomposition
$ M=M' plus.o M'', $
where $M'$ is $Lambda_k$-free, and $overline(M)''$ is a sum of copies of $S_1$
and $S_(p-1)$. A computation involving successive basis changes then shows that
$ M''=M_1 plus.o M_(p-1),M_i=Lambda_k "-module of type" i,i=1,p-1. $
(We omit the details.)

The structure of the $Lambda_k$-lattice $M_1$ is easily described. We have
$lambda M_1 subset.eq p^(k-1) M_1$.#ed-note[
  The printed minimum does not give the required valuation: the minimum
  nonnegative exponent is zero, and the zero operator has no largest finite
  valuation.
] Indeed, let $bold(upright(T))$ be the matrix of $lambda=1-x$. If
$bold(upright(T))=0$, the inclusion is immediate. Otherwise write
$bold(upright(T))=p^t bold(upright(U))$, where $1<=t<=k-1$ and
$bold(upright(U))$ has a unit entry. If $t<=k-2$, the defining relation gives
$
  0=(bold(upright(I))-bold(upright(T)))^p-bold(upright(I))
  =p^(t+1) bold(upright(U)) bold(upright(B)),
$
where $bold(upright(B)) equiv -bold(upright(I)) mod p$ and hence
$bold(upright(B))$ is invertible. Thus $p^(t+1) bold(upright(U))=0$. Since $M_1$
is free over $R_k$ and $t+1<k$, every entry of $bold(upright(U))$ lies in
$p^(k-t-1) R_k$, contradicting its unit entry. Therefore $t=k-1$, proving the
inclusion. Thus, $M_1$ affords a matrix representation
$ x mapsto bold(upright(I))+p^(k-1) bold(upright(B)), $
where $bold(upright(B))$ may be viewed as a matrix over $overline(R)$. The
isomorphism class of $M_1$
#source(662)
determines the similarity class of $bold(upright(B))$ over $overline(R)$, and
conversely. The indecomposable $M_1$'s thus correspond to matrices
$bold(upright(B))$ which are companion matrices of polynomials $f(X)^e$, with
$f(X)$ irreducible in $overline(R)[X]$ and $e>=1$.

Finally, the $Lambda_k$-lattices $M_(p-1)$ of type $p-1$ can be classified as
follows. The augmentation ideal of the group ring $Lambda_k$ is
$lambda dot Lambda_k$, and every $Lambda_k$-lattice $M$ of type $p-1$ can be
written as an inner tensor product
$ M tilde.equiv (lambda dot Lambda_k) times.o_(R_k) N, $
with $N$ a $Lambda_k$-lattice of type $1$. (Conversely, each such tensor product
is of type $p-1$.) The isomorphism class of $M$ determines that of $N$, and
conversely. The proof is not difficult, but we omit it.

The above results show how to classify all $R_k G$-lattices when $G$ is cyclic
of order $p$, with $p$ odd. Analogous results hold for $p=2$. For cyclic groups
of order $p^n$, $n>1$, partial results have been obtained by
Thévenaz~@bib:Thevenaz1981a @bib:Thevenaz1981b. His work also deals with
arbitrary finite groups. However, the general classification problem for
$R_k G$-lattices is of wild type (see Chapter~8 of Volume~II) whenever $k>=2$
and $G$ is a $p$-group (cyclic or not) of order greater than $p$. This result is
due to Bondarenko~@bib:Bondarenko1976; see also Gudivok~@bib:Gudivok1978b.

For further reading: Drobotenko-Gudivok-Lichtman~@bib:Drobotenko1964,
Drobotenko-Lichtman~@bib:Drobotenko1960, Hannula~@bib:Hannula1968,
Nazarova-Roiter~@bib:Nazarova1967a @bib:Nazarova1969, Levy~@bib:Levy1981.

#remarks(name: "Note", numbered: false)[
  Nazarova-Roiter~@bib:Nazarova1969 determine _all_ finite $ZZ G$-modules, where
  $G$ is cyclic of prime order $p$. Each such module $M$ decomposes into a sum
  of $q$-primary components, with $q$ ranging over all rational primes. The case
  where $q!=p$ is easily handled, since $ZZ_q G$ is a direct sum of local
  Dedekind rings. The only problem occurs when $q=p$.

  Here they use the fibre product diagram
  #cyclotomic-dyad-diagram()
  They call $Lambda$ a _dyad_.#idx("dyad")

  The general dyad problem is this: let $R_1$, $R_2$ be a pair of local Dedekind
  rings with common residue class field $k$, and let
  #general-dyad-diagram()
  be a fibre product; call $Lambda$ a _dyad_. Each f.g. $Lambda$-module $M$
  determines a pair of
  #source(663)
  matrices $bold(upright(A))$, $bold(upright(B))$ over $k$, whose rows are
  weighted in a certain way. Certain permissible operations are performed on
  these rows (and also on the columns), and the resulting canonical forms yield
  a complete classification of all indecomposable f.g. $Lambda$-modules $M$. The
  procedure generalizes Nazarova~@bib:Nazarova1967.

  The authors use their results to describe all finite groups having an abelian
  normal subgroup of index $p$. This extends the work of V. S.
  Drobotenko~@bib:Drobotenko1966. See also
  Nazarova-Roiter-Sergeicuk-Bondarenko~@bib:Nazarova1972, and
  Levy~@bib:Levy1981.
]

#exercises-heading

#exercise[
  Let $I$ be an ideal of the commutative ring $R$, and let $M$ be any left
  $R$-module. Show that there is an $R$-isomorphism
  $ (R slash I) times.o_R M tilde.equiv M slash I M. $
  #hint([@exc:quotient-tensor-module])[
    The sequence
    $ I times.o M -> R times.o M -> (R slash I) times.o M -> 0 $
    is exact.
  ]
] <exc:quotient-tensor-module>

#exercise[
  Let $R$ be a d.v.r. with prime element $pi$, and let $Lambda$ be an $R$-order
  in a semisimple $K$-algebra $A$. Let bars denote reduction mod $pi$, and let
  $M$ and $N$ be $Lambda$-lattices. Show that
  $
    Hom_(overline(Lambda)) lr((overline(M),overline(N))) tilde.equiv
    op("Ext")_Lambda^1 lr((overline(M),N)),
  $
  and that
  $
    Hom_(overline(Lambda)) lr((overline(M),overline(N)))=0 ==>
    op("Ext")_Lambda^1 lr((M,N))=0.
  $
  #hint([@exc:reduction-hom-extension-vanishing])[
    The exact sequence $0 -> N arrow.r^pi N -> overline(N) -> 0$ gives an exact
    sequence
    $
      Hom(overline(M), N) -> Hom(overline(M), overline(N))
      -> op("Ext")(overline(M), N) arrow.r^pi op("Ext")(overline(M), N).
    $
    But $Hom(overline(M), N)=0$ since $N$ is $R$-torsionfree; also,
    $pi dot op("Ext")(overline(M), N)=0$ since $pi overline(M)=0$. Thus
    $Hom(overline(M), overline(N)) tilde.equiv op("Ext")(overline(M), N)$. If
    $Hom(overline(M), overline(N))=0$, then the exact sequence
    $
      op("Ext")_Lambda^1 lr((overline(M),N)) ->
      op("Ext")_Lambda^1 lr((M,N)) arrow.r^pi
      op("Ext")_Lambda^1 lr((M,N))
    $
    shows that $pi$ gives a monomorphism of $op("Ext")(M, N)$ into itself. This
    implies that $op("Ext")(M, N)=0$, since $op("Ext")(M, N)$ is a f.g. torsion
    $R$-module.
  ]
] <exc:reduction-hom-extension-vanishing>

#exercise[
  Keep the notation of @prop:module-isomorphism-completion. Prove that
  $M divides N$ if and only if $hat(M) divides hat(N)$.
  #hint([@exc:module-summand-completion])[
    If $hat(M) divides hat(N)$, there exist $hat(Lambda)$-homomorphisms
    $f_1:hat(M) -> hat(N)$, and $g_1:hat(N) -> hat(M)$, such that $g_1 f_1=1$.
    As in the proof of @prop:module-isomorphism-completion, there exists
    $Lambda$-maps $f:M -> N$, $g:N -> M$, which lift $f_1$ and $g_1$,
    respectively, and such that $g f in Aut M$. Therefore $M divides N$.
  ]
] <exc:module-summand-completion>

#source(664)
#exercise[
  Keep the notation of
  @th:local-extension-indecomposable-endomorphism-correspondence, but assume
  further that $S$ has an $R$-basis of $k$ elements. Show that $S M$ and $S N$
  have a common indecomposable direct summand if and only if the same holds true
  for $M$ and $N$.
  #hint([@exc:finite-extension-common-summand])[
    It suffices to treat the case where $M$ and $N$ are indecomposable. Then use
    the fact that $S times.o_R M tilde.equiv M^((k))$ as $Lambda$-modules.
  ]
] <exc:finite-extension-common-summand>

#exercise[
  Keep the notation of
  @th:local-extension-indecomposable-endomorphism-correspondence. Let $S$ be a
  totally ramified extension of $R$, that is, an extension for which
  $overline(S)=overline(R)$. Show that for each f.g. indecomposable
  $Lambda$-module $M$, the $S Lambda$-module $S M$ is also indecomposable.
] <exc:totally-ramified-indecomposability>

#exercise[
  Let $Lambda$ be an $R$-order, where $R$ is a Dedekind domain. An $R$-algebra
  $S$ is called _faithfully flat_#idx("faithfully flat") if $S$ is a flat
  $R$-module with the property that for each $R$-module $M$, $S times.o_R M=0$
  implies $M=0$. Assuming $S$ faithfully flat, show that for f.g. left
  $Lambda$-modules $M$ and $N$ satisfying
  $S times.o_R M tilde.equiv S times.o_R N$ as $(S times.o_R Lambda)$-modules,
  it need not follow that $M tilde.equiv N$.
  #hint([@exc:faithfully-flat-isomorphism-nondescent])[
    Take $Lambda=R$, $S=product.co_P lr((R_P))$, where $P$ ranges over all
    maximal ideals of $R$, and $R_P$ denotes the $P$-adic completion of $R$.
    Choose $N=R$, $M=$ nonprincipal ideal of $R$. Then
    $S times.o M tilde.equiv S times.o N$ but $M tilde.equiv.not N$.
  ]
] <exc:faithfully-flat-isomorphism-nondescent>
