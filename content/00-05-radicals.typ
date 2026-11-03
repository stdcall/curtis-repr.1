#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/05-radicals.typ": units-quotient-diagram

== Radicals <sec:radicals>
#item-series(start: 0)

=== Basic Definitions <ss:radicals-basic-definitions>

Throughout, let $A$ be a ring with 1, and let “$A$-module” mean “left
$A$-module”, unless otherwise stated. A _simple_ $A$-module is a nonzero
$A$-module $X$ whose only submodules are 0 and $X$. By a _maximal
submodule_#idx("maximal submodule") of an $A$-module $M$ we mean a submodule
$N subset M$ such that there are no submodules $L$ with $N subset L subset
M$; thus $N$ is maximal in $M$ if and only if $M slash N$ is a simple module.

#source(124)
We show at once (by using Zorn's Lemma) that every finitely generated nonzero
module $M$ contains maximal submodules. Indeed, we shall prove that given any
submodule $N subset M$, there exists a maximal submodule $L$ of $M$ with
$N subset.eq L subset M$. Consider the set
$ S = {L: N subset.eq L subset M}, $
a non-empty subset of submodules of $M$ (note that $N in S$), and let $S$ be
partially ordered by inclusion. We wish to assert that $S$ contains a maximal
element. This will follow from Zorn's Lemma as soon as we show that each
chain#footnote[
  A _chain_#idx("chain") $\{L_alpha\}$ in a partially ordered set $(S,lt.eq)$ is
  a subset of $S$ such that for each $alpha$ and $beta$, either
  $L_alpha lt.eq L_beta$ or $L_beta lt.eq L_alpha$.
] $\{L_alpha\}$ from $S$ has an upper bound in $S$. Clearly $union L_alpha$ is a
submodule of $M$, and we need only show that this union lies in $S$, that is,
that it is a proper submodule of $M$. Suppose to the contrary that
$union L_alpha = M$. Since $M$ is f.g., we have $M = sum_(i=1)^n A m_i$ for some
elements $m_1,dots,m_n$. Then each $m_i$ lies in some $L_(alpha_i)$,
$1 lt.eq i lt.eq n$, whence $M = union.big_(i=1)^n L_(alpha_i)$. But for each
$i,j$ between 1 and $n$, one of $L_(alpha_i),L_(alpha_j)$ contains the other,
since $\{L_alpha\}$ is a chain. Thus $union.big_(i=1)^n L_(alpha_i)$ is some
$L_(alpha_k)$, which gives $M = L_(alpha_k)$, a contradiction. We have thus
shown that every chain $\{L_alpha\}$ from $S$ has an upper bound in $S$. Thus,
by Zorn's Lemma, $S$ has a maximal element $L$. Clearly
$N subset.eq L subset M$, and $L$ is a maximal submodule of $M$, as desired.

For each surjection $f: M -> X$ with $X$ simple, clearly $ker f$ is a maximal
submodule of $M$. Conversely, if $L$ is maximal in $M$, then $L$ is the kernel
of the natural surjection $M -> M slash L$. Thus, we can characterize maximal
submodules of $M$ as kernels of surjections $M -> X$, with $X$ simple.

The _radical_#idx("radical of module") of an $A$-module (denoted by $rad M$) is
defined as the intersection of all maximal submodules of $M$. (If $M$ has no
maximal submodules, set $rad M = M$.) By the preceding remarks,
$ rad M subset M $
for every nonzero finitely generated $A$-module $M$. Furthermore, for any module
$M$, we have
$ rad M = inter.big_(f: M -> X) ker f, $
where the intersection is taken over all surjections $f: M -> X$ with $X$
simple.

#example[
  If $M$ is a simple $A$-module, then $rad M = 0$ since 0 is the only maximal
  submodule of $M$. More generally, we claim that $rad M = 0$ for every
  semisimple left $A$-module $M$. Indeed, by @prop:semisimple-module-criteria we
  may express $M$ as a direct
  #source(125)
  sum $plus.o.big_(i in I) M_i$ of simple submodules $\{M_i\}$. If any summand
  is omitted, the remaining direct sum is a maximal submodule of $M$. Therefore
  the intersection of all maximal submodules of $M$ is 0, that is, $rad M = 0$.

  It may well happen that $rad M = 0$ even though $M$ is not a semisimple
  module. For example, let $M = ZZ$, a left $ZZ$-module. The maximal submodules
  of $M$ are given by $\{p dot ZZ: p "prime"\}$, and their intersection is 0.
  Thus $rad M = 0$, but $M$ cannot be expressed as a direct sum of simple
  submodules.
] <exm:semisimple-module-radical-zero>

#proposition[
  Let $L,M$ be $A$-modules.
  #enum(
    numbering: "(i)",
    [For each $A$-homomorphism $g: L -> M$, we have
      $ g(rad L) subset.eq rad M. $],
    [If $L subset.eq M$, then
      $
        rad L subset.eq rad M, quad "and" quad
        (rad M + L) slash L subset.eq rad(M slash L).
      $],
    [If $L subset.eq rad M$, then
      $ (rad M) slash L = rad(M slash L). $],
  )
] <prop:module-radical-functoriality>

#proof[
  To prove (i), let $f: M -> X$ be any surjection with $X$ simple. Then there is
  a map $f g: L -> X$, and the image $(f g)(L)$ is a submodule of $X$. Since $X$
  is simple, it follows that either $(f g)(L)=X$ or $(f g)(L)=0$. In the first
  case we have a surjection $f g: L -> X$, whence $(f g)(rad L)=0$, and so
  $g(rad L) subset.eq ker f$. In the second case we have
  $g(rad L) subset.eq g(L) subset.eq ker f$. Thus for each $f$ we have
  $g(rad L) subset.eq ker f$, and hence
  $ g(rad L) subset.eq inter.big_f ker f = rad M. $
  This proves (i).

  Now let $L subset.eq M$; this inclusion map yields an inclusion
  $rad L subset.eq rad M$, by (i). On the other hand, let $g: M -> M slash L$ be
  the natural surjection. Then by (i),
  $ (rad M + L) slash L = g(rad M) subset.eq rad(M slash L), $
  which establishes the second assertion in (ii).

  Finally, suppose that $L subset.eq rad M$. The correspondence $N mapsto
  N slash L$ maps each maximal submodule $N$ of $M$ containing $L$ onto a
  maximal submodule $N slash L$ of $M slash L$, and is bijective. However, since
  $rad M$ is the intersection of all maximal submodules of $M$, the hypothesis
  on $L$ implies that every maximal submodule $N$ of $M$ must contain $L$.
  Therefore
  $ (rad M) slash L = (inter N) slash L = inter(N slash L) = rad(M slash L), $
  where the intersections are taken over all maximal submodules $N$ of $M$. This
  completes the proof of the proposition.
]

#source(126)
#corollary[
  Let $M$ be an $A$-module. Then $M slash rad M$ has radical 0, and $rad M$ is
  the smallest submodule $M'$ of $M$ such that $rad(M slash M')=0$.
] <cor:quotient-by-module-radical>

#proof[
  By @prop:module-radical-functoriality(iii), with $L=rad M$, we have
  $ rad\{M slash (rad M)\} = (rad M) slash (rad M) = 0. $
  On the other hand, if $rad(M slash M')=0$ then by
  @prop:module-radical-functoriality it follows that $rad M subset.eq M'$. This
  completes the proof.
]

#corollary[
  Let $M$ be a finitely generated $A$-module, and let $L$ be a submodule such
  that $L+rad M=M$. Then necessarily $L=M$.
] <cor:radical-superfluous-finitely-generated>

#proof[
  By @prop:module-radical-functoriality(ii) we deduce that
  $M slash L subset.eq rad(M slash L)$, whence equality must hold. But
  $M slash L$ is a finitely generated $A$-module, since $M$ is finitely
  generated. We have already remarked above that $rad X subset X$ for every
  nonzero finitely generated module $X$. Thus $M slash L$ must be zero, and the
  proof is finished.
]

#definition[
  The _Jacobson radical_#idx("Jacobson radical") of $A$, denoted by $rad A$, is
  the radical of the left regular module $attach(A, bl: A)$. (Jacobson
  @bib:Jacobson1945b). Thus
  $ rad A = inter L, quad L "ranging over all maximal left ideals of" A. $
] <def:jacobson-radical>
#idx("radical of ring", target: [@def:jacobson-radical])

Let us give another description of $rad A$. For each $A$-module $X$, define its
_annihilator_#idx("annihilator") as
$ "ann" X = {a in A: a X = 0}, $
which is obviously a two-sided ideal of $A$.

#proposition[
  We have $rad A = inter.big_X "ann" X$, where $X$ ranges over all simple left
  $A$-modules. Thus $rad A$ is a two-sided ideal of $A$.
] <prop:radical-annihilates-simple-modules>

#proof[
  Let $X$ be simple; then $X= A x$ for each nonzero $x in X$, and there is a
  surjection $A -> X$ given by $a mapsto a x$, $a in A$. The kernel of this
  surjection must be a maximal left ideal $L$ of $A$, and clearly
  $L = "ann" x = {a in A: a x=0}$. Thus
  $
    inter.big_X "ann" X = inter.big_X {inter.big_(x in X) "ann" x}
    supset.eq inter L' = rad A,
  $
  where $L'$ ranges over all maximal left ideals of $A$.

  To prove the reverse inclusion, observe that by the preceding paragraph, every
  simple $X$ is of the form $A slash L$ for some maximal left ideal $L$ of $A$.
  If $a X=0$ then $a A subset.eq L$, whence $a in L$ since $1 in A$. This shows
  that $"ann" X subset.eq L$, and
  #source(127)
  hence
  $ inter.big_X "ann" X subset.eq inter.big_L L = rad A, $
  since $L$ may range over all maximal left ideals of $A$. This completes the
  proof of the formula
  $ rad A = inter.big_X "ann" X. $
  Finally, each $"ann" X$ is a two-sided ideal of $A$, whence so is $rad A$.
]

For future reference, we list some direct consequences of
@prop:module-radical-functoriality; these are assertions about radicals of
_rings_, and as we shall see, they follow readily from results about radicals of
_modules_.

#proposition[
  #enum(
    numbering: "(i)",
    [For each ring $A$, the factor ring $A slash rad A$ has radical 0.],
    [For any surjection of rings $f: A -> B$, we have
      $f(rad A) subset.eq rad B$, and $f$ induces a surjection
      $A slash rad A -> B slash rad B$.],
    [For each $A$-module $M$, $(rad A)M subset.eq rad M$.],
  )
] <prop:ring-radical-quotients-and-modules>

#proof[
  Assertion (i) follows by applying @cor:quotient-by-module-radical with
  $M = attach(A, bl: A)$. To prove (ii), view $B$ as a left $A$-module by means
  of $f$. By @prop:module-radical-functoriality we have
  $f(rad A) subset.eq rad attach(B, bl: A)$, where $rad attach(B, bl: A)$ is the
  intersection of the maximal $A$-submodules of $B$. But the left $A$-submodules
  of $B$ coincide with the left $B$-submodules of $B$, since $f$ is surjective.
  Thus $rad attach(B, bl: A)$ is identical with the Jacobson radical $rad B$ of
  the ring $B$. We have thus established that $f(rad A) subset.eq rad B$, which
  implies at once that $f$ induces a surjection of rings:
  $A slash rad A -> B slash rad B$.

  Finally, let $M$ be any left $A$-module, and consider a surjection $g: M -> X$
  with $X$ simple. Then
  $ g((rad A)M) subset.eq (rad A)X=0, $
  whence $(rad A)M subset.eq rad M$ as claimed.
]

#lemma(name: "Nakayama's Lemma")[
  Let $M$ be a finitely generated left $A$-module, and let $L subset.eq M$ be a
  submodule such that
  $ L + (rad A)M = M. $
  Then necessarily $L=M$.
] <lem:nakayama>
#idx("Nakayama's Lemma", target: [@lem:nakayama])

#proof[
  Since $(rad A)M subset.eq rad M$ by @prop:ring-radical-quotients-and-modules,
  the hypotheses imply that $L+rad M=M$. Therefore $L=M$ by
  @cor:radical-superfluous-finitely-generated, and the proof is finished.
]

#source(128)
There is another characterization of radicals of rings in terms of units, which
is extremely useful. We begin with some results of independent interest.

#proposition[
  Let $M$ be a noetherian $A$-module, and let $f in End_A M$ be such that
  $f(M)=M$. Then $f$ is an isomorphism.
] <prop:surjective-noetherian-endomorphism>

#proof[
  We need only show that $f$ is injective. For $n gt.eq 1$, set
  $ K_n = ker f^n = {m in M: f^n lr((m))=0}. $
  Then $K_1 subset.eq K_2 subset.eq dots$ is an ascending chain of submodules of
  $M$. Since $M$ is noetherian, the chain must terminate, so $K_n = K_(n+1)$ for
  some $n$. Now let $m in M$ be such that $f(m)=0$. Since $M=f(M)$ we have also
  $M=f^n lr((M))$, so $m=f^n lr((m'))$ for some $m' in M$. Then
  $0=f(m)=f^(n+1) lr((m'))$, whence $m' in K_(n+1)$. But then $m' in K_n$, so
  $f^n lr((m'))=0$, that is, $m=0$ as desired. This completes the proof.
]

An element $u in A$ is a _unit_#idx("unit") if there exists an element $v in A$
such that $u v=v u=1$. The group of units in $A$ will be denoted by $A^dot$ or
$u(A)$. In many cases which occur in this book, each $u in A$ having one-sided
inverse is necessarily a unit of $A$. In fact, we have:

#proposition[
  Let $A$ be a left noetherian ring, and let $a b=1$ in $A$. Then also $b a=1$,
  so $a,b in A^dot$.
] <prop:noetherian-one-sided-inverses>

#proof[
  We apply @prop:surjective-noetherian-endomorphism with $M$ the noetherian
  $A$-module $attach(A, bl: A)$. We have
  $ A = A a b subset.eq A b subset.eq A, $
  whence $A b=A$. Thus the left $A$-endomorphism $x mapsto x b$, $x in A$, is
  surjective. Hence it is injective by @prop:surjective-noetherian-endomorphism.
  But then from $(1-b a)b = b-b a b=0$ we may conclude that $1-b a=0$, as
  claimed.
]

We now prove the following basic result:

#theorem[
  For any ring $A$ with 1, we have
  $
    rad A & = {x in A: 1-a x b in A^dot "for all" a,b in A} \
          & = {x in A: 1-a x "has a left inverse for all" a in A}.
  $
  Further, for each $x in rad A$ and each $a in A$, a left inverse of $1-a x$ is
  necessarily a two-sided inverse.
] <th:radical-unit-characterization>

#proof[
  _Step 1._ Let $x in rad A$, and let $a,b in A$; we shall show that $1-a x b$
  has a two-sided inverse in $A$. Since $a x b in rad A$, it suffices to show
  that for
  #source(129)
  each $x in rad A$, we have $1-x in A^dot$. Consider the left ideal $A(1-x)$ of
  $A$; if $A(1-x) != A$, then
  $ A(1-x) subset.eq L subset A $
  for some maximal left ideal $L$ of $A$. But then $1-x in L$, and also
  $x in rad A subset.eq L$, whence also $1=(1-x)+x in L$. This is impossible,
  and proves that $A(1-x)=A$. Therefore
  $ 1=t(1-x) quad "for some" t in A. $
  This gives
  $ 1-t = -t x in rad A, $
  so by the same reasoning there is an element $u in A$ such that
  $ 1 = u(1-(1-t)). $
  Thus $u t=1$, and so
  $ u = u t(1-x) = 1-x. $
  This proves that $t$ is a two-sided inverse of $1-x$, so $1-x in A^dot$ as
  desired.

  _Step 2._ Let $x in A$ be such that $1-a x$ has a left inverse in $A$, for
  each $a in A$. To complete the proof of the theorem, we must show that
  $x in rad A$. By @prop:radical-annihilates-simple-modules it suffices to show
  that $x W=0$ for each simple left $A$-module $W$. If $x W != 0$, then
  $x w != 0$ for some $w in W$, and so $W=A dot x w$. Therefore $w=a x w$ for
  some $a in A$, that is, $(1-a x)w=0$. But then $w=0$, since $1-a x$ has a left
  inverse in $A$. This is a contradiction, and establishes the following
  inclusion:
  $ {x in A: 1-a x "has a left inverse for all" a in A} subset.eq rad A. $
  Thus the theorem is proved, since the final assertion thereof is obvious from
  the preceding assertions.
]

#corollary[
  The radical of the right regular module $A_A$ coincides with $rad A$. Thus
  $ rad A = inter R = inter "ann" Y, $
  where $R$ ranges over all maximal right ideals of $A$, and $Y$ ranges over all
  simple right $A$-modules.
] <cor:radical-left-right-symmetry>

#proof[
  The first formula for $rad A$ in @th:radical-unit-characterization is
  left-right symmetric, which implies the desired result.
]

#source(130)
We note also that by virtue of this symmetry we have
$
  rad A = {x in A: 1-x b "has a right inverse for all" b in A}.
$ <eq:radical-right-inverse-characterization>

To conclude this subsection, we shall compute the radicals of some rings related
to the ring $A$. Recall that an _idempotent_ in $A$ is a nonzero $e in A$ such
that $e^2=e$. Thus $e A e$ is a ring with identity element $e$. We prove
(following the treatment in Behrens @bib:Behrens1972, p. 154, Th. 8):

#proposition[
  Let $e in A$ be idempotent, and let $J=rad A$. Then
  $ rad e A e = e J e. $
  If $overline(A)=A slash J$, then
  $ e A e slash rad(e A e) tilde.equiv overline(e) overline(A) overline(e). $
] <prop:radical-idempotent-corner>

#proof[
  Clearly
  $ e J e = J inter e A e, $
  since for each $x in J inter e A e$, we have $x=e x e in e J e$. This shows
  that $e J e$ contains the intersection, and the reverse inclusion is obvious.

  Suppose now that $x in e J e$; then $e x=x e=x$, and for each $a in e A e$,
  $1-a x$ has a left inverse $y in A$. Thus $y(1-a x)=1$, so
  $ e y e(e-a x) = e y(1-a x)e = e. $
  This shows that $e-a x$ has a left inverse in $e A e$, whence $x in rad e A e$
  by @th:radical-unit-characterization. Thus $e J e subset.eq rad e A e$.

  Conversely, let $x in rad e A e$. To prove that $x in e J e$, it suffices to
  show that $x in J$. By @th:radical-unit-characterization, we need only verify
  that for each $a in A$, the element $1-a x$ has a left inverse in $A$. But
  $e a e in A$, so $e-e a e dot x$ has a left inverse $z$ in $e A e$. Thus
  $ z(e-e a e dot x)=e, quad z e=e z=z, $
  and so
  $ z-z a x=e. $
  Therefore
  $
    (1-e+z)(1-a x) & = (1-e)(1-a x)+z(1-a x) \
                   & = (1-e)(1-a x)+e=1-(1-e)a x=1-y,
  $
  where $y=(1-e)a x$. But $y^2=0$, so $(1+y)(1-y)=1$. This gives
  $ (1+y)(1-e+z)(1-a x)=(1+y)(1-y)=1, $
  so $1-a x$ has a left inverse in $A$. This completes the proof that
  $e J e=rad e A e$.

  #source(131)
  Finally, the kernel of the surjection
  $e A e -> overline(e) overline(A) overline(e)$ is $e A e inter J$. Since we
  have just shown that this intersection equals the radical of $e A e$, the
  final assertion of the proposition is established.
]

#proposition[
  Let $B=M_n lr((A))$ be a full matrix ring over the ring $A$, and let
  $J=rad A$. Then
  $ rad B=M_n lr((J)) $
  and
  $ B slash rad B tilde.equiv M_n lr((A slash J)). $
] <prop:radical-matrix-ring>

#proof[
  Since the rings $A$ and $B$ are Morita equivalent, every two-sided ideal of
  $B$ is of the form $M_n lr((I))$, with $I$ a two-sided ideal of $A$. Let us
  write $rad B=M_n lr((I))$, and let $\{e_(i j): 1 lt.eq i,j lt.eq n\}$ be a set
  of matrix units in $B$. Then $e_11 B e_11$ consists of all $n times n$
  matrices with arbitrary elements of $A$ in the $(1,1)$-position, and zeros
  elsewhere. We shall treat the ring isomorphism $e_11 B e_11 tilde.equiv A$ as
  an identification. By @prop:radical-idempotent-corner we then obtain
  $ I=e_11(rad B)e_11=rad(e_11 B e_11)=rad A=J, $
  so $rad B=M_n lr((J))$ as claimed. The formula for $B slash rad B$ is then
  obvious.
]

=== Radicals of Artinian Rings <ss:radicals-artinian-rings>

We recall that a left ideal $N$ in a ring $A$ is _nilpotent_#idx("nilpotent") if
there exists a positive integer $k$ such that the $k$-fold product
$N dot N dots N$ equals 0, or equivalently, if $x_1 x_2 dots x_k=0$ for all
$\{x_i\} subset N$. An element $x in A$ is _nilpotent_ if $x^k=0$ for some $k$,
and a left ideal is a _nil ideal_#idx("nil ideal") if each of its elements is
nilpotent. Nilpotent ideals are clearly nil ideals, but there exist rings for
which the reverse is not true.

#proposition[
  In a left artinian ring $A$, $rad A$ is a nilpotent ideal. Moreover $rad A$
  contains all nilpotent one-sided ideals (left or right) and all one-sided nil
  ideals.
] <prop:artinian-radical-nilpotent>

#proof[
  (Jacobson @bib:Jacobson1945b). Let $J=rad A$. By the minimum condition there
  exists an integer $m>0$ such that $J^m=J^(m+1)=dots$. We shall prove that
  $J^m=0$. If this is not the case, then $J^m=J^(2m) != 0$, and there exist left
  ideals $I$ such that $J^m I != 0$. Again by the minimum condition, there is a
  minimal such left ideal $I_0$. Then $J^m I_0 != 0$, which implies that
  $J^m a != 0$ for some $a in I_0$. But $J^m a subset.eq I_0$, and moreover,
  $J^m lr((J^m a))=J^(2m)a=J^m a != 0$. By the minimality of $I_0$, we have
  $I_0=J^m a$; hence $a in J^m a$, and so $a=x a$ for some $x in J^m$. Then
  $(1-x)a=0$, with $x in J^m subset J$, and hence $a=0$ because $1-x$ is
  invertible by @th:radical-unit-characterization. This is a contradiction, and
  we have proved that $J$ is nilpotent.

  #source(132)
  Now let $N$ be a nil left ideal; then for each $x in N$, $x^k=0$ for some $k$,
  and hence $1-x$ is invertible, with inverse $sum_(i=0)^infinity x^i$ (which is
  just a finite sum because $x^k=0$). For each $x in N$, $a x in N$ for all
  $a in A$, and so $1-a x$ is invertible for all $a in A$, and $x in rad A$ by
  @th:radical-unit-characterization. A similar argument shows that each nil
  right ideal is contained in $rad A$, and because nilpotent ideals are nil
  ideals, the proposition is proved.
]

In a left artinian ring, there is a useful connection between nilpotence of
ideals and the existence of idempotents.

#proposition[
  In a left artinian ring, each non-nilpotent left ideal contains an idempotent
  element.
] <prop:artinian-nonnilpotent-ideal-idempotent>

#proof[@bib:CurtisReiner1962[CR (24.2)] or @bib:Reiner1975[MO (6.8)].]

The proof in @bib:CurtisReiner1962[CR (24.2)] can be modified to prove the
existence of idempotents under weaker hypotheses:

#proposition[
  Let $N$ be a nilpotent left ideal in an arbitrary ring $A$, and let $x in A$
  be a non-nilpotent element such that $x^2-x in N$. Then the left ideal $A x$
  contains an idempotent element $y$ such that $y-x in N$.
] <prop:idempotent-modulo-nilpotent-ideal>

#proof[@bib:Reiner1975[MO (6.7)].]

For left artinian rings there is a close connection between radicals and the
concept of semisimplicity introduced in @sec:semisimple-rings-modules. Recall
that a left $A$-module $M$ is _semisimple_ if $M$ is a direct sum of some family
of simple submodules, or equivalently (see @prop:semisimple-module-criteria) if
every submodule of $M$ is a direct summand of $M$. The ring $A$ is _(left)
semisimple_ if every left $A$-module is semisimple. We now prove the following
basic result.

#theorem[
  A left artinian ring $A$ is left semisimple if and only if $rad A=0$.
] <th:artinian-semisimple-radical-zero>

#proof[
  By @prop:radical-annihilates-simple-modules, $rad A$ annihilates every simple
  left $A$-module. Hence if $A$ is left semisimple, then $(rad A)A=0$, and
  therefore $rad A=0$ since $1 in A$.

  Conversely, suppose that $rad A=0$, so by @prop:artinian-radical-nilpotent the
  ring $A$ contains no nilpotent left ideals except 0. Hence by
  @prop:artinian-nonnilpotent-ideal-idempotent every nonzero left ideal of $A$
  contains an idempotent element. Now define a _minimal left ideal_#idx(
    "minimal left ideal",
  ) of $A$ to be a simple submodule of $attach(A, bl: A)$. Under our assumption
  that $rad A=0$, each minimal left ideal $L$ contains an idempotent $e$.
  Clearly $A e subset.eq L$, and $A e$ is a nonzero submodule of $L$ since
  $e=e^2 in A e$. Therefore $L=A e$, which shows that when $rad A=0$, every
  minimal left ideal $L$ of $A$ is generated by an idempotent $e$; indeed, we
  have further
  $ L e=A e dot e=A e=L. $

  #source(133)
  Using this, let us show that $L$ is a direct summand of each left ideal $L'$
  of $A$ containing $L$. In fact, there is a direct sum decomposition of left
  $A$-modules:
  $ L'=L plus.o L'(1-e), $
  since the inclusions
  $ L=A e supset.eq L'e supset.eq L e=L $
  show that $L'e=L$.

  Now the left artinian module $attach(A, bl: A)$ clearly is expressible as a
  finite direct sum of indecomposable modules. By the above, each of these
  indecomposable summands must be a minimal left ideal of $A$. Therefore
  $attach(A, bl: A)$ is a semisimple module, that is, $A$ is a left semisimple
  ring.
]

By Exercise @exc:left-right-semisimplicity, a ring is left semisimple if and
only if it is right semisimple. For convenience of terminology, we omit the
adjectives “left”, “right”, and refer to such rings as _semisimple rings_#idx(
  "semisimple ring",
). We have at once

#proposition[
  For each left artinian ring $A$, the factor ring $A slash rad A$ is an
  artinian semisimple ring.
] <prop:artinian-semisimple-radical-quotient>

#proof[
  Let $B=A slash rad A$; then $rad B=0$ by
  @prop:ring-radical-quotients-and-modules(i). Further, since $A$ is left
  artinian, so is $B$. Hence $B$ is semisimple by
  @th:artinian-semisimple-radical-zero.
]

#theorem(name: "Hopkin's Theorem")[
  Every left artinian ring (with 1) is necessarily left noetherian.
] <th:hopkins-artinian-noetherian>
#idx("Hopkin's Theorem", target: [@th:hopkins-artinian-noetherian])

#proof[See @bib:CurtisReiner1962[CR (54.1)].]

=== Local Rings <ss:local-rings>

A ring $A$ is _local_#idx("local ring") (or _completely primary_#idx(
  "completely primary = local",
)) if $A$ has a unique maximal left ideal. It follows at once, from Definition
@def:jacobson-radical of $rad A$, that $A$ is local if and only if $rad A$ is a
maximal left ideal of $A$.

#proposition[
  The following are equivalent:
  #enum(
    numbering: "(i)",
    [$A$ is local.],
    [The set $S$ of non-units in $A$ is a left ideal.],
    [$A slash rad A$ is a division ring, that is, a skewfield.],
  )
] <prop:local-ring-criteria>

#proof[
  (i)$arrow.r.double$(ii). We are given that $rad A$ is a maximal left ideal. We
  shall prove that $rad A$ coincides with the set $S$ of non-units. Clearly
  $rad A subset.eq S$.

  #source(134)
  Conversely, let $x in S$, and consider the left ideal $A x$. If $A x != A$,
  then $A x$ is contained in a maximal left ideal, hence $A x subset.eq rad A$.
  If $A x=A$, then for some $y in A$, $y x=1$. Clearly $y in.not rad A$, hence
  $A y=A$ and there exists $z$ such that $z y=1$. Then $y$ is invertible, and
  hence $x$ is invertible, contrary to assumption.

  (ii)$arrow.r.double$(iii). If the set $S$ of non-units in $A$ is a left ideal,
  then clearly $S=rad A$, and $A$ is local. Then $A slash rad A$ contains no
  nontrivial left ideals, and is a division ring.

  Finally, (iii)$arrow.r.double$(i) by an easy argument, and the result is
  proved.
]

In @ss:localization, we have already encountered an example of a local ring.
Namely, let $P$ be a prime ideal in a commutative ring $R$; then the
localization $R_P$ of $R$ at $P$ is a local ring, and $rad R_P=P dot R_P$.
Likewise the discrete valuation rings occurring in @ss:valuations-completions
are local rings. Of course, every field or division ring is local. Much more
important for us, however, is the fact that under suitable hypotheses, a module
(over a ring) is indecomposable if and only if its endomorphism ring is local
(see @sec:idempotents-krull-schmidt-projective-covers below).

For the remainder of this section, we fix the following notation:
$
            R & = "commutative local ring" \
            P & = rad R = "unique maximal ideal of" R \
  overline(R) & = R slash P = "residue class field of" R \
            A & = R"-algebra" \
  overline(A) & = A slash P A.
$
We recall that an $R$-algebra $A$ comes equipped with a homomorphism $Phi$ of
$R$ into the center of $A$, such that $Phi(1_R)=1_A$. By virtue of this
homomorphism, every $A$-module may be viewed as $R$-module. In particular, $A$
is itself an $R$-module, and $overline(A)$ is an algebra over the field
$overline(R)$. The following basic result relates $rad A$ with
$rad overline(A)$.

#proposition[
  Let $R$ be a commutative local ring with residue class field
  $overline(R)=R slash P$, and let $A$ be an $R$-algebra which is finitely
  generated as $R$-module. Set $overline(A)=A slash P A$, a finite dimensional
  $overline(R)$-algebra, and let $phi: A -> overline(A)$ be the natural
  surjection. Then
  #enum(
    numbering: "(i)",
    [$rad A=phi^(-1) lr((rad overline(A))) supset.eq P A$.],
    [The map $phi$ induces an isomorphism of $overline(R)$-algebras
      $ A slash rad A tilde.equiv overline(A) slash rad overline(A). $],
    [$A slash rad A$ is a semisimple artinian ring.],
    [There exists a positive integer $k$ such that
      $ (rad A)^k subset.eq P A. $],
  )
] <prop:finite-algebra-local-base-radical>

#proof[
  #source(135)
  We show first that $P A subset.eq rad A$ by proving that $P A dot M=0$ for
  each simple left $A$-module $M$. Since $M=A m$ for each nonzero $m in M$, it
  follows that $M$ is finitely generated as $R$-module. Now $P M$ is an
  $A$-submodule of $M$, and hence is either $M$ or 0. But $P M != M$ by
  Nakayama's Lemma @lem:nakayama, since otherwise $M=0$. Thus $P M=0$, whence
  $P A dot M=0$ for each simple $A$-module $M$. This proves that
  $P A subset.eq rad A$.

  By @prop:ring-radical-quotients-and-modules(ii), the surjection
  $phi: A -> overline(A)$ induces a surjection
  $ A slash rad A -> overline(A) slash rad overline(A). $
  On the other hand, since $P A subset.eq rad A$ there is also a surjection
  $ psi: overline(A) -> A slash rad A. $
  By @prop:ring-radical-quotients-and-modules we have
  $ psi(rad overline(A)) subset.eq rad(A slash rad A)=0, $
  and therefore $psi$ induces a surjection
  $ overline(A) slash rad overline(A) -> A slash rad A. $
  But both $A slash rad A$ and $overline(A) slash rad overline(A)$ are finite
  dimensional algebras over the field $overline(R)$, and each is a homomorphic
  image of the other. Hence each of these surjections must be an isomorphism,
  which proves (i) and (ii). Assertion (iii) follows at once from (ii), by use
  of @prop:artinian-semisimple-radical-quotient.

  Finally, since $overline(A)$ is artinian it follows from
  @prop:artinian-radical-nilpotent that $(rad overline(A))^k=0$ for some $k$.
  Therefore $phi((rad A)^k)=0$, whence $(rad A)^k subset.eq ker phi
  = P A$. This completes the proof of the proposition.
]

Keeping the above notation, let us briefly discuss completions (see
@ss:valuations-completions). Given a finitely generated $R$-module $X$, we give
$X$ a _$P$-adic topology_ by choosing as basis for the neighborhoods of a point
$x in X$ the open sets
$ {x+P^k X: k=0,1,2,dots}. $
Let $hat(X)$ denote the $P$-adic completion of $X$ in this topology, and in
particular let $hat(R)$ be the completion of $R$.

If, for example, $X=plus.o.big_(i=1)^m R x_i$ is $R$-free, then
$P^k X=plus.o.big_(i=1)^m P^k x_i$. If $\{y_n\}$ is a sequence of elements of
$X$, we may write
$ y_n=sum_(i=1)^m r_n^((i)) x_i, quad r_n^((i)) in R. $
It is then obvious that $\{y_n\}$ is a Cauchy sequence relative to the $P$-adic
topology on $X$ if and only if for each $i$, $\{r_n^((i))\}$ is a Cauchy
sequence relative to the $P$-adic topology on $R$. Further, $\{y_n\}$ converges
in $X$ if and only if each
#source(136)
$\{r_n^((i))\}$ converges in $R$, and we have
$
  lim_(n -> infinity) sum_(i=1)^m r_n^((i)) x_i
  = sum_(i=1)^m (lim_(n -> infinity) r_n^((i))) x_i.
$
Thus $X$ is complete if and only if $R$ is complete.

When $R$ is not complete, we may form the $P$-adic completions $hat(R)$ and
$hat(X)$, and the preceding discussion shows that there is a topological
$hat(R)$-isomorphism
$ hat(X) tilde.equiv hat(R) times.o_R X. $ <eq:completion-tensor-product>

As a matter of fact (see @bib:Reiner1975[MO (6.16)] and references listed
there), the isomorphism @eq:completion-tensor-product holds true for any
finitely generated $R$-module $X$, provided that $R$ is a commutative noetherian
local ring. Furthermore, $hat(R)$ and $hat(X)$ are complete Hausdorff spaces
relative to the topologies induced on them by the $P$-adic topologies of $R$ and
$X$. We shall use this fact primarily for the case where $hat(R)$ is the
$P$-adic completion of a discrete valuation ring with maximal ideal $P$ (see
@ss:valuations-completions).

Let us conclude this subsection with some important examples of local rings. We
prove

#theorem[
  Let $G$ be a finite $p$-group, and let $K$ be a field of characteristic $p$.
  Then there is exactly one simple left $K G$-module, namely, the field $K$ on
  which the elements of $G$ act trivially. Further, $K G$ is a local ring, and
  $ rad K G = plus.o.big_(x in G - {1}) K(x-1), $
  the augmentation ideal of $K G$. Moreover, every f.g. projective $K G$-module
  is free.
] <th:p-group-algebra-local>
#idx("augmentation ideal", target: [@th:p-group-algebra-local])

#proof[
  The result is clear if $abs(G)=1$, so assume now that $abs(G)=p^n$, $n>0$, and
  use induction on $n$. Let $V$ be any simple $K G$-module, and let
  $ H={x in G: x "acts trivially on" V}. $
  Then $H lt.closed.eq G$, and $V$ is also a simple $K(G slash H)$-module. If
  $H != 1$, then $V$ is the trivial module $K$ by the induction hypothesis. So
  now suppose that $H=1$, that is, if $(x-1)V=0$ for some $x in G$, then $x=1$.
  By @sec:background-algebras-groups, the group $G$ has a nontrivial center
  $Z(G)$; choosing $x in Z(G)$, $x != 1$, it is then clear that $(x-1)V$ is a
  nonzero submodule of $V$. Hence $V=(x-1)V$. But then
  $ V=(x-1)V=(x-1)^2 V=dots=(x-1)^(p^n) V=(x^(p^n)-1)V=0, $
  a contradiction. This completes the proof that $V tilde.equiv K$.

  #source(137)
  Now $rad K G$ is the intersection of the annihilators of the simple
  $K G$-modules, and thus $rad K G$ is the annihilator of $K$. Let
  $J=plus.o.big K(x-1)$, summed over all $x in G-\{1\}$. Then $J$ annihilates
  the simple module $K$, so $J subset.eq rad K G$. But $dim_K J=abs(G)-1$, and
  $rad K G subset K G$. Therefore $rad K G=J$, as claimed. Hence $K G$ is local
  by @prop:local-ring-criteria. The final assertion now follows from Exercise
  @exc:projective-local-free.
]

#corollary[
  Let $G$ be a $p$-group, and let $R$ be a commutative local ring with
  $P=rad R$, and let $overline(R)=R slash P$ be a field of characteristic $p$.
  Then the group ring $R G$ is local, and
  $ rad R G=P G+I, quad R G slash rad R G tilde.equiv R slash P, $
  where
  $ I=plus.o.big_(x in G, x != 1) R(x-1) $
  is the augmentation ideal of $R G$. Further, every f.g. projective
  $R G$-module is free.
] <cor:p-group-ring-local-base>
#idx("augmentation ideal", target: [@cor:p-group-ring-local-base])

#proof[
  By @prop:finite-algebra-local-base-radical, $rad R G$ is the inverse image of
  $rad overline(R)G$ under the surjection
  $
    R G -> R G slash P dot R G tilde.equiv overline(R)G, quad
    "where" overline(R)=R slash P.
  $
  The result now follows from @th:p-group-algebra-local and Exercise
  @exc:projective-local-free.
]

#proposition[
  Let $p$ be prime, and let $D$ be a normal $p$-subgroup of a finite group $G$.
  Let $R$ be a commutative local ring whose residue class field $overline(R)$
  has characteristic $p$. Then the natural surjection $tau: R G -> R(G slash D)$
  has the property that $ker tau$ is nilpotent mod $P G$, and hence
  $ker tau subset.eq rad(R G)$.
] <prop:normal-p-subgroup-radical-kernel>

#proof[
  By the preceding discussion, it is sufficient to work over the field
  $overline(R)$. As an exercise, the reader can verify that $ker tau$ is
  generated by elements of the form $g(x-1)$, with $g in G$, $x in D$. The
  identity
  $ g(x-1)g'(x'-1)=g g'((g')^(-1)x g'-1)(x'-1), $
  combined with @th:p-group-algebra-local, shows that $ker tau$ is nilpotent mod
  $P G$, and the result follows. (See also
  @prop:normal-p-subgroup-brauer-kernel.)
]

We end this subsection with a few remarks about semilocal rings.

#definition[
  The ring $A$ is _semilocal_#idx("semilocal") if $A slash rad A$ is a
  semisimple artinian ring. (Local rings are automatically semilocal!)
] <def:semilocal-ring>

#source(138)
By @prop:ring-radical-quotients-and-modules(i), the factor ring $A slash rad A$
has radical 0. Thus by @def:semisimple-ring and
@th:artinian-semisimple-radical-zero, this factor ring is semisimple if and only
if it is artinian. Hence the ring $A$ is semilocal if and only if
$A slash rad A$ is (left) artinian. This gives

#proposition[
  #enum(numbering: "(i)", [Every left artinian ring is semilocal.], [Every
    $R$-algebra $A$, as in @prop:finite-algebra-local-base-radical, is
    semilocal.])
] <prop:artinian-and-finite-local-algebras-semilocal>

Let us point out that $ZZ$ is _not_ semilocal, so there exist rings which are
not semilocal. More generally, any Dedekind domain $A$ with an infinite number
of maximal ideals is not semilocal.

For semilocal rings, there is an important relation between radicals of modules
and the Jacobson radical of the ring. We have:

#proposition[
  Let $M$ be a left $A$-module, where $A$ is any semilocal ring. Then
  $ rad M=(rad A)M. $
] <prop:semilocal-module-radical>

#proof[
  Put $J=rad A$, $overline(A)=A slash J$, so $overline(A)$ is a semisimple
  artinian ring. Then $M slash J M$ is a left $overline(A)$-module, hence is
  semisimple by @prop:semisimple-ring-criteria. Thus $rad(M slash J M)=0$ by
  @exm:semisimple-module-radical-zero. However,
  $ rad(M slash J M)=(rad M) slash J M $
  by @prop:module-radical-functoriality(iii), since we already know that
  $J M subset.eq rad M$ from @prop:ring-radical-quotients-and-modules. Thus
  $rad M=J M$, as claimed.
]

#exercises-heading

#exercise[
  Prove that every maximal two-sided ideal $J$ of the ring $A$ must contain
  $rad A$.

  #hint([@exc:maximal-two-sided-ideal-radical])[
    If not, then $J+rad A=A$; now use Nakayama's Lemma.
  ]
] <exc:maximal-two-sided-ideal-radical>

#exercise[
  Show that an element $x$ of a ring $A$ is a unit if and only if the image of
  $x$ in $A slash rad A$ is a unit.
] <exc:units-modulo-radical>

#exercise[
  Let $A$ be a ring such that $A slash rad A$ is semisimple artinian, and let
  $J$ be a one-sided ideal of $A$ such that $J^m subset.eq rad A$. Prove that
  $J subset.eq rad A$.

  #hint([@exc:nilpotent-modulo-radical])[
    The image of $J$ in the semisimple artinian ring $A slash rad A$ is a
    nilpotent one-sided ideal, hence is 0 by @prop:artinian-radical-nilpotent.
  ]
] <exc:nilpotent-modulo-radical>

#exercise[
  Let $e in A$ be idempotent, where $A$ is any ring. Show that
  $ S inter e A e=(e S e) inter S $
  for every subset $S$ of $A$. Deduce that
  $ L=A L inter e A e $
  #source(139)
  for each left ideal $L$ of $e A e$. Show from this that if $A$ is left
  noetherian, then so is the ring $e A e$. Prove the corresponding result when
  “noetherian” is replaced by “artinian”.
] <exc:corner-ring-finiteness>

#exercise[
  Prove that any monomorphism $f: M -> M$ of an artinian $A$-module $M$ must be
  an isomorphism. Here, $A$ is an arbitrary ring.

  #hint([@exc:injective-artinian-endomorphism])[
    Imitate the proof of @prop:surjective-noetherian-endomorphism.
  ]
] <exc:injective-artinian-endomorphism>

#exercise[
  Let $A$ be a f.d. algebra over a field $K$, and let $T: A times A -> K$ be the
  bilinear trace form given by $T(a,b)=T_(A slash K) lr((a b))$, $a,b in A$,
  where $T_(A slash K)$ is the ordinary trace. Show that if $T$ is nondegenerate
  then $A$ is semisimple. (See also Exercise @exc:separable-trace-form.)

  #hint([@exc:nondegenerate-trace-semisimple])[
    Each element of $rad A$ is nilpotent by @prop:artinian-radical-nilpotent, so
    has trace 0. For $x in rad A$, we obtain
    $"Tr"(x,A)=T_(A slash K) lr((x A))=0$, so $x=0$.
  ]
] <exc:nondegenerate-trace-semisimple>

#exercise[
  Let $A$ be an $R$-algebra as in @prop:finite-algebra-local-base-radical,
  assume in addition that $R$ is noetherian, and let $hat(R)$ denote the
  $P$-adic completion of $R$. Let $hat(A)=hat(R) times.o_R A$, the $P$-adic
  completion of $A$. Show that
  $
    rad hat(A)=hat(R) times.o_R rad A, quad
    hat(A) slash rad hat(A) tilde.equiv A slash rad A.
  $

  #hint([@exc:radical-completion])[
    Since $P$ annihilates $A slash rad A$, we have
    $
      A slash rad A tilde.equiv hat(R) times.o (A slash rad A)
      tilde.equiv hat(A) slash (hat(R) times.o rad A),
    $
    where $times.o$ means $times.o_R$. Therefore
    $hat(R) times.o rad A supset.eq rad hat(A)$, since $A slash rad A$ is
    semisimple. On the other hand, $(hat(R) times.o rad A)^k subset.eq
    P hat(A)$ with $k$ as in @prop:finite-algebra-local-base-radical(iv), whence
    $hat(R) times.o rad A subset.eq rad hat(A)$.
  ]
  #ed-note[
    The noetherian hypothesis on $R$ has been added: without it, the displayed
    radical identity can fail, even when $A=R$. For completion of finite modules
    under this hypothesis, see Reiner~@bib:Reiner2003, Theorem~6.16.
  ]
] <exc:radical-completion>

#exercise[
  Let $R$ be a commutative local noetherian ring with maximal ideal $P$, and let
  $M$ be a f.g. left $R$-module. Let $f in Aut_R lr((M))$ and
  $g in End_R lr((M))$ be such that $f equiv g (mod P)$, that is,
  $ f-g in P dot End_R lr((M)). $
  Prove that also $g in Aut_R lr((M))$.

  #hint([@exc:automorphism-modulo-maximal-ideal])[
    The hypothesis implies that $M=g(M)+P M$. Now use @lem:nakayama and
    @prop:surjective-noetherian-endomorphism.
  ]
] <exc:automorphism-modulo-maximal-ideal>

#exercise[
  Let $R$ be a complete d.v.r. of characteristic zero, with maximal ideal $pi R$
  and residue class field of characteristic $p$. Let $G$ be a cyclic $p$-group
  of order $p^n$, where $n gt.eq 1$. Show that the $R G$-module $rad R G$ is
  indecomposable except possibly when $n=1$. (The result is due to Ayoub and
  Ayoub @bib:Ayoub1969 and J. Schmidt.)

  #hint([@exc:cyclic-p-group-ring-radical-indecomposable])[
    Let $K$ be the quotient field of $R$, put $q=v_pi lr((p))$ and $N=p^n$, and
    write $G=chevron.l x chevron.r$. Then
    $
      J=rad R G=pi R G+(x-1)R G, quad
      End_(R G) lr((J))={y in K G: J y subset.eq J}.
    $
    Indeed, $K J=K G$, so endomorphisms extend to multiplication maps on $K G$.
    Thus it suffices to exclude nontrivial idempotents $e$ with
    $J e subset.eq J$. Such an $e$ satisfies $pi e in J subset.eq R G$. If $d$
    is the rank of multiplication by $e$ on $K G$, its regular trace gives the
    coefficient of 1 in $e$ as $d slash p^n$, where $0<d<p^n$. Consequently
    $ v_pi lr((d slash p^n))=q(v_p lr((d))-n) <= -q. $
    Integrality of $pi e$ implies that this valuation is at least $-1$. Hence
    $q=1$ and $v_p lr((d))=n-1$. In particular, there is no such $e$ in the
    ramified case $q>1$.

    When $q=1$, for $1 <= j <= n$ the polynomial $Phi_(p^j)(1+T)$ is Eisenstein
    over $R$: its constant term is $p$, and its reduction is $T^((p-1)p^(j-1))$.
    Therefore the field factors of $K G$ have dimensions
    $1,p-1,(p-1)p,dots,(p-1)p^(n-1)$. A nonzero sum of a proper subset of these
    dimensions is divisible by
    $p^(n-1)$
    only when it consists of all the lower dimensions or of the single top
    dimension. Thus the only possible $e$ are $h$ and $1-h$, where
    #source(140)
    $ h=e_(n-1)=1/p sum_(k=0)^(p-1) x^(k p^(n-1)). $
    This is the average of the subgroup $H=chevron.l x^(p^(n-1)) chevron.r$ of
    order $p$. If $n>1$, the cosets $H$ and $x H$ are disjoint, so $(x-1)h$ has
    coefficients $1/p$ and $-1/p$ and does not belong to $R G$. The same
    obstruction applies to $1-h$. This proves indecomposability for $n>1$. If
    $n=1$ and $q=1$, then $(x-1)h=0$ and $pi h in J$: the latter follows from
    integrality and augmentation $pi in pi R$. Both $h$ and $1-h$ preserve $J$,
    so $J$ is decomposable. If $n=1$ and $q>1$, the trace argument already
    proves indecomposability.
  ]
  #ed-note[
    The printed primitive-idempotent list is defective, and primitivity of
    rational subgroup averages cannot be assumed after extension to an arbitrary
    $K$. The hint above is an independent replacement argument. For Eisenstein's
    criterion see Reiner~@bib:Reiner2003, Exercise~5.1; for the rational
    subgroup averages and their successive differences see
    Ayoub–Ayoub~@bib:Ayoub1969, Theorem~5 and its corollary.
  ]
] <exc:cyclic-p-group-ring-radical-indecomposable>

#exercise[
  Let $M$ be a f.g. left $A$-module, where $A$ is a left artinian ring. Show
  that $M$ is semisimple if and only if $rad M=0$.

  #hint([@exc:artinian-module-radical-zero])[
    Use @prop:semilocal-module-radical and
    @prop:radical-annihilates-simple-modules.
  ]
] <exc:artinian-module-radical-zero>

#exercise[
  Let $M$ and $N$ be $A$-modules, where $A$ is arbitrary. Prove that
  $ rad(M plus.o N)=rad M plus.o rad N. $

  #hint([@exc:radical-direct-sum])[
    Apply @prop:module-radical-functoriality(i) to the inclusions
    $M -> M plus.o N$, $N -> M plus.o N$ to obtain
    $rad M plus.o rad N subset.eq rad(M plus.o N)$. Apply it to the two
    projections to obtain the reverse inclusion.
  ]
  #ed-note[
    The printed proof, attributed to Janusz, groups all maximal submodules into
    intersections indexed by pairs of maximal submodules of $M$ and $N$. Such a
    family can be empty, even when the other module has maximal submodules. The
    hint above avoids this problem. For the convention that $rad M=M$ when $M$
    has no maximal submodules see Lam~@bib:Lam1999, p.~99; the direct-sum
    argument here follows independently from @prop:module-radical-functoriality.
  ]
] <exc:radical-direct-sum>

#exercise[
  Let $A$ be an $R$-algebra as in @prop:finite-algebra-local-base-radical, $I$
  any two-sided ideal of $A$. Show that the surjection $A -> A slash I$ gives a
  surjection $u(A) -> u(A slash I)$ of unit groups.

  #hint([@exc:units-surject-quotient-local-base])[
    By @prop:ring-radical-quotients-and-modules,
    $rad(A slash I) supset.eq (I+rad A) slash I$. On the other hand,
    $
      overline(A)=(A slash I) slash ((I+rad A) slash I)
      tilde.equiv A slash (I+rad A)
      = "factor ring of" A slash rad A.
    $
    Thus $overline(A)$ is semisimple artinian, so
    $rad(A slash I)=(I+rad A) slash I$. Consider the commutative diagram

    #units-quotient-diagram

    #source(141)
    in which each arrow is a ring surjection. For $x in u(A slash I)$,
    $f(x) in u(overline(A))$. But $f(x)=g(y)$ for some $y in u(A slash rad A)$,
    since $A slash rad A$ is semisimple. Then $y$ is the image of some
    $a in u(A)$, and $a-x in I+rad A$. Changing $a$ mod $(rad A)$ and $x$ mod
    $I$, we then have $x=$ image of an element in $u(A)$.
  ]
] <exc:units-surject-quotient-local-base>
