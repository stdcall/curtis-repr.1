#import "main-defs.typ": *
#import "statements.typ": *

== Jordan-Zassenhaus Theorem <sec:jordan-zassenhaus>

Throughout this section, let $R$ be a Dedekind domain with quotient field $K$.
If $K$ is a global field (either an algebraic number field or a function field,
as described in §@ss:ideal-class-groups-global-fields), then the number of
classes of $R$-ideals in $K$ is finite. The Jordan-Zassenhaus Theorem stated
below is a strong generalization of this fact, and is proved by arguments
analogous to those used for global fields. Instead of $R$-ideals in $K$, we
consider full $Lambda$-lattices in some given f.g. left $A$-module. Here,
$Lambda$ is an $R$-order in a semisimple f.d. $K$-algebra $A$. Further, instead
of ideal classes we consider isomorphism classes of $Lambda$-lattices. The
fundamental result is as follows:

#theorem(name: "Jordan-Zassenhaus Theorem")[
  Let $R$ be a Dedekind ring whose field of quotients $K$ is a global field. Let
  $A$ be a finite dimensional semisimple $K$-algebra, and let $Lambda$ be an
  $R$-order in $A$. Then for each f.g. left $A$-module $V$, there are only a
  finite number of isomorphism classes of left $Lambda$-lattices $M$ such that
  $K M tilde.equiv V$.
] <th:jordan-zassenhaus>
#idx("Jordan-Zassenhaus Theorem", target: [@th:jordan-zassenhaus])

#source(557)
We shall omit the proof, which is given in detail in @bib:Reiner1975[MO §26].
Another version of the proof is given in @bib:CurtisReiner1962[CR §79] for the
special case where $K$ is an algebraic number field.

It is often useful to state @th:jordan-zassenhaus in a somewhat different form.
If $K M tilde.equiv V$, we may replace $M$ by its isomorphic image in $V$; it
thus suffices to consider full $Lambda$-lattices lying in a given f.g.
$A$-module $V$. Recall from §@ss:modules-dedekind-domains that the dimension
$dim_K K M$ is called the _$R$-rank_ of $M$. Let $t>0$. Since $A$ is semisimple
(by hypothesis), there are only finitely many isomorphism classes of $A$-modules
$V$ such that $dim_K V<=t$. Thus we have the following equivalent formulation of
@th:jordan-zassenhaus:

#theorem[
  Keep the notation and hypotheses of @th:jordan-zassenhaus. Then for each
  $t>0$, there are only finitely many isomorphism classes of left
  $Lambda$-lattices whose $R$-rank is at most $t$.
] <th:jordan-zassenhaus-bounded-rank>

We are going to prove that if $A$ is _not_ semisimple, and if $R!=K$, then for
each $R$-order $Lambda$ in $A$ there are infinitely many non-isomorphic full
left $Lambda$-lattices in $A$. Thus (assuming that $R$ is not a field), the
hypothesis that $A$ be semisimple cannot be omitted from the statement of the
Jordan-Zassenhaus Theorem.

By way of preparation, let us give a definition which will be useful in other
contexts as well.

#definition[
  Let $M$ be a full $R$-lattice in a f.d. $K$-algebra $A$. The _left order_
  #idx("left order")#idx("order", "left") of $M$ is defined as
  $ O_l lr((M))={x in A:x M subset.eq M}. $
  #idx("$O_l lr((M)), O_r lr((M))$")
  The _right order_#idx("right order")#idx("order", "right") of $M$ is defined
  as
  $ O_r lr((M))={x in A:M x subset.eq M}. $
] <def:left-right-order>

(Some authors call $O_l lr((M))$ the _left multiplier ring_ of $M$.) #idx(
  "left multiplier ring",
)#idx("multiplier ring")

Clearly $O_l lr((M))$ is an $R$-module, and is a subring of $A$ whose center
contains $R$. To show that $O_l lr((M))$ is an $R$-order in $A$, we must check
that $O_l lr((M))$ is a full $R$-lattice in $A$. For each $x in A$, $x M$ is an
$R$-lattice in $A$ (though not necessarily a full lattice in $A$); hence there
exists a nonzero $r in R$ such that $r dot x M subset.eq M$. Thus
$r x in O_l lr((M))$, which proves that $K dot O_l lr((M))=A$. Next, there
exists a nonzero $s in R$ such that $s dot 1_A in M$, where $1_A$ is the
identity element of $A$. Then $O_l lr((M)) dot (s dot 1_A) subset.eq M$, so
$O_l lr((M)) subset.eq s^(-1) M$. Since $R$ is noetherian and $s^(-1) M$ is
f.g./$R$, it follows that $O_l lr((M))$ is also f.g./$R$. Thus $O_l lr((M))$ is
a full $R$-lattice in $A$, and is therefore an $R$-order in $A$. Likewise,
$O_r lr((M))$ is an $R$-order in $A$.

#source(558)
In particular, if $Lambda$ is an $R$-order in $A$, then by
Exercise~@exc:left-order-principal-lattice
$ O_l lr((Lambda))=O_r lr((Lambda))=Lambda. $

These concepts play a crucial role in the following result of
Faddeev~@bib:Faddeev1965a (see also Roggenkamp and Huber-Dyson
@bib:Roggenkamp1970a, pp. 201–202):

#proposition[
  Let $A$ be a non-semisimple f.d. $K$-algebra. Let $Lambda$ be an $R$-order in
  $A$, where $R$ is a Dedekind domain but not a field. Then there exists a
  strictly increasing infinite chain of full left $Lambda$-lattices in $A$, no
  two of which are isomorphic.
] <prop:nonsemisimple-infinite-lattice-chain>

#proof[
  Since $A$ is (left) artinian and not semisimple, it follows from
  @prop:artinian-radical-nilpotent and @th:artinian-semisimple-radical-zero that
  $rad A$ is a nonzero nilpotent ideal of $A$. Hence there exists an integer
  $n>=1$ such that
  $ (rad A)^n!=0,(rad A)^(n+1)=0. $
  Since $R!=K$, there exists a nonzero element $r in R$ such that
  $r^(-1) in.not R$. We now put
  $ L_i=Lambda inter (rad A)^i,i>=1. $
  Then each $L_i$ is an $R$-pure $Lambda$-sublattice of $Lambda$, by
  @prop:pure-order-sublattice-correspondence. We now define
  $ Lambda_t=Lambda+r^(-t) L_1+r^(-2t) L_2+...+r^(-n t) L_n,t>=1. $
  From the fact that $L_i L_j subset.eq L_(i+j)$ for $i,j>=1$, it follows
  readily that each $Lambda_t$ is an $R$-order in $A$. Further, since
  $L_i subset.eq r^(-1) L_i$ for each $i$, we obtain an increasing sequence
  $ Lambda=Lambda_0 subset.eq Lambda_1 subset.eq Lambda_2 subset.eq ... . $
  <eq:nonsemisimple-order-chain>
  We prove next that each inclusion is strict. Suppose to the contrary that
  $Lambda_t=Lambda_(t+1)$ for some $t$. Multiplying by $r^((t+1)n)$, we find
  that $L_n subset.eq r^n Lambda$. Therefore
  $
    L_n subset.eq r^n Lambda inter (rad A)^n
    =r^n (Lambda inter (rad A)^n)=r^n L_n.
  $
  Thus $L_n=r^n L_n$, which is impossible since $r^n$ is a nonunit of $R$ and
  $L_n$ is an $R$-lattice (see Exercise~@exc:nonunit-invariant-lattice-zero).
  Thus the chain of $Lambda_t$'s is strictly increasing, as claimed.

  We have shown that each $Lambda_t$ is an $R$-order in $A$, and is hence a full
  $Lambda$-lattice in $A$. We claim that no two of the ${Lambda_t}$ are
  $Lambda$-isomorphic. Indeed, if $Lambda_i tilde.equiv Lambda_j$ as left
  $Lambda$-modules, then by @th:change-of-rings this isomorphism extends to an
  isomorphism $A tilde.equiv A$ as left $A$-modules. Such an isomorphism must be
  given by right multiplication by some unit $x in A$, and so
  $Lambda_i=Lambda_j x$. But then (see
  #source(559)
  Exercise~@exc:left-order-principal-lattice)
  $ Lambda_i=O_l lr((Lambda_i))=O_l lr((Lambda_j x))=Lambda_j, $
  so $i=j$. Thus @eq:nonsemisimple-order-chain is the desired chain of full
  $Lambda$-lattices in $A$, no two of which are isomorphic.
]

#corollary[
  Keep the hypotheses of @prop:nonsemisimple-infinite-lattice-chain. Then every
  $R$-order $Lambda$ is strictly contained in a larger $R$-order in $A$.
] <cor:nonsemisimple-no-maximal-order>
#proof[
  Use the notation of the proof of @prop:nonsemisimple-infinite-lattice-chain.
  We have shown that $Lambda subset Lambda_1$, and that $Lambda_1$ is also an
  $R$-order in $A$.
]

There is also a local version of the Jordan-Zassenhaus Theorem, as follows:

#theorem[
  Let $R$ be a complete d.v.r. whose field of quotients $K$ is the completion of
  a global field with respect to some non-archimedean valuation. Let $Lambda$ be
  an $R$-order in a semisimple f.d. $K$-algebra $A$. Then for each $t>0$, there
  are only finitely many isomorphism classes of left $Lambda$-lattices whose
  $R$-rank is at most $t$.
] <th:local-jordan-zassenhaus>
#idx("Jordan-Zassenhaus Theorem", target: [@th:local-jordan-zassenhaus])

This result can be proved in exactly the same manner as the global version
@th:jordan-zassenhaus. Indeed, the local result is somewhat simpler, and follows
from @bib:Reiner1975[MO §26] or @bib:CurtisReiner1962[CR §79] by slightly
modifying the proofs given in these references. It should also be observed that
the result follows directly from Maranda's
Theorem~@th:maranda-lattice-isomorphism, assuming that $A$ is a separable
$K$-algebra (see Remark (ii) of @rem:maranda-lattice-finiteness).

#remarks(name: "Notes", numbered: false)[
  #enum(
    numbering: "(1)",
    [For a proof of @th:jordan-zassenhaus when $K$ is a function field, see also
      Higman-McLaughlin~@bib:Higman1959a.],
    [If $K$ is not a global field, the Jordan-Zassenhaus Theorem need not hold
      for $Lambda$-lattices. Even when $R$ is a complete d.v.r., there exist
      counterexamples in case $R$ has infinite residue class field. For example,
      see Roggenkamp~@bib:Roggenkamp1970.],
    [Plesken~@bib:Plesken1977 considers the number of classes of full
      $R G$-lattices in an absolutely simple $K G$-module $V$, in the case where
      $K$ is arbitrary and $char K divides.not |G|$. He proves that this number
      is finite if and only if $R$ has finite class number.],
  )
]

#exercises-heading

#exercise[
  Let $Lambda$ be an $R$-order in a semisimple $K$-algebra $A$. Show that the
  left class number of $Lambda$ equals the right class number of $Lambda$. In
  other words, let $cal(L)$ be the set of “fractional” left ideals of $Lambda$,
  that is, the set of all full left $Lambda$-lattices in $A$. Let $cal(R)$ be
  the set of all fractional right ideals. Then show that there is a bijection
  between the set of $Lambda$-isomorphism classes in $cal(L)$ and the
  corresponding set for $cal(R)$.

  #source(560)
  #hint([@exc:left-right-order-class-number])[
    For each $L in cal(L)$, let $L^*=Hom_R lr((L,R))$, viewed as right
    $Lambda$-lattice. Then $K times.o_R L^*=Hom_K lr((A,K))$, and
    $ Hom_K lr((attach(A, bl: A),K)) tilde.equiv attach(A, br: A) $
    since $A$ is a Frobenius algebra over $K$ (see
    @prop:eilenberg-nakayama-symmetric-semisimple). Thus we may identify $L^*$
    with a full right $Lambda$-lattice in $A$. Since $L tilde.equiv (L^*)^*$,
    the correspondence $L in cal(L) arrow.l.r L^* in cal(R)$ gives the desired
    bijection.
  ]
] <exc:left-right-order-class-number>

#exercise[
  Let $M$ be an $R$-lattice as in @def:left-right-order, $S$ a Dedekind domain
  containing $R$. Prove that
  $ O_l lr((S times.o_R M))=S times.o_R O_l lr((M)). $

  #hint([@exc:order-scalar-extension])[
    Use @th:change-of-rings.
  ]
] <exc:order-scalar-extension>

#exercise[
  Let $alpha$ be a nonunit of the Dedekind domain $R$, and let $L$ be an
  $R$-lattice such that $L=alpha L$. Show that $L$ must equal $0$.

  #hint([@exc:nonunit-invariant-lattice-zero])[
    Choose a maximal ideal $P$ of $R$ containing $alpha$, and let the subscript
    $P$ indicate localization at $P$. Then $L_P=alpha L_P$ gives $L_P=P L_P$,
    whence $L_P=0$ by Nakayama's Lemma. Therefore $P+"ann"_R L=R$ by
    Exercise~@exc:localization-zero-annihilator, a contradiction since $L$ is
    $R$-torsionfree. This same argument works for $R$ any integral domain, and
    $L$ any f.g. torsionfree $R$-module.
  ]
] <exc:nonunit-invariant-lattice-zero>

#exercise[
  Let $Lambda$ be an $R$-order in a f.d. $K$-algebra $A$, and let $x in A^dot$.
  Prove that
  $ O_l lr((Lambda x))=Lambda. $

  #hint([@exc:left-order-principal-lattice])[
    Let $y in A$. Then
    $
      y in O_l lr((Lambda x)) arrow.l.r y Lambda x subset.eq Lambda x
      arrow.l.r y Lambda subset.eq Lambda arrow.l.r y in Lambda.
    $
  ]
] <exc:left-order-principal-lattice>
