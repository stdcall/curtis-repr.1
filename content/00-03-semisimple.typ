#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/03-semisimple.typ": *

#heading(level: 2)[
  Semisimple Rings and Modules. The Wedderburn and Morita Theorems
] <sec:semisimple-rings-modules>

#source(62)
This section begins by reviewing finiteness conditions for rings and modules.
Next comes the theory of semisimple modules and rings, including the Wedderburn
Theorems and the Chevalley–Jacobson Density Theorem. Applications are given to
finite dimensional algebras over fields, and in particular, to the theory of
group representations. An account of the Morita theorems for categories of
modules is given, with applications to tensor products of simple algebras and
modules.

=== Finiteness Conditions <ss:finiteness-conditions>

The definition and elementary properties of noetherian and artinian rings and
modules will be sketched without proofs. Modules satisfying both finiteness
conditions have composition series, and an important numerical invariant (the
length of such a module) is introduced, as well as the possibility of analyzing
modules of finite lengths in terms of simple modules.

#proposition[
  Let $M$ be a left module over a ring $A$. The following conditions are
  equivalent:
  #enum(
    numbering: "(a)",
    [The submodules of $M$ satisfy the _ascending chain condition_#idx(
        "A. C. C. = ascending chain condition",
      ) (ACC): For every increasing sequence of submodules of $M$,
      $ M_1 subset.eq M_2 subset.eq dots, $
      there exists an integer $n$ such that $M_n = M_(n+1) = dots$.],
    [The submodules of $M$ satisfy the _maximum condition_#idx(
        "maximal condition",
      ): every non-empty set of submodules, partially ordered by inclusion, has
      a maximal element.],
    [Every submodule of $M$ is finitely generated.],
  )
] <prop:noetherian-module-criteria>

#definition[
  A left $A$-module satisfying any one of the equivalent conditions stated in
  @prop:noetherian-module-criteria is called a _noetherian module_. A ring $A$
  whose left regular module $attach(A, bl: A)$ is noetherian is called a _left
  noetherian ring_#idx(
    "noetherian ring",
  ) (with a similar definition for a _right noetherian ring_).
] <def:noetherian-module-ring>
#idx(
  "noetherian module",
  target: [@def:noetherian-module-ring],
)

Principal ideal domains, and (by the Hilbert Basis Theorem) polynomial rings
$R[X_1,dots,X_n]$ over a left noetherian ring $R$, are examples of left
noetherian rings. Noetherian modules can often be identified by the following
result:

#proposition[
  A finitely generated left module over a left noetherian ring is noetherian.
  (For a proof see @bib:CurtisReiner1962[CR §~11]).
] <prop:finitely-generated-noetherian>

#corollary[
  Let $A$ be an algebra over a commutative noetherian ring $R$, such that $A$ is
  a finitely generated left $R$-module. Then every finitely generated left
  $A$-module is noetherian.
] <cor:noetherian-finite-algebra-modules>

#source(63)
Another finiteness condition on rings and modules is described in the following
result:

#proposition[
  Let $A$ be an arbitrary ring, and let $M$ be a left $A$-module. The following
  conditions are equivalent:
  #enum(
    numbering: "(i)",
    [The submodules of $M$ satisfy the _descending chain condition_#idx(
        "D. C. C. = descending chain condition",
      ) (DCC): for every descending sequence of submodules of $M$,
      $ M_1 supset.eq M_2 supset.eq dots, $
      there exists an integer $k$ such that $M_k=M_(k+1)=dots$.],
    [The submodules of $M$ satisfy the _minimum condition_#idx(
        "minimum condition",
      ): every non-empty family of submodules, viewed as a partially ordered set
      under inclusion, has a minimal element.],
  )
] <prop:artinian-module-criteria>

#definition[
  A left $A$-module $M$ is called _artinian_ in case its submodules satisfy the
  DCC, or equivalently, the minimum condition. A _left artinian ring_#idx(
    "artinian ring",
  ) is a ring $A$ whose left regular module $attach(A, bl: A)$ is artinian.
] <def:artinian-module-ring>
#idx(
  "artinian module",
  target: [@def:artinian-module-ring],
)

The following criterion will be used repeatedly in practice:

#proposition[
  Every f.g. left module $M$ over a left artinian ring $A$ is both artinian and
  noetherian.
] <prop:artinian-finitely-generated-modules>

#proof[
  Hopkin's Theorem#idx(
    "Hopkin's Theorem",
  ) (see @bib:CurtisReiner1962[CR (54.1)]) states that every left artinian ring
  is necessarily left noetherian. Thus $M$ is a noetherian module by
  @prop:finitely-generated-noetherian. But since $A$ is artinian, so is $M$ (see
  @bib:CurtisReiner1962[CR (11.15)], for example).
]

#definition[
  A left $A$-module $P$ is _simple_ (or _irreducible_) in case $P != 0$, and the
  only submodules of $P$ are $P$ and $0$. A left $A$-module $M$ has a
  _composition series_#idx(
    "composition series",
  ) if there exists a descending chain of submodules of $M$:
  $ M=M_1 supset M_2 supset dots supset M_s supset M_(s+1)=0, $
  such that the factor modules ${M_i slash M_(i+1): 1 <= i <= s}$ are simple.
  The modules ${M_i slash M_(i+1)}$ are called the _factors_#idx(
    "composition factors",
  ) of the composition series, and the number of factors (in this case $s$) is
  called the _length_ of the composition series#idx(
    "length of composition series",
  ). (See @th:jordan-holder for finite groups.)
] <def:simple-module-composition-series>
#idx(
  "simple module",
  target: [@def:simple-module-composition-series],
)

#proposition[
  A necessary and sufficient condition for a left $A$-module to have a
  composition series is that it be both left noetherian and left artinian. In
  case this occurs, any two composition series have the same length. (For a
  proof see @bib:CurtisReiner1962[CR §~11].)
] <prop:composition-series-finiteness>

#source(64)
#definition[
  Let $M$ be a left $A$-module with a composition series. The length of a
  composition series of $M$ is called the _length of_ $M$, and is denoted by
  $l(M)$.
] <def:module-length>
#idx(
  "length of composition series",
  target: [@def:module-length],
)

Proposition~@prop:composition-series-finiteness shows that the length of a
module with a composition series is independent of the choice of the composition
series, and is therefore a numerical invariant of the module.

#theorem(name: "Jordan–Hölder Theorem")[
  Suppose $M$ is a module having two composition series. Then the numbers of
  factors in the two series are the same, and a bijection from one set of
  factors to the other can be defined in such a way that corresponding factors
  are isomorphic.
] <th:module-jordan-holder>
#idx(
  "Jordan-Holder Theorem",
  target: [@th:module-jordan-holder],
)

=== Semisimple Modules and Rings <ss:semisimple-modules-rings>

The least complicated behavior of a left $A$-module $M$ with reference to simple
submodules is described by the following result:

#proposition[
  Let $M$ be a left $A$-module over an arbitrary ring $A$. The following
  statements are equivalent:
  #enum(
    numbering: "(i)",
    [$M = op("⨁", limits: #true)_(i in I) M_i$ for some family ${M_i}_(i in I)$
      of simple submodules of $M$.],
    [$M = sum_(j in J) M_j$ for some family ${M_j}_(j in J)$ of simple
      submodules.],
    [For every submodule $M' subset.eq M$, there exists a submodule
      $M'' subset.eq M$ such that $M=M' plus.o M''$.],
  )
] <prop:semisimple-module-criteria>

The proof is available in many places, for example in @bib:CurtisReiner1962[CR
  §~12]. Notice that no finiteness conditions are assumed in
Proposition~@prop:semisimple-module-criteria; note also that (i) implies the
existence of simple submodules of $M$.

#definition[
  A left $A$-module satisfying the conditions of
  @prop:semisimple-module-criteria is called a _semisimple module_ (or a
  _completely reducible module_#idx(
    "completely reducible",
  ), as in @bib:CurtisReiner1962[CR], for example).
] <def:semisimple-module>
#idx(
  "semisimple module",
  target: [@def:semisimple-module],
)

Some important examples of semisimple modules are (i) vector spaces over fields
or division rings, and (ii) finitely generated modules $M$ over a principal
ideal domain $R$, where $op("ann")_R lr((M))=R alpha$ for an element $alpha$
which is a product of distinct primes. (See
Exercise~@exc:pid-squarefree-semisimple.)

The following basic result concerning the semisimplicity of modules over group
algebras illustrates the use of condition @prop:semisimple-module-criteria
(iii).

#theorem(name: "Maschke's Theorem")[
  Let $K G$ be the group algebra of a finite group $G$ over a field $K$ (see
  @exm:algebras (ii)). Assume that $|G| != 0$ in $K$, that is, $|G|$ is not a
  #source(65)
  multiple of the characteristic of $K$. Then every f.g. left $K G$-module $M$
  is semisimple.
] <th:maschke>
#idx(
  "Maschke's Theorem",
  target: [@th:maschke],
)

#proof(head: emph[Sketch of Proof.])[
  Let $N$ be a $K G$-submodule of $M$, so $N$ is a $K$-subspace of $M$ such that
  $x N subset.eq N$ for all $x in G$. By linear algebra, there exists a
  $K$-subspace $N'$ of $M$ such that $M=N plus.o N'$. Let $E in End_K lr((M))$
  be the projection of $M$ onto $N$ arising from this direct sum decomposition.
  Then $E M subset.eq N$, and $E|_N=1_N$ ($= "identity map on" N$). The idea is
  to find an element $E^* in End_(K G) lr((M))$ satisfying these same
  conditions; in that case, $(1-E^*)M$ will be the required $K G$-complement of
  $N$ in $M$.

  The solution arises from setting
  $ E^* = |G|^(-1) sum_(x in G) x E x^(-1). $
  For each $y in G$, we have
  $ y E^* y^(-1)=|G|^(-1) sum_(x in G) y x E (y x)^(-1)=E^*, $
  so $E^* in End_(K G) lr((M))$. Further, $E^* M subset.eq N$ and $E^*|_N=1$, as
  is easily checked. Therefore $E^*$ is the required $K G$-projection of $M$
  onto $N$, which completes the proof that $M$ is semisimple.
]

It is natural to ask what can be said about rings (or algebras) for which
_every_ f.g. module is semisimple, as in the case of group algebras considered
in Maschke's theorem.

#proposition[
  The following conditions concerning a ring $A$ are equivalent:
  #enum(
    numbering: "(i)",
    [Every left $A$-module is semisimple.],
    [Every f.g. left $A$-module is semisimple.],
    [The left regular module $attach(A, bl: A)$ is semisimple, and is a direct
      sum $A=L_1 plus.o dots plus.o L_m$ of a finite number of
      _minimal_#footnote[A minimal left ideal of $A$ is a nonzero left ideal $L$
        which does not properly contain any nonzero left ideals, that is, $L$ is
        a simple submodule of the left regular module $attach(A, bl: A)$.] left
      ideals ${L_1,dots,L_m}$.],
  )
] <prop:semisimple-ring-criteria>

#proof[
  Clearly (i)$arrow.r.double$(ii). Assume (ii). Then $attach(A, bl: A)$ is
  finitely generated (because $A=A dot 1$) and thus is semisimple, so that by
  @prop:semisimple-module-criteria
  $ A = op("⨁", limits: #true)_(i in I) L_i $
  for some family ${L_i}_(i in I)$ of minimal left ideals. Let
  $ 1=l_(i_1)+dots+l_(i_n), $
  #source(66)
  with $l_(i_j) in L_(i_j)$, for some indices ${i_j}$ in $I$. Then each $a in A$
  can be expressed in the form
  $ a=a l_(i_1)+dots+a l_(i_n), $
  and hence $A=L_(i_1)+dots+L_(i_n)$, and (iii) follows.

  Finally assume (iii), and let $M$ be an arbitrary left $A$-module. Then
  $ M=A M=sum_(m in M) sum_(i in I) L_i m. $
  By @prop:semisimple-module-criteria it is sufficient to prove that each
  submodule $L_i m$ is either zero or simple. This is clear, because for each
  $L_i$ and $m in M$, there exists a surjection of $A$-modules
  $phi: L_i -> L_i m$, given by $phi(l)=l m$, $l in L_i$. The assertion about
  $L_i m$ then follows from the fundamental theorem on homomorphisms because
  $L_i$ is simple. This completes the proof.
]

#definition[
  A ring $A$ is _(left) semisimple_ if $A$ satisfies any one of the conditions
  of @prop:semisimple-ring-criteria.
] <def:semisimple-ring>
#idx(
  "semisimple ring",
  target: [@def:semisimple-ring],
)

The basic problems concerning semisimple rings are to classify their simple
modules, and to determine the structure of the rings themselves. We begin with a
result showing that the simple modules are all isomorphic to left ideals
generated by idempotents. We first require a basic lemma.

#lemma(name: "Schur's Lemma")[
  Let $M$ be a simple $A$-module over an arbitrary ring $A$. Then
  $End_A lr((M))$ is a division ring.
] <lem:schur>
#idx(
  "Schur's Lemma",
  target: [@lem:schur],
)

#proof(head: emph[Sketch of Proof.])[
  Let $f != 0$ be an element of $End_A lr((M))$. Since $M$ is simple, the
  fundamental homomorphism theorem implies that $f$ is an $A$-automorphism of
  $M$, and hence is invertible. Therefore $End_A lr((M))$ is a division ring.
]

An _idempotent_#idx(
  "idempotent",
) is a nonzero element $e$ of a ring $A$ such that $e^2=e$.

#proposition[
  Let $A$ be a semisimple ring. Then the following statements hold.
  #enum(
    numbering: "(i)",
    [Every nonzero left ideal $L$ in $A$ is generated by an idempotent: $L=A e$
      for some idempotent $e in A$.],
    [Every element $f in Hom_A lr((L,A))$ is given by a right multiplication:
      $f=a_r$, for some $a in A$.],
    [A left ideal $A e$ generated by an idempotent $e$ is simple if and only if
      $e A e$ is a division ring.],
    [Every simple left $A$-module is isomorphic to a left ideal in $A$.],
  )
] <prop:semisimple-left-ideals>

#source(67)
#proof[
  #enum(
    numbering: "(i)",
    [By semisimplicity, we may write $A=L plus.o L'$ for a left ideal $L'$, and
      put $1=e+e'$, with $e in L$, $e' in L'$. Then $e=e^2+e e'$, and
      $e-e^2=e e' in L inter L'=0$. Therefore $e^2=e$, and for all $x in L$,
      $x=x e+x e'$, and $x-x e=x e' in L inter L'=0$, so that $L=A e$ as
      required. Note that $e != 0$ since $L != 0$.],
    [Let $f in Hom_A lr((A e,A))$, where $e^2=e$. Then, setting $a=f(e)$, we
      have
      $ f(x)=f(x e)=x f(e)=x a, $
      for all $x in A e$, using the fact that $e$ acts as a right identity
      operator on $A e$. We have thus shown that $f=a_r$, as required.],
  )
]

Before proving (iii), we need one more general lemma.

#lemma[
  Let $e$ be an idempotent in an arbitrary ring $A$. Then
  $ End_A lr((A e)) tilde.equiv (e A e)^circle.small quad "(opposite ring)." $
] <lem:idempotent-corner-endomorphisms>

#proof[
  Let $f in End_A lr((A e))$. Then $f=a_r$, for $a=f(e)$ (see the proof of
  @prop:semisimple-left-ideals (ii)). It follows that $f=(e a e)_r$, because
  $ f(x)=x a=x e a e, quad "for" x in A e "and" f(x) in A e. $
  It is then easily checked that the map $f -> e f(e)e$ is an anti-isomorphism
  of $End_A lr((A e))$ to $e A e$, and the lemma is proved.
]

We now return to the proof of @prop:semisimple-left-ideals.

#proof[
  #enum(
    numbering: "(i)",
    start: 3,
    [First assume that $L=A e$ is a simple $A$-module. By Schur's
      Lemma~@lem:schur, $End_A lr((A e))$ is a division ring, and hence by
      Lemma~@lem:idempotent-corner-endomorphisms, $e A e$ is also a division
      ring. Conversely, suppose $L=A e$ is not simple. Then $L$ contains a
      nonzero proper submodule $L_1$, and $L=L_1 plus.o L'_1$ by semisimplicity,
      where $L'_1$ is also a nonzero proper submodule of $L$. The projections
      associated with this direct decomposition belong to $End_A lr((L))$, and
      are nonzero elements whose product is zero. Therefore $End_A lr((L))$ is
      not a division ring, and by Lemma~@lem:idempotent-corner-endomorphisms,
      $e A e$ is not a division ring.],
    [Let $M$ be a simple left $A$-module, and let $A=sum L_i$ for simple left
      ideals ${L_i}$. Then $M=A M=sum L_i M$, and some $L_i M != 0$. It follows
      that $L_i m != 0$ for some $m in M$, and because $M$ is simple, we have
      $L_i m=M$. The map $x -> x m$, $x in L_i$, is an $A$-surjection of $L_i$
      onto $M$; it is an isomorphism because $L_i$ is simple (thereby forcing
      the kernel to be zero).],
  )
]

The next step in analyzing semisimple rings and modules is to sort the simple
modules into isomorphism classes; for example, the question arises as to whether
a semisimple ring has only a finite number of nonisomorphic simple modules. As
an exercise the reader can easily settle this point using
#source(68)
@prop:semisimple-left-ideals and the Jordan–Hölder Theorem. A key result on this
type of question is the following general proposition about semisimple modules:

#proposition[
  Let $M$ be a semisimple left $A$-module over an arbitrary ring $A$. Let
  ${M_i}_(i in I)$ be a set of representatives of the isomorphism classes of
  simple submodules, and let
  $ H_i=sum_(P tilde.equiv M_i, P subset.eq M) P. $
  Then the following statements hold:
  #enum(
    numbering: "(i)",
    [$M=op("⨁", limits: #true)_(i in I) H_i$.],
    [Every simple submodule of $H_i$ is isomorphic to $M_i$.],
    [$Hom_A lr((H_i,H_(i')))=0$ if $i != i'$.],
    [Let $M=op("⨁", limits: #true)_(j in J) P_j$ be an arbitrary direct
      decomposition of $M$ into simple submodules $P_j$, and for each $i in I$,
      let $tilde(H)_i=sum_(j in J,P_j tilde.equiv M_i) P_j$. Then
      $tilde(H)_i=H_i$ for all $i in I$.],
  )
] <prop:homogeneous-decomposition>

#proof[
  We shall prove several statements which, taken together, will establish the
  proposition.

  (a) Let $M=op("⨁", limits: #true)_(j in J) P_j$, for a set of simple
  submodules ${P_j}$, and let $Q$ be an arbitrary simple submodule of $M$. Then
  $Q tilde.equiv P_j$ for some $j in J$. _Proof of (a)._ Let ${pi_j}_(j in J)$
  be the projections associated with the direct decomposition
  $M=op("⨁", limits: #true) P_j$. Then $pi_j lr((Q)) != 0$ for some $j$, and it
  follows that $pi_j|_Q: Q -> P_j$ is an isomorphism because both $Q$ and $P_j$
  are simple.

  (b) Let $tilde(H)_i=sum_(j in J,P_j tilde.equiv M_i) P_j$, as in (iv). Then
  $M=op("⨁", limits: #true)_(i in I) tilde(H)_i$, and every simple submodule of
  $tilde(H)_i$ is isomorphic to $M_i$, for all $i in I$. _Proof of (b)._ The
  first part of (b) follows from the definition of direct sum, and the second
  statement follows from (a), applied to $tilde(H)_i$.

  (c) Let $Q$ be an arbitrary simple submodule of $M$. Then $Q tilde.equiv M_i$
  for a unique $i in I$, and $Q subset.eq tilde(H)_i$. _Proof of (c)._ Let
  $q in Q$, and write
  $ q=sum_(j in J) q_j, quad q_j in P_j. $
  The proof of (a) shows that if any summand $q_j != 0$, then
  $pi_j lr((Q)) != 0$, and $Q tilde.equiv P_j$. Therefore $q_j=0$ unless
  $P_j tilde.equiv M_i$, and hence $q in tilde(H)_i$.

  #source(69)
  (d) Let $f in Hom_A lr((tilde(H)_i,tilde(H)_(i')))$ for $i != i'$. Then $f=0$.
  _Proof of (d)._ If $f != 0$, then $f(P) != 0$ for some simple submodule $P$ of
  $tilde(H)_i$, and it follows that $f(P)$ is a simple submodule of
  $tilde(H)_(i')$ isomorphic to $P$. These statements contradict (c), and
  therefore $f=0$.

  Statements (a)–(d) now show that $tilde(H)_i=H_i$ for each $i in I$, and also
  imply the other statements of the proposition.
]

#definition[
  Let $M$ be a semisimple left $A$-module, and ${M_i}_(i in I)$ a set of
  representatives of the isomorphism classes of simple left $A$-modules of $M$.
  The submodules ${H_i}_(i in I)$ defined in @prop:homogeneous-decomposition are
  called the _homogeneous components_#idx(
    "homogeneous components",
  ) of $M$ (or the _isotypic components of type_#idx(
    "isotypic components",
  ) $M_i$).
] <def:homogeneous-components>

A ring with identity element is called _simple_#idx(
  "simple ring",
) if it has no nonzero proper two-sided ideals. The first main structure theorem
on semisimple rings can now be stated.

#theorem(title: [Wedderburn])[
  Let $A$ be a left semisimple ring. The number of homogeneous components
  ${A_i}$ of the left regular module $attach(A, bl: A)$ is finite, and $A$ is
  their direct sum:
  $ A=A_1 plus.o dots plus.o A_m. $
  Each homogeneous component $A_i$ is a two-sided ideal in $A$, and
  $A_i A_(i')=0$ if $i != i'$. Moreover, each $A_i$ is a simple artinian ring
  (with identity element).
] <th:wedderburn-semisimple-decomposition>
#idx(
  "Wedderburn's Theorems (on simple and semisimple rings)",
  target: [@th:wedderburn-semisimple-decomposition],
)

#proof[
  From @prop:semisimple-ring-criteria (iii), the left regular module is a finite
  direct sum of minimal left ideals. By statement (a) in the proof of
  @prop:homogeneous-decomposition, every simple left $A$-module is isomorphic to
  one of these summands, and it follows that the number of homogeneous
  components of $attach(A, bl: A)$ is finite.

  Let $L$ be a minimal left ideal contained in $A_i$, and let $a in A_(i')$,
  with $i' != i$. Then $L a subset.eq A_(i')$ because $A_(i')$ is a left ideal,
  and $L a$ is either zero or a minimal left ideal isomorphic to $L$. Because
  $A_i$ and $A_(i')$ are different homogeneous components, we have $L a=0$.
  Therefore $A_i A_(i')=0$ if $i != i'$, and the ${A_i}$ are two-sided ideals in
  $A$.

  Letting $1=e_1+dots+e_m$, with $e_i in A_i$, $1 <= i <= m$, the proof of
  @prop:semisimple-left-ideals shows that $A_i=A e_i=e_i A$ (using the fact that
  $A_i$ is a two-sided ideal), and that $e_i^2=e_i$, $1 <= i <= m$; this proves
  that the ${e_i}$ are identity elements in the ideals $A_i$ to which they
  belong.

  Finally, let $S$ be a nonzero two-sided ideal in $A_i$, for some $i$. Because
  $A_i A_(i')=0$ if $i != i'$, it follows that $S$ is a two-sided ideal in $A$.
  Let $L$ be a minimal left ideal contained in $S$, and let $L'$ be another
  minimal left ideal contained in $A_i$. Then $L tilde.equiv L'$, and by
  @prop:semisimple-left-ideals, $L'=L a$ for some $a in A$. Because $S$ is a
  two-sided ideal in $A$, $L' subset.eq S$, and it follows that $S=A_i$, because
  $A_i$ is the sum of all simple left ideals isomorphic to $L$. Therefore $A_i$
  is a simple ring,
  #source(70)
  and is artinian because it is a finite direct sum of simple modules, and hence
  has a composition series. This completes the proof.
]

#definition[
  The ideals ${A_i}$ defined in Theorem~@th:wedderburn-semisimple-decomposition
  are called the _Wedderburn components_ of $A$.
] <def:wedderburn-components>
#idx(
  "Wedderburn components",
  target: [@def:wedderburn-components],
)

The preceding result shows that the multiplicative structure of a semisimple
ring is determined by the structure of simple artinian rings. Among the many
ways of proving the main structure theorem on simple artinian rings, we shall
follow Jacobson's original proof of the density theorem (for another proof, see
@bib:CurtisReiner1962[CR §~26]; a more general version of that argument appears
later in this section, in §@ss:morita-theorems on the Morita Theorems).

The first two results about simple rings clarify their connections with
semisimple rings, and set up a situation leading to the density theorem.

#proposition[
  Every simple artinian ring $A$ is semisimple.
] <prop:simple-artinian-semisimple>

#proof[
  Let $L$ be a minimal left ideal of $A$; then $B=sum_(a in A) L a$ is a
  semisimple submodule of $attach(A, bl: A)$, and coincides with $A$ because $B$
  is a non-zero two-sided ideal of $A$. Therefore $attach(A, bl: A)$ is a
  semisimple module, and $A$ is semisimple.
]

#proposition[
  Let $A$ be a simple artinian ring. Then $A$ is isomorphic to a subring $A_l$
  of the endomorphism ring of an abelian group $M$, where $M$ is a simple
  $A$-module. Moreover, $A_l subset.eq End_D lr((M))$, where $D=End_A lr((M))$
  is a division ring.
] <prop:simple-artinian-faithful-action>
#idx(
  "simple artinian ring (structure theorem)",
  target: [@prop:simple-artinian-faithful-action],
)#idx(
  "Wedderburn's Theorems (on simple and semisimple rings)",
  target: [@prop:simple-artinian-faithful-action],
)

#proof[
  Let $M$ be a minimal left ideal in $A$, (such an $M$ exists by the minimum
  condition.) The map $a -> a_l$, $a in A$, is a homomorphism $A -> A_l$ from
  $A$ into the endomorphism ring of $M$. Because $A$ is simple,
  $A tilde.equiv A_l$. Finally, $D=End_A lr((M))$ is a division ring by Schur's
  Lemma because $M$ is a simple module.
]

The structure of a ring of linear transformations over a division ring
satisfying the conditions in @prop:simple-artinian-faithful-action is determined
by the density theorem.

#definition[
  A ring of linear transformation on a left vector space $M$ over a division
  ring $D$ is called a _dense ring of linear transformations_, if, for every
  $k=1,2,dots$, and every set of $2 k$ elements of $M$,
  ${x_1,dots,x_k; y_1,dots,y_k}$, with ${x_1,dots,x_k}$ linearly independent
  over $D$, and ${y_1,dots,y_k}$ arbitrary, there exists an element $a in A$
  such that $a x_i=y_i$, $i=1,2,dots,k$.
] <def:dense-linear-transformations>
#idx(
  "dense ring of linear transformations",
  target: [@def:dense-linear-transformations],
)

#theorem(name: "Density Theorem")[
  Let $A$ be a subring of the endomorphism ring of an abelian group $M$,
  $A subset.eq End_ZZ lr((M))$, such that $M$ is a simple left $A$-module. Then
  $D=End_A lr((M))$ is a division ring, and $A$ is a dense ring of linear
  transformations on the vector space $M$ over $D$.
] <th:density>
#idx(
  "Density Theorem",
  target: [@th:density],
)

#source(71)
#proof[
  (Jacobson~@bib:Jacobson1945a). We use induction on $k$, starting from an
  arbitrary set of $2 k$ elements ${x_1,dots,x_k;y_1,dots,y_k}$, as in
  @def:dense-linear-transformations, with $x_1,dots,x_k$ linearly independent.
  First, let $k=1$. In this case, $x_1 != 0$, and $A x_1 != 0$, so that
  $A x_1=M$ because $M$ is simple. Therefore $y_1=a x_1$ for some $a in A$.

  Next, let $k=2$. First we prove that there exists $a_2 in A$ such that
  $a_2 x_1=0$, and $a_2 x_2 != 0$. If no such $a_2 in A$ exists, then
  $a x_1 -> a x_2$, for $a in A$, is a well-defined map from $A x_1$ to $A x_2$,
  and is an $A$-endomorphism of $M$ because $A x_1=A x_2=M$, again because $M$
  is simple. Therefore $a x_1 -> a x_2$ is given by left multiplication by some
  $delta in D=End_A lr((M))$, and in particular, $x_2=delta x_1$, contradicting
  the linear independence of $x_1$ and $x_2$. Thus $a_2$ exists. Similarly there
  exists $a_1 in A$ such that $a_1 x_1 != 0$, $a_1 x_2=0$. By the case $k=1$,
  there exist $b_1,b_2 in A$ such that $b_1 a_1 x_1=y_1$ and $b_2 a_2 x_2=y_2$.
  Then $a=b_1 a_1+b_2 a_2$ satisfies our requirements.

  Now let $k$ be arbitrary. We assume $k>2$, and that the result holds for any
  set of $2 m$ elements of the required sort, with $m<k$. By the argument in the
  case $k=2$, it is sufficient to find $a_k in A$ such that
  $a_k x_1=dots=a_k x_(k-1)=0$, and $a_k x_k != 0$. By induction, there exists
  an element $b in A$ such that
  $ b x_1=dots=b x_(k-2)=0, quad b x_k != 0. $
  Now let $B subset.eq A$ be the set of all such elements $b$. If either
  $b x_(k-1)=0$ or $b x_(k-1)$ and $b x_k$ are linearly independent, then it is
  easy to construct the required $a_k$, using the case $k=2$ in the second case
  to find $c in A$ with $c b x_(k-1)=0$, $c b x_k != 0$ and putting $a_k=c b$.
  Therefore we may assume that $b x_(k-1)=beta b x_k$ for some $beta != 0$ in
  $D$. Then $x_(k-1)-beta x_k != 0$, and by induction there exists $d in A$ with
  $d x_1=dots=d x_(k-2)=0$, $d(x_(k-1)-beta x_k) != 0$. If $d x_k=0$ (and hence
  $d x_(k-1) != 0$), there exists $u in A$ such that $u d x_(k-1)=b x_(k-1)$.
  Then, for $a_k=b-u d$, we have
  $ a_k x_1=dots=a_k x_(k-1)=0, quad a_k x_k=b x_k != 0. $
  So we may assume that $d x_k != 0$, and hence $d in B$. If either
  $d x_(k-1)=0$ or $d x_(k-1)$ and $d x_k$ are $D$-independent, then the
  previous discussion applies.

  So we may suppose that $d x_(k-1)=delta d x_k$, for $delta != 0$. Then
  $delta != beta$. We can find $v in A$ such that
  $ v d x_(k-1)=b x_(k-1). $
  Then
  $
    v d x_k=v d delta^(-1) x_(k-1)=delta^(-1) v d x_(k-1)
    =delta^(-1) b x_(k-1)=delta^(-1) beta b x_k,
  $
  and hence $(v d-delta^(-1) beta b)x_k=0$. Now put $a_k=b-v d$, then
  $ a_k x_1=dots=a_k x_(k-1)=0 $
  and $a_k x_k=(b-v d)x_k != 0$, because $(v d-delta^(-1) beta b)x_k=0$ and
  $delta^(-1) beta != 1$. This completes the proof.
]

#source(72)
The first application of the Density Theorem completes our present discussion of
semisimple rings.

#theorem(name: "Main Structure Theorem on Simple Artinian Rings")[
  Let $A$ be a simple artinian ring. Then $A tilde.equiv End_D lr((M))$, for a
  finite dimensional left vector space $M$ over a division ring $D$.
] <th:simple-artinian-structure>
#idx(
  "simple artinian ring (structure theorem)",
  target: [@th:simple-artinian-structure],
)#idx(
  "Wedderburn's Theorems (on simple and semisimple rings)",
  target: [@th:simple-artinian-structure],
)

#proof[
  Let $M$ be a minimal left ideal in $A$. By
  Prop.~@prop:simple-artinian-faithful-action,
  $A tilde.equiv A_l subset.eq End_ZZ lr((M))$, $D=End_A lr((M))$ is a division
  ring, and $A subset.eq End_D lr((M))$. By the Density Theorem~@th:density,
  $A_l$ is a dense ring of linear transformations on $M$ over $D$. It is
  sufficient to prove that $dim_D lr((M)) < infinity$. If this is not the case,
  there exists an infinite sequence $x_1,x_2,dots$ of linearly independent
  elements of $M$. For each $j=1,2,dots$, let
  $I_j={a in A_l: a x_1=dots=a x_j=0}$. Then the ${I_j}$ are left ideals, and
  $ I_1 supset.eq I_2 supset.eq dots. $
  Moreover, the inclusions $I_j supset.eq I_(j+1)$ are strict, because of the
  Density Theorem, and we have contradicted the assumption that $A$ is artinian.
  This completes the proof.
]

The converse of @th:simple-artinian-structure, that $M_n lr((D))$ is simple and
artinian, and the uniqueness of $D$ and $dim_D lr((M))$ in
Theorem~@th:simple-artinian-structure, are sketched in
Exercises~@exc:matrix-ring-structure and~@exc:wedderburn-uniqueness.

#heading(level: 3)[
  Semisimple Algebras over Fields. The Theorems of Burnside and Frobenius–Schur
] <ss:semisimple-algebras-fields>

In this section we apply the results of §@ss:finiteness-conditions,
@ss:semisimple-modules-rings to investigate algebras which act on semisimple
modules. It will not be necessary to assume that the algebras themselves are
semisimple, and in fact we shall later apply these results to non-semisimple
algebras.

Throughout this section, $A$ denotes a finite dimensional algebra over a field
$K$. All $A$-modules under consideration are assumed to be finitely generated
over $A$, and hence are finite dimensional $K$-spaces. For such a left
$A$-module $M$, $End_A lr((M))$ is a subalgebra of $End_K lr((M))$; thus
$End_A lr((M))$ is a finite dimensional $K$-algebra, called the
_centralizer_#idx(
  "centralizer",
) (or _commutant_#idx(
  "commutant",
)) of $M$. Finally, we recall that there is a homomorphism of $K$-algebras
$lambda: A -> A_l subset.eq End_K lr((M))$, given by $lambda(a)=a_l$, $a in A$,
where $a_l lr((m))=a m$ for $m in M$.

#definition[
  A left $A$-module $M$ is _faithful_ if $op("ann") M={0}$, where
  $op("ann") M={a in A: a M=0}$.
] <def:faithful-module>
#idx(
  "faithful",
  target: [@def:faithful-module],
)

Evidently $M$ is a faithful left $A$-module if and only if $lambda: A -> A_l$ is
an isomorphism of $K$-algebras, because $op("ann") M=ker lambda$.

#source(73)
#lemma[
  (Bourbaki~@bib:Bourbaki1958[p.~26]). Let $M$ be a faithful left $A$-module,
  and let ${x_j: 1 <= j <= s}$ be a set of generators of $M$ as a module over
  $End_A lr((M))$. Then the map $attach(A, bl: A) -> M^((s))$ defined by
  $ a -> (a x_1,dots,a x_s), quad a in A, $
  is a monomorphism of left $A$-modules.
] <lem:faithful-regular-embedding>

#proof[
  The map is clearly an $A$-homomorphism. Suppose $a$ is in the kernel. Then
  $a x_j=0$ for all $j$, whence for every set ${c_1,dots,c_s}$ of elements
  belonging to $End_A lr((M))$, we have
  $ a(sum c_j x_j)=sum c_j lr((a x_j))=0. $
  Because $M=sum End_A lr((M)) x_j$, we have $a M=0$, and hence $a=0$ by the
  hypothesis that $M$ is faithful.
]

#proposition[
  Suppose $M$ is a semisimple left $A$-module. Then $A_l$ is a semisimple
  $K$-algebra. If $M$ is a simple left $A$-module, then $A_l$ is a simple
  $K$-algebra.
] <prop:semisimple-image-algebra>

#proof[
  To prove the first statement, we note that $M$ is a faithful semisimple left
  $A_l$-module. Hence by Lemma~@lem:faithful-regular-embedding, there is a left
  $A_l$-isomorphism of $A_l$ onto a submodule of $M^((s))$ for some $s$. But
  $M^((s))$ is a semisimple $A_l$-module, whence so is $A_l$.

  Turning to the proof of the second assertion, we observe that for each $s$,
  $M^((s))$ is a homogeneous semisimple left $A_l$-module. Therefore by
  @lem:faithful-regular-embedding $A_l$ is also a homogeneous left $A_l$-module,
  so $A_l$ is a simple $K$-algebra by
  Theorem~@th:wedderburn-semisimple-decomposition.
]

#theorem(name: "Burnside's Theorem")[
  Let $M$ be a simple left $A$-module, and suppose that
  $End_A lr((M))=K dot 1_M$. Then $A_l=End_K lr((M))$, that is, every
  $K$-endomorphism of $M$ is realized by left multiplication by some element of
  $A$.
] <th:burnside-full-matrix-algebra>
#idx(
  "Burnside's Theorem",
  target: [@th:burnside-full-matrix-algebra],
)

#proof[
  By the Density Theorem, $A_l$ is a dense ring of linear transformations on the
  vector space $M$ over $D=End_A lr((M))$. Because $D=K 1_M$ and $M$ is finite
  dimensional, it follows that $A_l=End_K lr((M))$, as required.
]

An important case where Burnside's Theorem can be applied is described by:

#proposition[
  Let $M$ be a simple left $A$-module, and assume that the base field $K$ is
  algebraically closed. Then $End_A lr((M))=K dot 1_M$.
] <prop:algebraically-closed-simple-centralizer>

#proof[
  By Schur's Lemma, $End_A lr((M))$ is a division ring $D$, and $dim_K lr((D))$
  is finite. Let $delta in D$, and let $m(X)="min. pol."_K lr((delta))$. Then
  $m(X)$ is irreducible in
  #source(74)
  $K[X]$, since otherwise $m(X)=m_1 lr((X)) m_2 lr((X))$, where both
  $m_1 lr((X))$ and $m_2 lr((X))$ have smaller degree than $m(X)$. But then
  $m_1 lr((delta)) != 0$, $m_2 lr((delta)) != 0$, whereas $m(delta)=0$,
  contradicting the fact that $D$ is a division ring. Thus $m(X)$ must be
  irreducible. But then $m(X)=X-alpha$ for some $alpha in K$, since $K$ is
  algebraically closed. Therefore $delta=alpha dot 1_M in K dot 1_M$, and the
  result is proved.
]

#theorem[
  A necessary and sufficient condition for a semisimple $K$-algebra $A$ to have
  a two-sided Wedderburn decomposition of the form
  $
    A=op("⨁", limits: #true)_(j=1)^m B_j, quad "with"
    B_j tilde.equiv M_(n_j) lr((K)), quad j=1,dots,m,
  $
  is that $End_A lr((M))=K dot 1_M$ for each simple left $A$-module $M$.
] <th:split-semisimple-criterion>

This result follows directly from Burnside's Theorem.

#definition[
  A semisimple $K$-algebra satisfying the conditions of
  Theorem~@th:split-semisimple-criterion is called a _split semisimple
  $K$-algebra_.
] <def:split-semisimple-algebra>
#idx(
  "split semisimple K-algebra",
  target: [@def:split-semisimple-algebra],
)

In particular, by
@th:burnside-full-matrix-algebra–@th:split-semisimple-criterion, every
semisimple $K$-algebra over an algebraically closed field $K$ is a split
semisimple $K$-algebra.

We obtain next some results about split semisimple group algebras, which provide
a first link between the representation theory and the structure of groups.

We begin by introducing some useful terminology:

#definition[
  Let $A$ be a finite dimensional algebra over a field $K$. A set of
  representatives of the isomorphism classes of simple left $A$-modules will be
  called a _basic set of simple_ $A$-modules.
] <def:basic-simple-modules>
#idx(
  "basic set of simple modules",
  target: [@def:basic-simple-modules],
)

Thus ${M_1,dots,M_r}$ is a basic set of simple $A$-modules if every simple
$A$-module is isomorphic to some $M_j$, $1 <= j <= r$, and if
$M_i tilde.equiv.not M_j$ for $i != j$.

#theorem[
  Let $G$ be a finite group, and $K$ a field such that $K G$ is a split
  semisimple $K$-algebra. Let ${M_1,dots,M_r}$ be a basic set of simple
  $K G$-modules. Then
  #enum(
    numbering: "(i)",
    [$|G|=sum_(j=1)^r (dim_K lr((M_j)))^2$.],
    [$r$ equals the number of conjugacy classes in $G$.],
    [The number of times $M_j$ occurs as a composition factor of the left
      regular module $attach((K G), bl: K G)$ is equal to $dim_K lr((M_j))$.],
  )
] <th:split-group-algebra-dimensions>

#proof(head: emph[Sketch of Proof.])[
  The proofs of (i) and (iii) are immediate from the structure theorems
  (§@ss:semisimple-modules-rings). The proof of (ii) is based on the following:
]

#source(75)
#lemma-suffix(base: [@th:split-group-algebra-dimensions], suffix: "a")[
  Let $R$ be a commutative ring, and $G$ a finite group. The center $c(R G)$ of
  the group algebra $R G$ is a free $R$-module, with an $R$-basis consisting of
  the class sums
  $ C_i=sum_(x in frak(C)_i) x, $
  where the ${frak(C)_i}$ are the conjugacy classes of $G$.
] <lem:class-sums-center>
#idx(
  "class sum",
  target: [@lem:class-sums-center],
)

The proof of the lemma is left as an exercise for the reader (see
@bib:CurtisReiner1962[CR (27.24)]). For further discussion of
Theorem~@th:split-group-algebra-dimensions (iii), see
Exercise~@exc:idempotent-multiplicities.

We now use the Lemma to complete the proof of (ii) of
Theorem~@th:split-group-algebra-dimensions, by showing that if $K G$ is split
semisimple, then $dim_K lr((c(K G)))$ is the number of isomorphism classes of
simple left $K G$-modules. From the first Wedderburn Theorem, it follows that
this number of isomorphism classes is the number of Wedderburn components. The
center of $K G$ is easily shown to be the direct sum of the centers of the
Wedderburn components; since $K G$ is split semisimple, each of these is
one-dimensional over $K$, and the theorem follows.

#definition[
  Let $M$ be a left $A$-module of dimension $n$ over $K$. A set of _matrix
  coordinate functions_ of $M$ is a set of $n^2$ functions
  ${X_(i j): 1 <= i,j <= n}$ from $A$ to $K$ defined as follows: Let
  $T: A -> M_n lr((K))$ be a matrix representation afforded by $M$. The matrix
  coordinate function $X_(i j)$ is the function that assigns to each $a in A$
  the $(i,j)$ entry of the matrix $T(a)$.
] <def:matrix-coordinate-functions>
#idx(
  "matrix coordinate functions",
  target: [@def:matrix-coordinate-functions],
)

We remark that different sets of matrix coordinate functions on $M$ are obtained
by varying the choice of a $K$-basis of $M$.

#proposition[
  Let $M$ be a simple left $A$-module of dimension $n$ over $K$, such that
  $End_A lr((M))$ consists of the scalar multiplications by elements of $K$. Let
  ${X_(i j)}$ be a set of matrix coordinate functions of $M$. Then the functions
  ${X_(i j)}$ are linearly independent over $K$.
] <prop:matrix-coordinates-independent>

#proof(head: emph[Sketch of Proof.])[
  We have to prove that if
  $ sum_(i,j) xi_(i j) X_(i j) lr((a))=0 quad "for all" a in A, $
  where the ${xi_(i j)}$ are in $K$, then each $xi_(i j)=0$. By Burnside's
  Theorem, $A_l=End_K lr((M))$. Therefore for each pair $(i,j)$,
  $1 <= i,j <= n$, there exists an $a in A$ such that $X_(i j) lr((a))=1$,
  $X_(i' j') lr((a))=0$, $(i',j') != (i,j)$. The result follows at once.
]

#corollary[
  Let $G$ be a group and $T: G -> GL(M)$ an irreducible representation of $G$ on
  a finite dimensional space $M$. Assume that the centralizer of the set of
  matrices ${T(a),a in G}$ in $End_K lr((M))$ is the set of scalar
  multiplications by elements of $K$. Then the functions $X_(i j): G -> K$
  defined as in @def:matrix-coordinate-functions are linearly independent over
  $K$.
] <cor:irreducible-group-matrix-coordinates>

#source(76)
#proof[
  Let $A$ be the $K$-algebra generated by the matrices ${T(g):g in G}$. Then $A$
  consists of all $K$-linear combinations of these matrices, and so $M$ is a
  faithful simple $A$-module for which $End_A lr((M))=K dot 1_M$. Now let
  ${xi_(i j)} in K$, and suppose that $sum xi_(i j) X_(i j) lr((g))=0$ for all
  $g in G$. It follows that $sum xi_(i j) X_(i j) lr((a))=0$ for all $a in A$,
  where the ${X_(i j)}$ are now a set of matrix coordinate functions defined on
  $A$. Then each $xi_(i j)=0$ by Prop.~@prop:matrix-coordinates-independent, and
  the result is proved.
]

#theorem(name: "Frobenius–Schur Theorem")[
  Let ${M_1,dots,M_d}$ be a basic set of simple left $A$-modules such that
  $End_A lr((M_k))=K$ for $1 <= k <= d$. For each $k$, $1 <= k <= d$, let
  $n_k=dim_K lr((M_k))$ and let ${X_(i j)^k: 1 <= i,j <= n_k}$ be a set of
  matrix coordinate functions of $M_k$. Then the set of $sum n_k^2$ matrix
  coordinate functions ${X_(i j)^k}$ is linearly independent over $K$.
] <th:frobenius-schur-matrix-coordinates>
#idx(
  "Frobenius-Schur Theorem",
  target: [@th:frobenius-schur-matrix-coordinates],
)

#proof(head: emph[Sketch of Proof.])[
  Let the ${xi_(i j)^k} in K$ be such that
  $
    sum_(k=1)^d sum_(i,j=1)^(n_k) xi_(i j)^k X_(i j)^k lr((a))=0
    quad "for all" a in A.
  $
  We must show that each $xi_(i j)^k=0$. Let $M=product.co_(k=1)^d M_k$, and let
  $A_M subset.eq End_K lr((M))$ be the algebra consisting of all left
  multiplications by elements of $A$ acting on $M$. Then $M$ is a faithful
  semisimple left $A_M$-module, and ${M_1,dots,M_d}$ are a basic set of simple
  left $A$-modules. By Burnside's Theorem~@th:burnside-full-matrix-algebra, the
  Wedderburn component of $A_M$ corresponding to $M_k$ affords all
  $K$-endomorphisms on $M_k$, and annihilates each $M_(k')$, for $k' != k$. It
  follows that for each triple ${i,j,k}$, where $1 <= k <= d$,
  $1 <= i,j <= n_k$, there exists an $a in A$ such that
  $
    X_(i j)^k lr((a))=1, quad X_(i' j')^(k') lr((a))=0
    quad "for all" {i',j',k'} != {i,j,k}.
  $
  This gives the desired result.
]

For $E$ an extension field of $K$, and $M$ a left $A$-module, we define
$ M^E=E times.o_K M="left" A^E "-module," quad "where" A^E=E times.o_K A. $

#definition[
  A left $A$-module $M$ is _absolutely simple_ if for every extension field
  $E supset.eq K$, $M^E$ is a simple $A^E$-module. Correspondingly, an
  irreducible $K$-representation of $A$ is _absolutely irreducible_#idx(
    "absolutely irreducible",
  ) if for every $E supset.eq K$, the representation obtained by extending the
  ground field from $K$ to $E$ remains irreducible.
] <def:absolutely-simple>
#idx(
  "absolutely simple module",
  target: [@def:absolutely-simple],
)

Burnside's Theorem yields the following useful criterion for a left $A$-module
$M$ to be absolutely simple.

#theorem[
  A simple left $A$-module $M$ is absolutely simple if and only if
  $End_A lr((M))=K 1_M$.
] <th:absolute-simplicity-centralizer>

#source(77)
#proof(head: emph[Sketch of Proof.])[
  (See @bib:CurtisReiner1962[CR, pp.~202,203]). In case
  $End_A lr((M))=K dot 1_M$, Burnside's Theorem implies that
  $A_l=End_K lr((M))$. Thus $A_l$ induces $(dim_K M)^2$ linearly independent
  $K$-endomorphisms on $M$, for example, a set of matrix units relative to some
  $K$-basis. Then $(A^E)_l$ induces a set of matrix units on the extended vector
  space $M^E$, and hence $M^E$ is a simple $A^E$-module. Conversely, suppose
  $M^E$ is simple for all $E$. From Exercise~@exc:hom-field-extension it follows
  that $dim_K lr((End_A lr((M))))=dim_E lr((End_(A^E) lr((M^E))))$ for all
  extension fields $E$ of $K$. Letting $E$ be algebraically closed, we have
  $dim_E lr((End_(A^E) lr((M^E))))=1$, because $M^E$ is assumed to be simple.
  Then $dim_K lr((End_A lr((M))))=1$, and the proof is completed.
]

Theorem~@th:absolute-simplicity-centralizer is especially important because it
provides an intrinsic test for a module to be absolutely simple, involving only
the computation of $End_A lr((M))$, rather than the consideration of extension
fields.

=== The Morita Theorems <ss:morita-theorems>

Wedderburn's Theorem~@th:simple-artinian-structure establishes a deep connection
between the structure of a simple artinian ring $A$ and the division ring $D$
obtained as the centralizer $End_A lr((M))$ of a simple left $A$-module $M$.
Moreover, the categories of left $A$-modules and left $D$-modules are
essentially the same: every left $A$-module is a direct sum of copies of a
single simple module, and the same is true for $D$-modules.
Morita~@bib:Morita1958 showed that this phenomenon was a special case of a
general criterion for the category of modules over one ring to be equivalent to
the category of modules over another ring. Part of the idea is to analyze the
familiar isomorphism of vector spaces
$ End_K lr((V)) tilde.equiv Hom_K lr((V,K)) times.o_K V $
from a more general point of view. In this section we follow unpublished notes
of Bass, and present some of Morita's results in a form suitable for later
applications.

We must first introduce some additional concepts from category theory (see
§@ss:categories-functors). Let $frak(A)$ and $frak(B)$ be categories, and let
$F,G$ be covariant functors from $frak(A)$ to $frak(B)$. A _natural
transformation_#idx(
  "natural transformation",
) $tau: F -> G$ is a rule which assigns to each object $A in frak(A)$ a map
$tau_A: F(A) -> G(A)$, such that for every map $f: A_1 -> A_2$ in $frak(A)$, the
following diagram is commutative
#natural-transformation-diagram
In case the maps $tau_A$ are isomorphisms for all $A in frak(A)$, $tau$ is
called a _natural equivalence of functors_#idx(
  "natural equivalence of functors",
).

#source(78)
The composite of two covariant functors $F: frak(A) -> frak(B)$ and
$G: frak(B) -> frak(C)$ is well defined, and yields a covariant functor
$G compose F: frak(A) -> frak(C)$. The _identity functor_ $id_(frak(A))$ of a
category $frak(A)$ is the functor which assigns each object and map of $frak(A)$
to itself.

#definition(numbered: false)[
  Two categories $frak(A)$ and $frak(B)$ are _equivalent_#idx(
    "equivalent categories",
  ) provided there exist covariant functors $F: frak(A) -> frak(B)$ and
  $G: frak(B) -> frak(A)$ such that the composites $G compose F$ and
  $F compose G$ are naturally equivalent to the identity functors in $frak(A)$
  and $frak(B)$, respectively. Equivalent categories (of modules) are often said
  to be _Morita equivalent_#idx(
    "Morita equivalence",
  ).
]

Properties of objects or maps in $frak(A)$ are _categorical_#idx(
  "categorical",
) if these properties carry over to their images under arbitrary equivalences of
categories.

In a category of modules $attach(frak(M), bl: A)$, a module $P$ is called a
_generator_#idx(
  "generator (of category)",
) of $attach(frak(M), bl: A)$ if every module $X in attach(frak(M), bl: A)$ is a
homomorphic image of a direct sum $op("⨁", limits: #true)_(i in I) P_i$ of
copies of $P$. Our first result is to characterize generators in categorical
terms.

#lemma[
  A module $P in attach(frak(M), bl: A)$ is a generator of
  $attach(frak(M), bl: A)$ if and only if for any two distinct maps
  $g_1,g_2 in Hom_A lr((N,N'))$, there exists a map $f: P -> N$ such that
  $g_1 f != g_2 f$.
] <lem:generator-categorical-criterion>

#proof[
  First suppose $P$ is a generator, and let $g_1$ and $g_2$ be distinct maps
  from $N$ to $N'$. Suppose that for every map $f: P -> N$ we have
  $g_1 f=g_2 f$. Since $N$ is expressible as a homomorphic image of a direct sum
  of copies of $P$, it follows that for each $n in N$ there exists a finite set
  of homomorphisms $f_i: P -> N$ such that $n=sum f_i lr((p_i))$ for some
  elements $p_i$ in $P$. Then
  $g_1 n=sum g_1 f_i lr((p_i))=sum g_2 f_i lr((p_i))=g_2 n$, contrary to our
  assumption. Therefore there must exist a map $f: P -> N$ with the required
  property that $g_1 f != g_2 f$.

  Conversely, suppose that $P in attach(frak(M), bl: A)$ has the property that
  for each pair of distinct maps $g_1,g_2 in Hom_A lr((N,N'))$, there exists an
  $f in Hom_A lr((P,N))$ with $g_1 f != g_2 f$. We must show that $P$ is a
  generator of $attach(frak(M), bl: A)$. Given $N in attach(frak(M), bl: A)$,
  consider the set of all submodules $L subset.eq N$ which are images of direct
  sums of copies of $P$. This set is nonempty (since it contains the zero
  submodule of $N$), and for every increasing chain of such $L$'s, their union
  is again an image of a direct sum of copies of $P$. Hence by Zorn's Lemma,
  this set has a maximal element $N^*$, say. We wish to show that $N^*=N$; if
  $N^* != N$, then the natural surjection $h: N -> N slash N^*$ is not the zero
  map. By hypothesis, there must then exist an $f in Hom_A lr((P,N))$ such that
  $h f != 0$, that is, $f(P) subset.not N^*$. But then $N^*+f(P)$ is a
  homomorphic image of a direct sum of copies of $P$, which contradicts the
  maximality of $N^*$. Thus $N^*=N$, that is, $N$ is an image of a direct sum of
  copies of $P$, and the proof is finished.
]

Thus, if $attach(frak(M), bl: A)$ and $attach(frak(M), bl: B)$ are equivalent
categories and $P$ is a generator of $attach(frak(M), bl: A)$, then the image of
$P$ in $attach(frak(M), bl: B)$ is a generator of $attach(frak(M), bl: B)$.
Other properties of modules preserved under category equivalences are described
in the exercises.

#source(79)
#lemma[
  For a module $P$ in the category $attach(frak(M), bl: A)$, the following are
  equivalent:
  #enum(
    numbering: "(i)",
    [$P$ is a generator of $attach(frak(M), bl: A)$.],
    [$sum_(u in P') u(P)=A$, where $P'=Hom_A lr((P,A))$.],
    [$A$ is a direct summand of a direct sum of copies of $P$.],
  )
] <lem:generator-trace-criterion>

#proof[
  (i)$arrow.r.double$(ii): Let $I=sum_(u in P') u(P)$. Then $I$ is a left ideal
  in $A$. If $I != A$, then the natural map $h: A -> A slash I$ is different
  from zero, whence by Lemma~@lem:generator-categorical-criterion there exists a
  map $g: P -> A$ such that $h g != 0$. On the other hand, $g(P) subset.eq I$
  and hence $h g=0$, contradicting the assumption that $I != A$, and proving
  that (i)$arrow.r.double$(ii).

  (ii)$arrow.r.double$(iii): Let $M=op("⨁", limits: #true)_(u in P') P_u$, a
  direct sum of copies of $P$ indexed by the set $P'$. The map $f: M -> A$,
  given by $f|_(P_u)=u$, is well defined and surjective by (ii). But $A$ is
  projective in $attach(frak(M), bl: A)$, and hence $A$ is a direct summand of
  $M$.

  (iii)$arrow.r.double$(i): Let
  $op("⨁", limits: #true)_(i in I) P_i=A plus.o A'$, and let $f: N -> N'$ be a
  nonzero map. Then there exists a map $overline(g): A -> N$ such that
  $f overline(g) != 0$. The map $overline(g)$ can be extended to a map
  $g: op("⨁", limits: #true) P_i -> N$, in such a way that $f g$ remains
  different from zero. For at least one index $i$, the restriction $f g|_(P_i)$
  is nonzero. Hence $g|_(P_i)$ defines a map from $P$ to $N$ whose composite
  with $f$ is not zero, which proves (i).
]

#lemma(name: "Dual Basis Lemma")[
  A left module $P in attach(frak(M), bl: A)$ is projective if and only if there
  exist elements ${x_i}$ in $P$ and ${u_i} in P'$, where $P'=Hom_A lr((P,A))$,
  such that
  #enum(
    numbering: "(a)",
    [for $x in P$, $u_i lr((x))=0$ for almost all $i$;],
    [for $x in P$, $x=sum u_i lr((x)) x_i$.],
  )
  Moreover, any generating set of $P$ can be used as a set ${x_i}$ satisfying
  (a) and (b); conversely, any set ${x_i}$, for which (a) and (b) hold, is a set
  of generators.
] <lem:dual-basis>
#idx(
  "Dual Basis Lemma",
  target: [@lem:dual-basis],
)

#proof[
  Let $P=sum_(i in I) A x_i$ be a projective $A$-module, and define a free
  $A$-module $F=op("⨁", limits: #true)_(i in I) A X_i$ with free basis
  ${X_i: i in I}$. Then there is a surjection $phi: F -> P$ given by
  $phi(X_i)=x_i$, $i in I$. This surjection is split since $P$ is
  $A$-projective. Thus we may view $P$ as a direct summand of $F$, and $phi$ as
  a projection map of $F$ onto its summand $P$. For each $x in P$, we can
  express $x$ as an $A$-linear combination of the basis elements ${X_i}$ of $F$,
  $ x=sum_(i in I) a_i lr((x)) X_i. $
  The coefficients ${a_i lr((x))}$ are uniquely determined, and vanish for
  almost all $i$ because the above sum is finite. It follows that each
  coefficient function
  #source(80)
  $x -> a_i lr((x))$, $x in P$, defines an element of $P'$. Using the fact that
  $phi(X_i)=x_i$ for $i in I$, we have
  $
    x=phi(x)=sum_(i in I) a_i lr((x)) phi(X_i)
    =sum_(i in I) a_i lr((x)) x_i.
  $
  Finally, we note that in this construction, the ${x_i}$ are an arbitrary set
  of generators for $P$.

  Conversely, given elements $x_i in P$, $u_i in P'$ for $i in I$, such that (a)
  and (b) hold, we may form the free module
  $F=op("⨁", limits: #true)_(i in I) A X_i$. Then define $phi: F -> P$ by
  $phi(X_i)=x_i$, $i in I$, extended by linearity to all of $F$. By (b), $phi$
  is a surjection and ${x_i}$ is a generating set for $P$. Now we define a map
  $psi: P -> F$ by
  $ psi(x)=sum u_i lr((x)) X_i, quad x in P. $
  Then $psi in Hom_A lr((P,F))$, and is such that $phi psi=1_P$, since for
  $x in P$ we have $x=sum u_i lr((x)) x_i=phi psi(x)$. Thus $P$ is a direct
  summand of $F$, hence is projective. This completes the proof of the lemma.
]

Let $M$ be a left $A$-module, and consider the ring $End_A lr((M))$, where
multiplication is defined as usual by composition of maps: for
$u,u' in End_A lr((M))$,
$ (u u')m=u(u'(m)), quad m in M. $
It is convenient to introduce the _opposite ring_
$B={End_A lr((M))}^circle.small$, having the same elements as $End_A lr((M))$,
but with multiplication reversed. The left $End_A lr((M))$-module $M$ then
becomes a right $B$-module: for $u,u' in B$ and $m in M$, we have
$ m(u u')=u'(u(m))=u'(m u)=(m u)u'. $
Thus, the left $A$-module $M$ becomes a left $A$-, right
${End_A lr((M))}^circle.small$-bimodule: $M in attach(frak(M), bl: A, br: B)$.
We describe this situation by saying that the endomorphism ring $End_A lr((M))$
acts from the opposite side from the action of $A$, and we shall adopt this
convention for the remainder of this section. In a similar fashion, each right
$A$-module $N$ is an $(End_A lr((N)),A)$-bimodule.

The situation to which the Morita Theorems apply involves the following data: a
ring $A$, a module $P in attach(frak(M), bl: A)$, and the ring
$B={End_A lr((P))}^circle.small$ acting from the right on $P$. Thus
$P in attach(frak(M), bl: A, br: B)$, as explained above. We set
$Q=Hom_A lr((P,A))$; then
$
  Q=Hom_A lr((attach(P, bl: A, br: B),attach(A, bl: A, br: A)))
  in attach(frak(M), bl: B, br: A),
$
by the discussion in §@sec:hom-tensor-projective-injective-flat. There are
compositions of $A$ and $B$ on $Q$ satisfying
$ (b u a)x=[u(x b)]a quad "for" a in A,b in B,u in Q,x in P. $

#source(81)
For the following discussion, we consistently let $a in A$, $b in B$,
$x,y,z in P$, $u,v,w in Q$.

We now define biadditive maps
$ ( , ): P times Q -> A, quad [ , ]: Q times P -> B, $
by the rules
$ (x,u)=x u, quad y[u,x]=(y,u)x. $ <eq:morita-pairings>
Then $( , )$ is a $B$-balanced map, that is,
$ (x b,u)=(x,b u) quad "for all" x,b,u. $
It therefore defines a homomorphism
$ ( ): P times.o_B Q -> A $ <eq:morita-evaluation-map>
of $(A,A)$-bimodules, by $(x times.o u)=(x,u)$.

We can now reformulate Lemma~@lem:generator-trace-criterion thus:

#lemma[
  Let $P in attach(frak(M), bl: A)$. The following are equivalent:
  #enum(
    numbering: "(i)",
    [$P$ is a generator of $attach(frak(M), bl: A)$.],
    [The homomorphism @eq:morita-evaluation-map of $(A,A)$-bimodules is
      surjective.],
    [$A$ is a direct summand of a direct sum of copies of $P$.],
  )
] <lem:morita-generator-evaluation>

The map $[ , ]$ is easily shown to be $A$-balanced, and defines a homomorphism
of $(B,B)$-bimodules
$
  [ ]: Q times.o_A P -> B, quad "given by"
  [u times.o x] -> [u,x] quad "for all" u,x.
$
The maps $( , )$ and $[ , ]$ also satisfy the relation
$ [u,x]v=u(x,v) quad "for all" u,x,v, $ <eq:morita-pairing-associativity>
as can be seen by letting both sides act on an element $y in P$ and using
@eq:morita-pairings.

We may now restate the Dual Basis Lemma~@lem:dual-basis in terms of the map
$[ , ]$, as follows:

#lemma[
  Let $P in attach(frak(M), bl: A)$, and let $[ , ]$ be defined as in
  @eq:morita-pairings. Then $P$ is finitely generated and projective if and only
  if the homomorphism of $(B,B)$-bimodules $[ ]: Q times.o_A P -> B$ is
  surjective.
] <lem:morita-finite-projective-evaluation>

#proof[
  The image of $[ ]$ is a two-sided ideal in $B$; hence $[ ]$ is surjective if
  and only if the identity element $1$ of $B$ belongs to the image of $[ ]$.
  Statement
  #source(82)
  (b) in the Dual Basis Lemma, that $x=sum u_i lr((x)) x_i$, is equivalent to
  the assertion that
  $ x=sum (x,u_i)x_i=sum x[u_i,x_i], $
  and hence to the condition that $1=sum [u_i,x_i]$. The proof follows easily
  from these remarks.
]

Returning to the ideas in the introductory paragraph of this section, we note
that the map $[ , ]: Q times P -> B$ generalizes the $K$-bilinear map of vector
spaces $Hom_K lr((V,K)) times V -> End_K lr((V))$. This latter map is used in
proving that $Hom_K lr((V,K)) times.o_K V tilde.equiv End_K lr((V))$ for a f.d.
vector space $V$ over a field $K$.

#definition[
  A module $P in attach(frak(M), bl: A)$ is a _progenerator_ (in
  $attach(frak(M), bl: A)$) if and only if $P$ is a f.g. projective generator of
  $attach(frak(M), bl: A)$.
] <def:progenerator>
#idx(
  "progenerator",
  target: [@def:progenerator],
)

#definition[
  A _Morita context_ consists of rings $A,B$, bimodules
  $P in attach(frak(M), bl: A, br: B)$, $Q in attach(frak(M), bl: B, br: A)$,
  and biadditive, balanced maps $( , ): P times Q -> A$ and
  $[ , ]: Q times P -> B$ which define homomorphisms of bimodules
  $ ( ): P times.o_B Q -> A quad "and" [ ]: Q times.o_A P -> B $
  such that
  $ (x times.o u)=(x,u), quad [u times.o x]=[u,x], $
  and satisfy the conditions:
  $ y[u,x]=(y,u)x, quad "and" [u,x]v=u(x,v), $
  for all $x,y in P$, and $u,v in Q$.
] <def:morita-context>
#idx(
  "Morita context",
  target: [@def:morita-context],
)

The situation we have considered, with $B={End_A lr((P))}^circle.small$,
$Q=Hom_A lr((P,A))$, etc., is a special case of a Morita context. The main
theorem below shows that when the bimodule homomorphisms $( )$ and $[ ]$ are
surjective, the Morita context coincides with the example we have constructed.
There are many other consequences as well, which are handled most efficiently
using the general concept of a Morita context. The formulation of the main
theorem and its proof are due to Bass.

#theorem(name: "Morita Theorem")[
  Let $A$ and $B$ be rings, and let
  ${P in attach(frak(M), bl: A, br: B),Q in attach(frak(M), bl: B, br: A),
    ( , ),[ , ]}$ be a Morita context for which the bimodule homomorphisms $( )$
  and $[ ]$ are surjective. Then the following statements hold:
  #enum(
    numbering: "(i)",
    [$P$ is a progenerator for $attach(frak(M), bl: A)$ and $frak(M)_B$; $Q$ is
      a progenerator for $frak(M)_A$ and
      #source(83)
      $attach(frak(M), bl: B)$.],
    [Both $( )$ and $[ ]$ are isomorphisms of bimodules.],
    [There are bimodule isomorphisms
      $
        Q tilde.equiv Hom_A lr((attach(P, bl: A),attach(A, bl: A)))
        tilde.equiv Hom_B lr((P_B,B_B)),
      $
      $
        P tilde.equiv Hom_A lr((Q_A,A_A))
        tilde.equiv Hom_B lr((attach(Q, bl: B),attach(B, bl: B))).
      $],
    [(Double Centralizer Property).#idx(
        "double centralizer property",
      ) There are ring isomorphisms
      $
        A tilde.equiv {End_B lr((Q))}^circle.small tilde.equiv End_B lr((P)),
        quad B tilde.equiv End_A lr((Q))
        tilde.equiv {End_A lr((P))}^circle.small.
      $],
    [The covariant functors
      $
        P times.o_B *: attach(frak(M), bl: B) -> attach(frak(M), bl: A)
        quad "and" Q times.o_A *:
        attach(frak(M), bl: A) -> attach(frak(M), bl: B)
      $
      define an equivalence of categories between $attach(frak(M), bl: A)$ and
      $attach(frak(M), bl: B)$. Similarly,
      $* times.o_A P: frak(M)_A -> frak(M)_B$ and
      $* times.o_B Q: frak(M)_B -> frak(M)_A$ define an equivalence of
      categories between $frak(M)_A$ and $frak(M)_B$.],
    [The set of $A$-submodules of $P$, ordered by inclusion, is isomorphic (as a
      partially ordered set) to the set of left ideals in $B$, ordered by
      inclusion. The $(A,B)$-submodules of $P$ correspond to two-sided ideals of
      $B$. Similar statements follow from symmetry. In particular, $A$ and $B$
      have isomorphic inclusion-ordered sets of two-sided ideals.],
  )
] <th:morita>
#idx(
  "Morita's Theorem",
  target: [@th:morita],
)

#remarks(numbered: false)[
  #enum(
    numbering: "(a)",
    [The inclusion-ordered set of $A$-submodules of $P$ is a lattice, with
      $P_1 and P_2=P_1 inter P_2$ and $P_1 or P_2=P_1+P_2$. It is immediate that
      isomorphisms of partially ordered sets, in this situation, define lattice
      isomorphisms (preserving $P_1 and P_2$ and $P_1 or P_2$), so that the
      isomorphisms in (vi) are in fact lattice isomorphisms.],
    [When $A$ is an algebra over a commutative ring $R$ (see
      §@sec:background-algebras-groups), a left $A$-module $P$ becomes an
      $R$-module, and the composition $A times P -> P$ is $R$-bilinear. Then
      $B={End_A lr((P))}^circle.small$ is also an $R$-algebra, and all
      isomorphisms and equivalences in the main theorem are easily seen to be
      compatible with the action of $R$.],
  )
]

#proof[
  (Remember our agreement to write $a in A$, $b in B$, $x,y,z in P$,
  $u,v,w in Q$.)

  (i) Each element $u in Q$ defines an $A$-homomorphism $( ,u): P -> A$. Since
  $( , )$ is surjective, there exist elements ${x_i} in P$, ${u_i} in Q$, such
  that $sum (x_i,u_i)=1$. By Lemma~@lem:morita-generator-evaluation, it follows
  that $P$ is a generator for $attach(frak(M), bl: A)$. In exactly the same way,
  using $[ , ]$ instead of $( , )$, it follows that $P$ is a generator for
  $frak(M)_B$. Since $[ , ]$ is surjective, there exist $v_j in Q$, $y_j in P$
  such that $sum [v_j,y_j]=1$. Using the
  #source(84)
  relations between $( , )$ and $[ , ]$ in a Morita context and
  Lemma~@lem:morita-finite-projective-evaluation, it follows that $P$ is a f.g.
  projective left $A$-module. Applying the same lemma to $P_B$, using the fact
  that $sum (x_i,u_i)=1$, we conclude that $P$ is a f.g. projective right
  $B$-module. We have now proved the statement (i) for $P$, and the
  corresponding statements for $Q$ follow by symmetry.

  For the rest of the proof, we assume that elements $x_i in P$, $u_i in Q$,
  etc., have been chosen so that
  $ sum (x_i,u_i)=1 quad "in" A, quad sum [v_j,y_j]=1 quad "in" B. $

  (ii) We prove that the kernel of $( )$ is zero. Suppose $z_k in P$, $w_k in Q$
  are such that $(sum z_k times.o w_k)=0$. Then
  $
    sum z_k times.o w_k & =(sum_k z_k times.o w_k) sum_i (x_i,u_i)
                          =sum_(i,k) z_k times.o [w_k,x_i]u_i \
                        & =sum_(i,k) z_k [w_k,x_i] times.o u_i
                          =sum_i sum_k (z_k,w_k)x_i times.o u_i=0.
  $
  Similarly, using the fact that $sum [v_j,y_j]=1$ in $B$, it follows that the
  kernel of $[ ]$ is zero. Since $( )$ and $[ ]$ are surjective by assumption,
  they are isomorphisms, and (ii) is proved.

  (iii) We prove first that
  $Q tilde.equiv Hom_A lr((attach(P, bl: A),attach(A, bl: A)))$. As we have
  already remarked, the map $phi: u -> ( ,u)$, takes $Q$ into
  $Hom_A lr((attach(P, bl: A),attach(A, bl: A)))$. Suppose $(x,u)=0$ for all
  $x in P$. Then $u=1 u=sum [v_j,y_j]u=sum v_j lr((y_j,u))=0$, so $phi$ is
  injective. Now let $f in Hom_A lr((attach(P, bl: A),attach(A, bl: A)))$; we
  shall prove that $f=( ,sum v_j lr((y_j f)))$. We have
  $
    (x,sum v_j lr((y_j f))) & =sum (x,v_j)(y_j f)=[sum (x,v_j)y_j]f \
                            & ={sum x[v_j,y_j]}f=x f,
  $
  as required. Finally, the map $phi$ is a $(B,A)$-homomorphism because
  $ (x,b u a)=(x b,u)a. $
  In exactly the same way, it is shown that there exist isomorphisms of
  bimodules
  $ Q tilde.equiv Hom_B lr((P_B,B_B)) quad "via" u -> [u, ]; $
  $
    P tilde.equiv Hom_B lr((attach(Q, bl: B),attach(B, bl: B)))
    quad "via" x -> [ ,x];
  $
  $ P tilde.equiv Hom_A lr((Q_A,A_A)) quad "via" x -> (x, ). $

  (iv) The map $a -> a_l$, where $a_l$ denotes left multiplication by $a$ on
  $P$, is a homomorphism of rings $A -> End_B lr((P))$, because $P$ is an
  $(A,B)$-bimodule. We
  #source(85)
  shall prove this map is an isomorphism. Suppose $a x=0$ for all $x in P$. Then
  $a=a dot 1=a sum (x_i,u_i)=sum (a x_i,u_i)=0$, and the map $a -> a_l$ is
  injective. Now let $s in End_B lr((P))$. We prove that
  $s=(sum (s x_i,u_i))_l$. For $x in P$ we have
  $
    sum (s x_i,u_i)x & =sum (s x_i)[u_i,x]=s{sum x_i[u_i,x]} \
                     & =s{sum (x_i,u_i)x}=s x,
  $
  and we have proved the first isomorphism. Similarly
  $B tilde.equiv End_A lr((Q))$ via left multiplication by elements of $B$. As
  we saw in our discussion of the examples of a Morita context, there is a
  homomorphism of rings $A -> {End_B lr((attach(Q, bl: B)))}^circle.small$,
  given by right multiplication. Just as in the case of the first isomorphism,
  we see that it is an isomorphism of rings; similarly,
  $B tilde.equiv {End_A lr((attach(P, bl: A)))}^circle.small$.

  (v) Let $F$ be the functor
  $Q times.o_A *: attach(frak(M), bl: A) -> attach(frak(M), bl: B)$, and $G$ the
  functor $P times.o_B *: attach(frak(M), bl: B) -> attach(frak(M), bl: A)$. For
  $M in attach(frak(M), bl: A)$, we have
  $
    G F(M) & =P times.o_B (Q times.o_A M) \
           & tilde.equiv (P times.o_B Q) times.o_A M \
           & tilde.equiv A times.o_A M tilde.equiv M.
  $
  Here, the crucial point is the bimodule isomorphism
  $P times.o_B Q tilde.equiv A$ established in (ii). Similarly
  $F G(N) tilde.equiv N$ for all $N in attach(frak(M), bl: B)$, again using
  (ii). The isomorphisms are natural in $M$ and $N$, and consequently define an
  equivalence of categories. The same arguments, again based on (ii), establish
  an equivalence of categories between $frak(M)_A$ and $frak(M)_B$, completing
  the proof of (v).

  (vi) Finally, the functor
  $G: attach(frak(M), bl: B) -> attach(frak(M), bl: A)$ defines an equivalence
  of categories, with $G(B)$ naturally isomorphic to $P$. It follows easily that
  there is an isomorphism (of partially ordered sets) between the
  inclusion-ordered set of left ideals of $B$ ($= B "-submodules of" B$) and the
  corresponding inclusion-ordered set of $A$-submodules of $G(B)$ ($=P$). This
  isomorphism is a lattice isomorphism, by the remark following the statement of
  the Theorem. This completes the proof.
]

The above result will be adequate for the applications in this book; however it
is by no means the last word on the Morita Theorems. For further results on
them, see Morita~@bib:Morita1958, @bib:Reiner1975[MO §~16], or
Anderson–Fuller~@bib:Anderson1973. Also note the similarities between parts of
the preceding proof and the correspondences, given in @bib:CurtisReiner1962[CR
  §~66], between submodules and ideals in endomorphism rings.

As an illustration, we give another version of the Wedderburn Theorem on the
structure of simple artinian rings; the previous proof in
§@ss:semisimple-algebras-fields made use of the Density Theorem. The argument to
follow is essentially a special case of the proof of the double centralizer
property given in @bib:CurtisReiner1962[CR, pp.~175–177].

#source(86)
#corollary[
  Let $A$ be a simple left artinian ring, and let $P$ be a simple left
  $A$-module. Let $D={End_A lr((P))}^circle.small$, so that
  $P in attach(frak(M), bl: A, br: D)$. Then $D$ is a division ring, $P$ is
  finite dimensional over $D$, and $A tilde.equiv End_D lr((P_D))$.
] <cor:morita-simple-artinian-structure>
#idx(
  "simple artinian ring (structure theorem)",
  target: [@cor:morita-simple-artinian-structure],
)#idx(
  "Wedderburn's Theorems (on simple and semisimple rings)",
  target: [@cor:morita-simple-artinian-structure],
)

#proof[
  From the first part of §@sec:semisimple-rings-modules, the ring $A$ is
  isomorphic to a direct sum of a finite number of copies of $P$, and $P$ is
  finitely generated and projective. By Lemma~@lem:generator-trace-criterion,
  $P$ is a progenerator in $attach(frak(M), bl: A)$. Letting
  $Q=Hom_A lr((attach(P, bl: A),attach(A, bl: A)))$, we have a Morita context
  with $( , )$ and $[ , ]$ defined as in @eq:morita-pairings. Moreover, by
  @lem:morita-generator-evaluation and @lem:morita-finite-projective-evaluation,
  the homomorphisms of bimodules
  $ ( ): P times.o_B Q -> A quad "and" [ ]: Q times.o_A P -> B $
  are surjective. The main theorem~@th:morita can now be applied to show that
  $P$ is also a progenerator in $frak(M)_D$, and hence $dim_D P$ is finite. The
  double centralizer property $End_D lr((P_D)) tilde.equiv A$ follows from part
  (iv) of the main theorem, and the proof is complete.
]

We recommend to the reader the instructive task of determining what the other
parts of the Morita Theorem contribute to the situation in
Corollary~@cor:morita-simple-artinian-structure.

#example(numbered: false)[
  Another frequently-used special case of the Morita Theorem is as follows (with
  proofs of the assertions left to the reader). Let $A$ be a ring and $P$ a free
  left $A$-module with a finite basis ${X_1,dots,X_n}$. Then $P$ is a
  progenerator in $attach(frak(M), bl: A)$. Let
  $B={End_A lr((P))}^circle.small$. Then $B$ is isomorphic to the matrix ring
  $M_n lr((A))$, via the map $b -> (a_(i j))$, where $X_i b=sum_j a_(i j) X_j$,
  $b in B$, $a_(i j) in A$. Let
  $Q=Hom_A lr((attach(P, bl: A),attach(A, bl: A)))$. Then
  $P in attach(frak(M), bl: A, br: B)$, $Q in attach(frak(M), bl: B, br: A)$,
  and ${A,B,P,Q}$ define a Morita context for which the maps $( )$ and $[ ]$,
  defined as in @eq:morita-evaluation-map, etc., are surjective. It follows that
  for $M in attach(frak(M), bl: A)$, $N in attach(frak(M), bl: B)$,
  $ M -> Q times.o_A M, quad "and" N -> P times.o_B N, $
  define an equivalence of categories between $attach(frak(M), bl: A)$ and
  $attach(frak(M), bl: M_n lr((A)))$.
]

#heading(level: 3)[
  Tensor Products of Simple Algebras and Modules. The Skolem–Noether Theorem
] <ss:tensor-simple-algebras-modules>

We shall apply the Morita Theorem~@th:morita to prove some basic results about
tensor products of simple modules and algebras. These will provide a foundation
for the theory of separable algebras and splitting fields to be developed in
§@sec:separable-algebras-splitting-fields. Throughout this section $K$ denotes a
field; though our interest here is mainly with finite dimensional $K$-algebras
and modules, we shall prove the principal results in somewhat greater
generality, which will be needed later.#footnote[For example, completions of
  fields, algebras, and modules are not usually f.g. over the ground field.]

#source(87)
We begin with a new proof of a special case of a result of Azumaya and Nakayama
(@bib:Azumaya1944, @bib:Azumaya1947) (see also Jacobson~@bib:Jacobson1956,
Bourbaki~@bib:Bourbaki1958.)

#proposition[
  Let $A$ and $B$ be $K$-algebras, and let $M$ be a simple left $A$-module, and
  $N$ a simple left $B$-module. Assume that $A$ and $B$ are left artinian rings
  (but not necessarily f.d./$K$). Let $D$ and $E$ be the division algebras over
  $K$ defined by
  $ D={End_A lr((M))}^circle.small, quad E={End_B lr((N))}^circle.small. $
  Letting $times.o$ denote $times.o_K$, we obtain bimodule structures
  $
    M in attach(frak(M), bl: A, br: D),
    quad N in attach(frak(M), bl: B, br: E),
    quad M times.o N in attach(frak(M), bl: A times.o B, br: D times.o E).
  $
  Then the following statements are valid:
  #enum(
    numbering: "(i)",
    [$M times.o N$ is a free right $(D times.o E)$-module with a finite basis.],
    [Let $(A times.o B)_l$ denote the $K$-algebra of left multiplications on
      $M times.o N$ by the elements of $A times.o B$. Then
      $ End_(D times.o E) lr((M times.o N))=(A times.o B)_l. $],
    [The lattice of left $(A times.o B)$-submodules of $M times.o N$ is
      isomorphic to the lattice of left ideals in $D times.o E$. (See
      §@ss:morita-theorems for a discussion of lattice isomorphisms.)],
    [$End_(A times.o B) lr((M times.o N))$ is the algebra of right
      multiplications on $M times.o N$ by elements of $D times.o E$.],
  )
] <prop:tensor-simple-module-centralizers>

#proof[
  We begin by proving (i); it clearly implies that $M times.o N$ is a
  progenerator in $frak(M)_(D times.o E)$. In the example of a Morita context
  given in §@ss:morita-theorems, we shall let $D times.o E$ play the role of the
  ring $A$ in §@ss:morita-theorems, and the right $(D times.o E)$-module
  $M times.o N$ play the role of the left $A$-module $P$ in
  §@ss:morita-theorems. We shall deduce from (ii) that the algebra
  $(A times.o B)_l$ occurring here corresponds to the ring
  $B={End_A lr((P))}^circle.small$ of §@ss:morita-theorems. The remaining
  statements (iii) and (iv) will then follow from Morita's Theorem~@th:morita.

  (i) The vector spaces $M_D$ and $N_E$ are finite dimensional over the division
  rings $D$ and $E$, respectively, by the proof of
  @th:simple-artinian-structure, since $A$ and $B$ are left artinian. If
  $M tilde.equiv D^((r))$ and $N tilde.equiv E^((s))$, then clearly
  $
    M times.o N tilde.equiv D^((r)) times.o E^((s))
    tilde.equiv (D times.o E)^((r s)),
  $
  so $M times.o N$ is a free $(D times.o E)$-module on $r s$ generators, and is
  thus a progenerator in $frak(M)_(D times.o E)$.

  #source(88)
  (ii) Let ${m_i}$ be a $D$-basis of $M_D$, and ${n_j}$ an $E$-basis of $N_E$.
  The above shows that the elements ${m_i times.o n_j}$ form a
  $(D times.o E)$-basis of $M times.o N$. Let
  $f in End_(D times.o E) lr((M times.o N))$. It is then sufficient to prove the
  existence of an element $c in A times.o B$ such that
  $ c(m_i times.o n_j)=f(m_i times.o n_j) $
  for all $i$ and $j$. We can write
  $
    f(m_i times.o n_j)=sum_(k,l,t)
    m_k d_(k l i j t) times.o n_l e_(k l i j t)
  $
  with $d_(k l i j t) in D$ and $e_(k l i j t) in E$. Each matrix coefficient in
  $D times.o_K E$ is a finite sum of simple tensors. Since there are only
  finitely many coefficients, we may use a common finite range $1 <= t <= T$,
  padding the coefficient lists with zeros. By the Density Theorem again, there
  exist elements $a_(k l i j t) in A$ and $b_(k l i j t) in B$ such that
  $
    a_(k l i j t) m_i=m_k d_(k l i j t), quad
    a_(k l i j t) m_(i')=0, quad i' != i,
  $
  and
  $
    b_(k l i j t) n_j=n_l e_(k l i j t), quad
    b_(k l i j t) n_(j')=0, quad j' != j.
  $
  Then
  $
    (sum_(k,l,t) a_(k l i j t) times.o b_(k l i j t))
    (m_i times.o n_j)=f(m_i times.o n_j),
  $
  and
  $
    (sum_(k,l,t) a_(k l i j t) times.o b_(k l i j t))
    (m_(i') times.o n_(j'))=0
    quad "if" (i,j) != (i',j').
  $
  It follows that the element
  $
    c=sum_(i,j,k,l,t) a_(k l i j t) times.o b_(k l i j t)
    in A times.o B
  $
  has the property that $c(m_i times.o n_j)=f(m_i times.o n_j)$ for all $i$ and
  $j$, and (ii) is proved. As we explained earlier, (iii) and (iv) now follow
  from Theorem~@th:morita, and the proposition is proved.#ed-note[
    An element of $D times.o_K E$ need not be a simple tensor; the printed proof
    omitted the finite sums needed for its matrix coefficients. For the matrix
    identities, see Jacobson~@bib:Jacobson1989, Propositions~4.9–4.10.
  ]
]

We shall now apply @prop:tensor-simple-module-centralizers to the study of
tensor products of simple algebras. Let $A$ be a $K$-algebra, not necessarily
finite dimensional over $K$. For $a in A$, let $a_l$ denote left multiplication
by $a$ on $A$, and $a_r$ right multiplication. Then there are $K$-algebra
homomorphisms
$
  A -> A_l subset.eq End_K lr((A)), quad
  A^circle.small -> A_r subset.eq End_K lr((A)),
$
where $A^circle.small$ is the opposite ring of $A$, and $A_l={a_l:a in A}$,
$A_r={a_r:a in A}$. The associativity of $A$ implies that $a_l b_r=b_r a_l$ for
all $a,b in A$. Therefore $A$ becomes
#source(89)
a left $(A times.o_K A^circle.small)$-module upon defining
$ (a times.o b^circle.small)x=(a_l b_r)x=a x b, quad a,b,x in A. $

#lemma[
  $End_(A times.o_K A^circle.small) lr((A))={c(A)}_l$, where $c(A)$ is the
  center of $A$.
] <lem:enveloping-algebra-centralizer>

#proof[
  We are assuming, as usual, that $A$ contains an identity $1$. The inclusion
  one way is clear. Conversely, suppose
  $f in End_(A times.o A^circle.small) lr((A))$. Then $f=f(1)_l$, by an easy
  computation, and one then checks that $f(1) in c(A)$ since
  $f in End_(A times.o A^circle.small) lr((A))$.
]

#lemma[
  Let $A$ be a $K$-algebra. Then
  #enum(
    numbering: "(i)",
    [$A$ is a simple#footnote[This means that $A$ is a simple ring; we do not
        assume here that $dim_K A$ is finite.] $K$-algebra if and only if $A$ is
      a simple left $(A times.o_K A^circle.small)$-module.],
    [If $A$ is a simple $K$-algebra, then its center $c(A)$ is a field.],
  )
] <lem:simple-enveloping-module>
#idx(
  "simple K-algebra",
  target: [@lem:simple-enveloping-module],
)

#proof[
  The two-sided ideals in $A$ are precisely the
  $(A times.o_K A^circle.small)$-submodules of $A$, proving the first statement.
  For the second, by (i) we know that $A$ is a simple
  $(A times.o A^circle.small)$-module; hence
  $End_(A times.o A^circle.small) lr((A))$ is a division algebra over $K$, by
  Schur's Lemma. From Lemma~@lem:enveloping-algebra-centralizer it follows that
  $End_(A times.o A^circle.small) lr((A)) tilde.equiv c(A)$, whence $c(A)$ is a
  field, as required.
]

#definition[
  A simple $K$-algebra $A$ is a _central simple $K$-algebra_ if $A$ is f.d./$K$,
  and the natural embedding $K -> c(A)$ gives an isomorphism
  $K tilde.equiv c(A)$.
] <def:central-simple-algebra>
#idx(
  "central simple K-algebra",
  target: [@def:central-simple-algebra],
)

#theorem[
  Let $A$ and $B$ be simple $K$-algebras, with centers $S$ and $T$,
  respectively. Let $times.o$ denote $times.o_K$. Then the following statements
  hold:
  #enum(
    numbering: "(i)",
    [If both $dim_K A$ and $dim_K B$ are finite, then the lattice of two-sided
      ideals in $A times.o_K B$ is isomorphic to the lattice of ideals in the
      commutative ring $S times.o T$.],
    [Let $A$ and $B$ satisfy the hypothesis of (i) above. Then $A times.o B$ is
      semisimple if and only if $S times.o T$ is semisimple.],
    [If $A$ is a central simple $K$-algebra, and $B$ is an arbitrary simple
      $K$-algebra (not necessarily f.d./$K$), then $A times.o B$ is simple with
      center $1 times.o T$.],
    [If $A$ and $B$ are central simple $K$-algebras, then so is $A times.o B$.],
  )
] <th:tensor-simple-algebras>

#proof[
  (i) By @lem:simple-enveloping-module, $A$ is a simple left
  $(A times.o A^circle.small)$-module, and
  $ End_(A times.o A^circle.small) lr((A)) tilde.equiv S $
  #source(90)
  by @lem:enveloping-algebra-centralizer. Since $S$ is a commutative
  $K$-algebra, we can view $A$ as an $(A times.o A^circle.small,S)$-bimodule.
  Likewise, $B$ is a $(B times.o B^circle.small,T)$-bimodule. We conclude from
  @prop:tensor-simple-module-centralizers that the lattice of
  $(A times.o A^circle.small,B times.o B^circle.small)$-submodules of
  $A times.o B$ is isomorphic to the lattice of ideals in the commutative
  $K$-algebra $S times.o T$. But on the other hand, the
  $(A times.o A^circle.small,B times.o B^circle.small)$-submodules of
  $A times.o B$ are precisely the two-sided ideals of $A times.o B$. This proves
  assertion (i). Statement (ii) is an immediate consequence of (i).

  (iii) We first determine the center $c(A times.o B)$ of $A times.o B$. Clearly
  $1 times.o T subset.eq c(A times.o B)$. Now let
  $sum a_i times.o b_i in c(A times.o B)$, where we may assume that the elements
  ${b_i}$ are linearly independent over $K$. Then for all $a in A$, we have
  $
    0 & =(a times.o 1)(sum a_i times.o b_i)
        -(sum a_i times.o b_i)(a times.o 1) \
      & =sum (a a_i-a_i a) times.o b_i.
  $
  Therefore $a a_i-a_i a=0$ for all $a in A$ and each $i$, so each
  $a_i in c(A)$. Identifying the center of $A$ with $K$, it follows that
  $sum a_i times.o b_i in 1 times.o B$, and hence
  $sum a_i times.o b_i in 1 times.o T$.

  We now turn to the question of the simplicity of $A times.o B$. By
  @lem:simple-enveloping-module and the Density Theorem,
  $A times.o A^circle.small$ is a dense algebra of $K$-linear transformations on
  $A$. If $z=sum_j x_j times.o y_j^circle.small in A times.o A^circle.small$,
  then $z times.o 1$ acts on $A times.o B$ by the formula
  $
    (z times.o 1)(a times.o b)&=z a times.o b
    =sum_j x_j a y_j times.o b \
    &=sum_j (x_j times.o 1)_l (y_j times.o 1)_r (a times.o b).
  $
  It follows that $z I subset.eq I$ for each two-sided ideal $I$ in
  $A times.o B$ and each $z in A times.o A^circle.small$.

  To complete the proof of (iii), it suffices to show that every two-sided ideal
  $I$ in $A times.o B$ is of the form $I=A times.o I'$ for some two-sided ideal
  $I'$ in $B$. Let us identify $A$ with $A times.o 1$, and $B$ with
  $1 times.o B$, and set $I'=I inter B$. Then $I'$ is a two-sided ideal in $B$,
  and clearly $A I' subset.eq I$. Now let $sum_(i=1)^m a_i b_i in I$, where we
  may assume that the elements ${a_i}$ are linearly independent over $K$. By the
  density of $A times.o A^circle.small$ acting on $A$, for each fixed index
  $i_0$, $1 <= i_0 <= m$, there exists an element
  $z_0 in A times.o A^circle.small$ such that $z_0 lr((a_(i_0)))=1$,
  $z_0 lr((a_i))=0$ for $i != i_0$. Since $z_0 I subset.eq I$ for each $z_0$, we
  obtain
  $ z_0 lr((sum a_i b_i))=b_(i_0) in I inter B=I'. $
  Hence $sum a_i b_i in A I'$, which proves that $I=A I'$, and establishes
  (iii).

  Statement (iv) is a direct consequence of (iii), and the theorem is proved.
]

#corollary[
  Let $A$ be a central simple $K$-algebra, and let $E$ be an arbitrary extension
  field of $K$. Then $E times.o_K A$ is a central simple $E$-algebra.
] <cor:central-simple-field-extension>

To conclude this section, we apply our results to the study of automorphisms of
central simple algebras. Let $A$ be a $K$-algebra, and let $a in A$ be an
invertible element. The map $x -> a x a^(-1)$, $x in A$, is an _inner
automorphism_#idx(
  "inner automorphism",
) of $A$. It is a $K$-algebra automorphism, and it leaves fixed each element in
the center
#source(91)
of $A$ (compare this concept with that of inner automorphisms of groups).
However, in contrast with the situation occurring in group theory, we shall
prove here that when $A$ is a central simple $K$-algebra, then every
automorphism of $A$ which acts as the identity on $c(A)$ must be an inner
automorphism. This is a consequence of the following basic result:

#theorem(name: "Skolem–Noether Theorem")[
  Let $B$ be a simple $K$-subalgebra of a central simple $K$-algebra $A$. Then
  every isomorphism of $K$-algebras $phi: B -> B' subset.eq A$ can be extended
  to an inner automorphism of $A$, that is, there exists an element $a in A$
  such that
  $ phi(b)=a b a^(-1) quad "for all" b in B. $
] <th:skolem-noether>
#idx(
  "Skolem-Noether Theorem",
  target: [@th:skolem-noether],
)

#proof[
  We let $times.o$ stand for $times.o_K$ throughout the proof. Let $M$ be a
  simple left $A$-module, and let $D=End_A lr((M))$. Then $D$ is a division
  algebra with center $K dot 1_M$, and by @th:tensor-simple-algebras,
  $B times.o D$ is a simple $K$-algebra, which acts on $M$ according to the rule
  $ (b times.o d)m=b(d m), quad b in B,d in D,m in M. $
  Using the automorphism $phi$, we define a second left $(B times.o D)$-module
  $M'$, whose underlying vector space over $K$ is $M$, and with the action of
  $B times.o D$ given by
  $ (b times.o d)m'=phi(b)(d m), quad b in B,d in D,m' in M'. $
  Then $M$ and $M'$ are left modules over the finite dimensional simple
  $K$-algebra $B times.o D$, and have the same dimension over $K$. From
  §@ss:semisimple-modules-rings, it follows that there exists an isomorphism of
  $(B times.o D)$-modules $theta: M tilde.equiv M'$. Because
  $theta in End_D lr((M))$, it follows from @th:simple-artinian-structure that
  $theta$ is a left multiplication $a_l$ for some element $a in A$. The element
  $a$ is invertible in $A$ because $theta$ is an isomorphism. Finally, since
  $theta$ ($=a_l$) is a $(B times.o D)$-isomorphism, we have
  $ a(b(d m))=phi(b)d(a m) quad "for all" b in B,d in D,m in M. $
  Taking $d=1$, and using the fact that $A$ acts faithfully on $M$, it follows
  that $a b=phi(b)a$, so $phi(b)=a b a^(-1)$, for all $b in B$, completing the
  proof.
]

#corollary[
  Let $A$ be a central simple $K$-algebra, and let $phi$ be an automorphism of
  $A$ which fixes each element of $K dot 1$. Then $phi$ is an inner
  automorphism.
] <cor:central-simple-automorphisms-inner>

#exercises-heading

#exercise[
  Let $D$ be a division ring, $D^circle.small$ its opposite ring, and
  $delta -> delta^circle.small$, $delta in D$, an anti-isomorphism from $D$ to
  $D^circle.small$. Let $V=op("⨁", limits: #true)_(i=1)^n D v_i$ be a left
  vector space over $D$ with basis
  #source(92)
  ${v_i}$. Let $A=End_D lr((V))$, and for each $a in A$ let
  $
    a v_j=sum_(i=1)^n alpha_(i j) v_i, quad alpha_(i j) in D,
    1 <= j <= n.
  $
  Prove that the map $a -> (alpha_(i j)^circle.small)$ gives a ring isomorphism
  $ End_D lr((V)) tilde.equiv M_n lr((D^circle.small)). $
  Show also that $V$ is a simple left $A$-module.
] <exc:left-division-space-endomorphisms>

#exercise[
  Let $A$ be a simple artinian ring, $M$ a simple left $A$-module, and let
  $D=End_A lr((M))$. Let $D^circle.small$ be as above. Prove that
  $A tilde.equiv M_n lr((D^circle.small))$ where $n$ is the dimension of $M$ as
  left vector space over the division ring $D$.
] <exc:simple-artinian-matrix-form>

#exercise[
  Let $A=M_n lr((E))$ for a division ring $E$. For each $i$, $1 <= i <= n$, let
  $L_i$ be the set of all matrices in $A$ whose entries are zero except in the
  $i$-th column.
  #enum(
    numbering: "(a)",
    [Prove that ${L_1,dots,L_n}$ are $A$-isomorphic minimal left ideals, such
      that $A=op("⨁", limits: #true)_(i=1)^n L_i$.],
    [Prove that $A$ is a left and right artinian simple ring, and that the
      center of $A$ consists of all scalar matrices $alpha I$, where $alpha$
      ranges over the center of $E$.],
    [Let $M$ be a simple left $A$-module, and $D=End_A lr((M))$. Prove that
      $D tilde.equiv E^circle.small$, and that $dim_D M=n$.],
  )
] <exc:matrix-ring-structure>

#exercise[
  Prove that a ring $A$ is left semisimple if and only if it is right
  semisimple. In particular, show that a semisimple ring is both left and right
  artinian.

  #hint([@exc:left-right-semisimplicity])[
    Use @th:wedderburn-semisimple-decomposition and
    @th:simple-artinian-structure.
  ]
] <exc:left-right-semisimplicity>

#exercise[
  Let $A$ be a semisimple ring, and $M_1,dots,M_s$ a basic set of simple left
  $A$-modules. Let $D_i=End_A lr((M_i))$, $1 <= i <= s$. Prove that $D_i$ is a
  division ring, and that if $n_i=dim_(D_i) lr((M_i))$, then the Wedderburn
  component of $A$ corresponding to $M_i$ is isomorphic to
  $M_(n_i) lr((D_i^circle.small))$, where $D_i^circle.small$ is the opposite
  ring of $D_i$.
] <exc:wedderburn-components-matrix-form>

#exercise[
  From Exercise~@exc:wedderburn-components-matrix-form, every semisimple ring
  $A$ is a direct sum $op("⨁", limits: #true)_(i=1)^n M_(n_i) lr((D_i))$ for
  some division rings $D_i$. Prove that the integers ${n_i}$ and the division
  rings ${D_i}$ are uniquely determined by $A$.
] <exc:wedderburn-uniqueness>

#exercise[
  Keeping the notation of Exercise~@exc:wedderburn-components-matrix-form, let
  $M$ be a left $A$-module for which
  $ M tilde.equiv product.co_(i=1)^s M_i^((k_i)). $
  Show that
  $
    End_A M tilde.equiv product_(i=1)^s End_A {M_i^((k_i))}
    tilde.equiv product_(i=1)^s M_(k_i) lr((D_i)),
  $
  #source(93)
  where
  $ D_i=End_A M_i, quad 1 <= i <= s. $
] <exc:semisimple-module-endomorphisms>

#exercise[
  An idempotent $e$ in a semisimple ring $A$ is called _primitive_#idx(
    "primitive idempotent",
  ) if $A e$ is a simple left $A$-module. Prove that $e$ is primitive if and
  only if it is impossible to express $e$ as a sum $e=e'+e''$ of idempotents
  $e',e''$ such that $e' e''=e'' e'=0$. (Remember that all idempotents are, by
  definition, different from zero.)
] <exc:primitive-idempotents>

#exercise[
  Let $A$ be a semisimple ring. An idempotent $e$ in the center of $A$ is
  _primitive_ (or _central primitive_#idx(
    "central (primitive) idempotents",
  )#idx(
    "primitive central idempotent",
  )) if $A e$ is a Wedderburn component of $A$.
  #enum(
    numbering: "(a)",
    [State and prove a criterion for central primitivity along the lines of
      Exercise~@exc:primitive-idempotents.],
    [Prove that a central primitive idempotent in $A$ is characterized as a
      central idempotent that acts as the identity operator on one simple left
      $A$-module $M$, and annihilates all other simple modules not isomorphic to
      $M$.],
  )
] <exc:central-primitive-idempotents>

#exercise[
  Let $A$ be a f.d. algebra over a field $K$. Let $M$ be a f.g. left $A$-module,
  and let $e$ be an idempotent in $A$.
  #enum(
    numbering: "(a)",
    [Prove that there exists a $K$-isomorphism
      $ Hom_A lr((A e,M)) tilde.equiv e M. $],
    [Prove that if $A$ is a split semisimple $K$-algebra, and $A e$ is a simple
      left $A$-module generated by an idempotent $e$, then
      $dim_K e M="number of direct summands"$ of $M$ isomorphic to $A e$.],
    [In particular, prove that a simple $A$-module $M$, for a split semisimple
      $K$-algebra $A$, appears in the left regular module $attach(A, bl: A)$
      with multiplicity equal to $dim_K M$. (Note that this result proves
      @th:split-group-algebra-dimensions (iii).)],
  )
] <exc:idempotent-multiplicities>

#exercise[
  Let $A=product.co_(i=1)^r M_(n_i) lr((K))$ be a split semisimple $K$-algebra
  over a field $K$. Prove that there exists a $K$-basis of $A$ consisting of
  elements ${e_(j k)^i}$, $1 <= i <= r$, $1 <= j,k <= n_i$, for which the
  multiplication is given by
  $
    e_(j k)^i e_(l m)^(i')=delta_(i i') delta_(k l) e_(j m)^i
    quad (delta_(i i'),delta_(k l)="Kronecker deltas").
  $
  Prove conversely that every $K$-algebra, with a basis satisfying the above
  multiplication table, is a split semisimple $K$-algebra.
] <exc:matrix-units-split-algebra>

#exercise[
  Let $A$ and $B$ be rings, and
  $F: attach(frak(M), bl: A) -> attach(frak(M), bl: B)$ and
  $G: attach(frak(M), bl: B) -> attach(frak(M), bl: A)$ covariant functors
  defining an equivalence of categories between $attach(frak(M), bl: A)$ and
  $attach(frak(M), bl: B)$. Prove that the following properties of morphisms and
  objects are _categorical_ in the sense#idx(
    "categorical property",
  ) that if $f: M -> N$ has the property in $attach(frak(M), bl: A)$, so does
  $F(f)$ in $attach(frak(M), bl: B)$, and similarly for objects:
  #enum(
    numbering: "(i)",
    [$f: M -> N$ is surjective (first prove that the condition is equivalent to
      the following: $g_1 f=g_2 f arrow.r.double g_1=g_2$).],
    [#source(94)
      $f: M -> N$ is injective (first prove that the condition is equivalent to
      the following: $f g_1=f g_2 arrow.r.double g_1=g_2$).],
    [An object $M in attach(frak(M), bl: A)$ is projective (use
      @prop:projective-module-criteria).],
    [An object $M in attach(frak(M), bl: A)$ is injective (dualize (iii)).],
    [An object $M in attach(frak(M), bl: A)$ is a generator (see
      @lem:generator-categorical-criterion).],
  )
] <exc:categorical-module-properties>

#exercise[
  (See Anderson–Fuller~@bib:Anderson1973, §~21). Let $A,B,F$ and $G$ be as in
  Exercise~@exc:categorical-module-properties. Let
  $ i_(N subset.eq M): N -> M $
  denote the inclusion map from a submodule $N$ into a module
  $M in attach(frak(M), bl: A)$. Prove that
  $ N -> im F(i_(N subset.eq M)) $
  is a lattice isomorphism from the family of submodules of $M$ to the family of
  submodules of $F(M)$. (This result was used without proof in (vi) of
  Theorem~@th:morita.)
] <exc:equivalence-submodule-lattice>

#exercise[
  Keep the above notation. Prove that a left $A$-module $M$ is simple,
  semisimple, indecomposable, or finitely generated if and only if the same is
  true for $F(M)$. Also prove that $rad M=0$ if and only if $rad F(M)=0$.

  #hint([@exc:equivalence-lattice-properties])[
    Show that each of these conditions can be formulated in terms of the lattice
    of submodules of $M$, and use Exercise~@exc:equivalence-submodule-lattice.
    See §@sec:radicals for a discussion of radicals of modules.
  ]
] <exc:equivalence-lattice-properties>

#exercise[
  With the above notation, prove that there is an isomorphism of rings
  $ End_A lr((M)) tilde.equiv End_B lr((F(M))). $
] <exc:equivalence-endomorphism-rings>

#exercise[
  Let $A$ be a f.d. $K$-algebra, and let $V$ be a f.g. left $A$-module. Suppose
  that $e in A$ is an idempotent which annihilates every composition factor of
  $V$. Prove that $e V=0$.

  #hint([@exc:idempotent-annihilates-composition-factors])[
    Relative to a $K$-basis of $V$ adapted to an $A$-composition series for $V$,
    the action of $e$ on $V$ is represented by an upper triangular matrix of the
    form
    $
      mat(
        delim: "[", 0, , ast; dots.v, dots.down, ;
        0, dots, 0
      ).
    $
    Since this matrix is nilpotent, and $e^2=e$, it follows that $e V=0$.
    Another proof is as follows: Let $V=V_1 supset V_2 supset dots supset V_n=0$
    be a composition series for $V$. Then $e V_i subset.eq V_(i+1)$ for each
    $i$, so $e V=0$ because $e^2=e$.
  ]
] <exc:idempotent-annihilates-composition-factors>

#exercise[
  Let $M$ be a f.g. module over a P.I.D. $R$, and let $op("ann")_R M=R alpha$
  for some nonzero $alpha$ which is a product of distinct primes of $R$. Prove
  that $M$ is a semisimple $R$-module.
] <exc:pid-squarefree-semisimple>
