#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/09-orthogonality.typ": *

#heading(level: 2)[
  Orthogonality Relations and Central Idempotents
] <sec:orthogonality-central-idempotents>

The orthogonality relations impose restrictions on the values of irreducible
characters. These facts alone are sufficiently powerful to handle a surprisingly
large number of applications. The account of the orthogonality relations in
@bib:CurtisReiner1962[CR §~31] follows closely the original work of Schur. The
same is true for the treatment in Dornhoff~@bib:Dornhoff1971 and
Feit~@bib:Feit1967. Our presentation below is based on the connection between
irreducible characters of a split semisimple algebra and the central idempotents
belonging to the Wedderburn components of the algebra which correspond to the
irreducible characters. The extension of the results from group algebras to
arbitrary semisimple algebras will be important in the discussion of Hecke
algebras and centralizer rings (see §@ss:hecke-algebras). The approach followed
below was communicated to the authors by Robert Kilmoyer.

In §@ss:frobenius-symmetric-algebras we review some facts about Frobenius and
symmetric algebras. The main results relating characters and central idempotents
are given in §@ss:split-semisimple-character-orthogonality, and are specialized
to group characters in §@ss:finite-group-character-orthogonality. The remaining
subsections deal with various applications of character theory, including in
§@ss:burnside-paqb a proof of Burnside's famous $p^a q^b$-Theorem.

=== Frobenius and Symmetric Algebras <ss:frobenius-symmetric-algebras>

In this subsection, $A$ denotes a f.d. algebra over an arbitrary field $K$. Let
$A^*=Hom_K lr((A,K))$, the space of $K$-linear maps from $A$ to $K$.

#source(218)
#definition[
  A bilinear form $beta:A times A -> K$ is called _associative_#idx(
    "associative form",
  ) if $beta(a b, c)=beta(a, b c)$, $a,b,c in A$, and _symmetric_#idx(
    "symmetric form",
  ) if $beta(a, b)=beta(b, a)$ for all $a,b in A$.
] <def:associative-symmetric-form>

#examples[
  #enum(
    numbering: "(a)",
    [Let $lambda:A -> K$ be an element of $A^*$. Then, letting
      $ beta(a, b)=lambda(a b),a,b in A, $
      we obtain an associative bilinear form $beta$.],
    [Let $A=K G$, the group algebra of a finite group $G$ over the field $K$. We
      define
      $ beta(a, b)=lambda(a b),a,b in A, $
      where $lambda in A^*$ is the map defined by
      $ lambda lr((sum_(x in G) alpha_x x))=alpha_1. $
      It is easily checked that, in this case, $beta$ is associative and
      symmetric.],
    [Let $A$ be arbitrary, and define
      $ beta(a, b)="Trace"(a_l b_l),a,b in A, $
      where $a_l in End_K lr((A))$ is the left multiplication defined by
      $a_l:x -> a x$, $x in A$. Then $beta$ is associative and symmetric.
      (Notice the similarity with the Killing form $"Trace"{("ad" a)("ad" b)}$
      on a Lie algebra.)],
  )
] <exm:associative-form-examples>

In case an algebra $A$ possesses an associative (and possibly symmetric)
bilinear form which is nondegenerate, there are a number of connections between
the form and the representation theory of $A$.

We leave it to the reader to check that the form given in
@exm:associative-form-examples(b) is nondegenerate, for an arbitrary field $K$.
The form given in @exm:associative-form-examples(c) is nondegenerate in case $A$
is semisimple and $K$ has characteristic zero. The proof goes as follows: The
form is clearly nondegenerate for $A slash K$ if and only if it is nondegenerate
for $A^E slash E$, for an arbitrary extension field $E$ of $K$. Since
$char K=0$, $A$ is separable over $K$ (see
§@sec:separable-algebras-splitting-fields), and there exists an extension field
$E$ such that $A^E$ is a split semisimple algebra over $E$, that is,
$ A^E tilde.equiv M_(n_1) lr((E)) plus.o dots.c plus.o M_(n_s) lr((E)), $
a direct sum of total matrix algebras over $E$. The Wedderburn components
$A_i tilde.equiv M_(n_i) lr((E))$ of $A^E$ are orthogonal with respect to the
form $beta$; hence $beta$ is nondegenerate if the form $"Tr"(a_l b_l)$ is
nondegenerate on a total matrix algebra $M_n lr((E))$. In this case, the matrix
of $a_l$ with respect to a suitable basis is a direct
#source(219)
sum of $n$ copies of the matrix $a$; hence,
$
  "Tr"(a_l b_l)="Tr"((a b)_l)=n "Tr"(a b),
  "for" a,b in M_n lr((E)).
$
The latter form is easily shown to be nondegenerate on $M_n lr((E))$, whenever
$n != 0$ in $E$.

The significance for representation theory of the existence of a nondegenerate
form, as in @def:associative-symmetric-form, was first pointed out by Frobenius.
Let $A$ be a $K$-algebra, $M$ an $A$-module, and let $M^*=Hom_K lr((M,K))$. The
correspondence $M -> M^*$ then defines a functor from right $A$-modules to left
$A$-modules. Specifically, let $M$ be a f.g. right $A$-module; then $M^*$
becomes a _left_ $A$-module once we define
$ (a phi)(m)=phi(m a),a in A,phi in M^*,m in M. $
<eq:dual-module-left-action>
Indeed, $M$ is a $(K,A)$-bimodule, and $Hom_K lr((M,K))$ is a contravariant
functor on $M$, so $M^*$ becomes a left $A$-module by means of the right action
of $A$ on $M$. (See the discussion in §@ss:homomorphisms in this connection.)

In particular, the algebra $A$ is itself an $(A,A)$-bimodule, and we may define
the _left regular module_#idx("regular module") $attach(A, bl: A)$ to be the
module $A$ on which the algebra $A$ acts from the left. Likewise, the _right
regular module_ $attach(A, br: A)$ is obtained by letting $A$ act from the
right. We may then form
$ (attach(A, br: A))^*=Hom_K lr((attach(A, br: A),K)), $
a left $A$-module.

#definition[
  A f.d. $K$-algebra $A$ is a _Frobenius algebra_#idx("Frobenius algebra") if
  the left $A$-modules $attach(A, bl: A)$ and $(attach(A, br: A))^*$ are
  isomorphic.
] <def:frobenius-algebra>

#proposition[
  A f.d. $K$-algebra is a Frobenius algebra if and only if there exists a
  nondegenerate associative bilinear form $beta:A times A -> K$.
] <prop:frobenius-associative-form>

#proof[
  Suppose $theta:attach(A, bl: A) -> (attach(A, br: A))^*$ is an isomorphism of
  left $A$-modules. Then $theta(a b)=a theta(b)$, and hence
  $ theta(a b)(c)=(a theta(b))(c)=theta(b)(c a),quad forall a,b,c in A. $
  Define $beta(a, b)=theta(b)(a)$, $a,b in A$. Then $beta$ is clearly bilinear,
  and is nondegenerate because $theta$ is an isomorphism. To prove that $beta$
  is associative, we have to compare $beta(a b, c)=theta(c)(a b)$ and
  $beta(a, b c)=theta(b c)(a)$; these are equal by the identity displayed above.
  Conversely, given such a form $beta$, we can define $theta$ as above. By
  reversing the argument, it is easy to show that $theta$ is an $A$-isomorphism
  from $attach(A, bl: A)$ to $(attach(A, br: A))^*$.
]

#source(220)
A Frobenius algebra with a symmetric associative nondegenerate bilinear form
$beta$ is called a _symmetric algebra_#idx("symmetric algebra"). Our previous
discussion shows:

#proposition[
  Let $G$ be a finite group, and $K$ an arbitrary field. Then the group algebra
  $K G$ is a symmetric $K$-algebra.
] <prop:group-algebra-symmetric>

Our earlier discussion also proves that f.d. semisimple algebras over fields of
characteristic zero are symmetric algebras. However, for later use we need the
fact that for every field $K$, whether or not $char K=0$, every f.d. semisimple
$K$-algebra is a symmetric algebra. We begin with an obvious lemma:

#lemma[
  Let $A$ be any f.d. $K$-algebra. Then $A$ is a symmetric $K$-algebra if and
  only if there exists a $K$-linear map $phi:A -> K$ such that
  $ phi(a b)=phi(b a) "for all" a,b in A, $
  and such that $phi$ does not annihilate any nonzero one-sided ideal of $A$.
] <lem:symmetric-algebra-functional>

#proof[
  Given such a $phi$, define $f:A times A -> K$ by $f(a,b)=phi(a b)$ for
  $a,b in A$. Then $f$ has the desired properties. Conversely, given $f$, set
  $phi(a)=f(a,1)$ for $a in A$, and clearly $phi$ behaves as required.
]

#proposition(title: [Eilenberg-Nakayama~@bib:Eilenberg1955])[
  Every f.d. semisimple $K$-algebra $A$ is a symmetric $K$-algebra.
] <prop:eilenberg-nakayama-symmetric-semisimple>
#idx(
  "Eilenberg-Nakayama Theorem",
  target: [@prop:eilenberg-nakayama-symmetric-semisimple],
)

#proof[
  It suffices to prove the result for each simple component of $A$, so (changing
  notation) we may assume that $A=M_n lr((D))$, where $D$ is a division algebra
  over $K$. By Exercise~@exc:division-algebra-additive-commutators, there exists
  a nonzero $K$-linear map $theta:D -> K$ such that
  $theta(alpha beta)=theta(beta alpha)$ for all $alpha,beta in D$. Now define
  $phi:A -> K$ by $phi(a)=theta("Trace" a)$, $a in A$, where $"Trace"(a)$ is the
  usual trace of the matrix $a in M_n lr((D))$. It is easily checked that $phi$
  has the properties described in @lem:symmetric-algebra-functional. Indeed, if
  $L$ is a nonzero left ideal of $A$, choose $a in L$, $a != 0$, and write
  $a=(alpha_(i j))$. Replacing $a$ by $x a$ for suitable $x in A$, we may assume
  that for some $i$, $alpha_(i i) != 0$ and all but the $i$-th row of $a$
  vanishes. But then $L$ contains elements in which $alpha_(i i)$ is arbitrary
  in $D$, so $phi(L) supset.eq theta(D)=K$. This completes the proof.
]

For the rest of this subsection, let $A$ be a f.d. $K$-algebra, and let
$beta:A times A -> K$ be as in @prop:frobenius-associative-form, so $A$ is a
Frobenius $K$-algebra. Let $L$ denote an arbitrary left ideal of $A$, and
$ r(L)="right annihilator of" L={x in A:L x=0}, $
#idx("annihilator")
$ L^perp={x in A:beta(L, x)=0}. $
Then $r(L)$ is clearly a right ideal of $A$, and $r(L)=L^perp$ because for
$x in A$,
$ L x=0 <=> beta(A, L x)=0 <=> beta(A L, x)=0 <=> beta(L, x)=0. $

#source(221)
Similarly, for any right ideal $R$ of $A$, define
$ l(R)="left annihilator of" R={y in A:y R=0}, $
#idx("annihilator")
$ R^perp={y in A:beta(y, R)=0}, $
so $l(R)$ is a left ideal of $A$, and $l(R)=R^perp$. Further, we have
$ (L^perp)^perp=L,(R^perp)^perp=R. $
It follows at once that the correspondence $X arrow.l.r Y$, given by $Y=X^perp$,
$X=Y^perp$, is an inclusion-reversing bijection between the set of left ideals
$X$ of $A$ contained in $L$, and the set of right ideals $Y$ of $A$ containing
$L^perp$. We thus obtain an inclusion-reversing bijection between the set of
submodules of $L$ and the set of submodules of $A slash L^perp$.

We apply these considerations to the case where $L=A e$, with $e$ an idempotent
in $A$. Then for $x in A$,
$ x in L^perp <=> A e x=0 <=> e x=0 <=> x in (1-e)A, $
so
$
  (A e)^perp=(1-e)A,quad A slash (A e)^perp
  =(e A plus.o (1-e)A) slash (1-e)A tilde.equiv e A.
$
We therefore obtain an inclusion-reversing bijection $X arrow.l.r Y$ between the
sets of submodules $X$ of $A e$ and submodules $Y$ of $e A$, given by
$ Y="image of" X^perp slash (1-e)A "in" e A=e X^perp. $
We shall use this machinery to prove a basic result:

#proposition[
  Let $A$ be a Frobenius $K$-algebra, and set $N=rad A$. Let
  $ r(N)={x in A:N x=0},l(N)={y in A:y N=0}. $
  Then
  #enum(
    numbering: "(i)",
    [$r(N)=l(N)$, and $r(N)$ is a two-sided ideal of $A$.],
    [For each primitive idempotent $e in A$, $N e$ is the unique maximal
      submodule of $A e$, and $r(N)e$ is the unique minimal submodule of $A e$.
      Therefore
      $ r(N)e="soc" A e, $
      the socle of $A e$ (see §@ss:injective-hulls).],
    [The algebra $A$ is _self-injective_#idx("self-injective")
      $(="quasi-Frobenius")$#idx("quasi-Frobenius"), that is, the left regular
      module $attach(A, bl: A)$ is injective (see §@ss:injective-hulls).],
    [#source(222)
      For each $e$ as above, $A e$ is a projective cover of $A e slash N e$, and
      is also an injective hull of $r(N)e$.],
  )
] <prop:frobenius-algebra-properties>

#proof[
  Since $N$ is a two-sided ideal of $A$, so are its right and left annihilators
  $r(N)$ and $l(N)$. Let $e$ be a primitive idempotent, so $N e$ is the unique
  maximal submodule of $A e$, and the quotient $A e slash N e$ is a simple left
  $A$-module, by @cor:indecomposable-projective-top.

  We choose $X=N e$ in the discussion preceding
  @prop:frobenius-algebra-properties. The corresponding $Y$ equals $e X^perp$,
  and is the unique minimal submodule of $e A$. Further, for $y in A$, we have
  $ y in X^perp <=> N e y=0 <=> e y in r(N), $
  which implies that $Y=e dot r(N)$. Thus, $e dot r(N)$ is the unique minimal
  submodule of $e A$.

  Since $N$ annihilates all simple $A$-modules, we obtain $(e dot r(N))N=0$, and
  therefore $e dot r(N)N=0$. Therefore $r(N)N$ is annihilated by _every_
  primitive idempotent $e in A$. Since $1_A$ is expressible as a sum of such
  $e$'s, we conclude that $r(N)N=0$, and therefore $r(N) subset.eq l(N)$. The
  reverse inclusion holds by symmetry, and (i) is established. The same argument
  (reversing left and right) also proves (ii).

  We already know from §@ss:projective-covers that $A e$ is a projective cover
  of $A e slash N e$. By @prop:finitely-generated-injective-criterion, to prove
  (iii) we need only show that every short exact sequence
  $ 0 -> attach(A, bl: A) -> V -> W -> 0, $
  <eq:frobenius-injective-extension>
  in which $V$ and $W$ are f.g. left $A$-modules, is necessarily $A$-split. Let
  $ V^*=Hom_K lr((V,K))="dual of" V, $
  so $V^*$ is a right $A$-module, and $(V^*)^* tilde.equiv V$. Since
  @eq:frobenius-injective-extension is split over $K$ (because $K$ is a field),
  it follows that the sequence
  $ 0 -> W^* -> V^* -> (attach(A, bl: A))^* -> 0 $
  <eq:frobenius-dual-projective-sequence>
  is also $K$-split, and is exact as sequence of right $A$-modules. But
  $(attach(A, bl: A))^* tilde.equiv attach(A, br: A)$ by @def:frobenius-algebra,
  so @eq:frobenius-dual-projective-sequence is $A$-split. Taking duals of
  @eq:frobenius-dual-projective-sequence, we obtain an $A$-split exact sequence;
  but the sequence of duals of @eq:frobenius-dual-projective-sequence is
  precisely the sequence @eq:frobenius-injective-extension, so
  @eq:frobenius-injective-extension is $A$-split, as required. We have thus
  verified that every Frobenius algebra is a quasi-Frobenius ring.

  (iv) Now let $e in A$ be a primitive idempotent. Then $A e$ is a direct
  summand of the injective $A$-module $attach(A, bl: A)$, and so $A e$ is an
  indecomposable injective module. To complete the proof of (iv), it suffices to
  show that $A e$ is an injective hull of each of its nonzero submodules $M$.
  Let $E$ be any injective
  #source(223)
  hull of $M$, and consider the diagram
  #frobenius-injective-hull-diagram
  in which $i$, $j$ are inclusion maps. Then there exists a map $theta$ making
  the diagram commute, since $A e$ is injective. Clearly $M inter ker theta=0$,
  and therefore $ker theta=0$ because $E$ is an injective hull of $M$. Thus we
  have an exact sequence
  $ 0 -> E arrow.r^theta A e, $
  which must split since $E$ is injective. Therefore $A e tilde.equiv E$, so
  $A e$ is an injective hull of $M$, as claimed.
]

As remarked in @rem:artinian-self-injective-socles, the assertions in
@prop:frobenius-algebra-properties hold in the more general situation where $A$
is any self-injective ring. However, the proof is somewhat more complicated, and
we refer the reader to @bib:CurtisReiner1962[CR (58.12)] for details.

Some additional information is available when $A$ is not only a Frobenius
algebra, but in fact a symmetric algebra. Let us prove:

#proposition[
  Let $A$ be a symmetric $K$-algebra, and let $e$ be any primitive idempotent of
  $A$. Then
  $ A e slash N e tilde.equiv r(N)e, $
  that is, the socle of $A e$ is isomorphic to the unique simple factor module
  $A e slash N e$ of $A e$.
] <prop:symmetric-projective-top-socle>

#proof[
  Suppose that the bilinear form $beta$ is symmetric. We know by
  @prop:frobenius-algebra-properties that $r(N)e$ is the unique minimal
  submodule of $A e$, and that $N dot r(N)e=0$. Hence every
  $f in Hom_A lr((A e,r(N)e))$ induces a map
  $overline(f) in Hom_A lr((A e slash N e,r(N)e))$, and it suffices to find a
  nonzero $f$. Since there is an isomorphism of additive groups
  $ Hom_A lr((A e,r(N)e)) tilde.equiv e dot r(N)e, $
  given by $f -> f(e)$, we need only show that $e dot r(N)e != 0$.

  Let us assume that $e dot r(N)e=0$, and obtain a contradiction. We have, since
  $beta$ is symmetric and $r(N)$ is a left ideal of $A$,
  $
    0 & =beta(1, e dot r(N)e)=beta(e, r(N)e)=beta(r(N)e, e)=beta(r(N), e) \
      & =beta(A dot r(N), e)=beta(A, r(N)e).
  $
  #source(224)
  Therefore $r(N)e=0$, which is impossible. This completes the proof of the
  Proposition.
]

Since group algebras $K G$ are always symmetric $K$-algebras, the results in
@prop:frobenius-algebra-properties and @prop:symmetric-projective-top-socle
apply to the case where $A=K G$, with $G$ any finite group. These results will
be quite important in the study of modular representations.

#heading(level: 3)[
  Characters and Central Idempotents in Split Semisimple Algebras. Orthogonality
  Relations
] <ss:split-semisimple-character-orthogonality>

In this section, $A$ denotes a f.d. algebra over a field $K$. We shall be
concerned mainly with the case where $char K=0$ and $A$ is a split semisimple
$K$-algebra (see Definition~@def:split-semisimple-algebra), but we shall not
impose these restrictions until later.

Let $M$ be a left $A$-module (always assumed f.d. over $K$ in this subsection).
The trace function $mu:A -> K$ defined by
$ mu(a)="Trace"(a,M),a in A, $
is called the _character_#idx("character") of $A$ _afforded by_#idx(
  "character",
  "afforded by a module",
) $M$. The _degree_#idx("degree of a character")#idx("character", "degree of")
of $mu$, denoted by $deg mu$, is defined as $dim_K M$. Since $mu$ is the trace
map, we have
$ deg mu=mu(1). $
The fact that $mu$ is a trace map has several important consequences:

#proposition[
  #enum(
    numbering: "(i)",
    [$mu in A^*$, where $A^*=Hom_K lr((A,K))$.],
    [If $M$ and $M'$ are isomorphic left $A$-modules, with characters $mu$ and
      $mu'$, respectively, then $mu=mu'$.],
    [If $U_0 supset.eq U_1 supset.eq U_2 supset.eq dots.c$ is an eventually zero
      chain of $A$-submodules of a left $A$-module $U_0$, and if
      $M_i=U_i slash U_(i+1)$, $i=0,1,dots$ are the factor modules with
      characters $mu_0,mu_1,dots$, respectively, then the character $phi$
      afforded by $U_0$ is given by
      $ phi=mu_0+mu_1+dots. $],
  )
] <prop:character-trace-properties>

#proof[
  (i) and (iii) are obvious, while (ii) holds because the trace is preserved
  under a similarity transformation.
]

The main theme of character theory is the study of left $A$-modules (which are
complicated) in terms of their trace functions (which are less complicated).

Let ${M_1,dots,M_s}$ be a basic set of simple left $A$-modules (see
@def:basic-simple-modules), and let $mu_i$ be the character of $A$ afforded by
$M_i$, $1 <= i <= s$. The characters ${mu_1,dots,mu_s}$ are called a _basic set
of irreducible characters_#idx("basic set of irreducible characters")#idx(
  "irreducible character",
)#idx("character", "irreducible") of $A$, and we use the notation
$ "Irr"(A)={mu_1,dots,mu_s}. $
#idx("Irr")

#source(225)
From @prop:character-trace-properties(ii), it follows that the irreducible
characters ${mu_i}$ are independent of the choice of representatives of the
isomorphism classes of simple left $A$-modules.

From now on, we shall assume that $A$ is a split semisimple $K$-algebra. The
results of §@ss:semisimple-algebras-fields apply whether or not $char K=0$, and
we have:

#proposition[
  Let $K$ be an arbitrary field, and let $A$ be a split semisimple $K$-algebra.
  Then
  #enum(
    numbering: "(i)",
    [Each simple $A$-module $M_i$ occurs in the left regular module
      $attach(A, bl: A)$ with multiplicity equal to its $K$-dimension. Therefore
      the character $rho$ of the left regular module can be expressed in terms
      of the irreducible characters as follows:
      $ rho=sum_(i=1)^s (deg mu_i)mu_i=sum_(i=1)^s mu_i lr((1))mu_i. $
      <eq:regular-character-decomposition>],
    [The irreducible characters ${mu_i}$ are linearly independent over $K$.],
    [Let ${e_1,dots,e_s}$ be the central primitive idempotents in $A$. Then
      ${e_1,dots,e_s}$ can be paired with the irreducible characters ${mu_i}$ in
      such a way that $e_i$ acts as the identity operator on $M_i$ and
      annihilates $M_(i')$, for $i' != i$. In terms of characters,
      $mu_i lr((e_i))=deg mu_i$, and $mu_i lr((e_(i')))=0$ if $i != i'$.],
    [The idempotents ${e_1,dots,e_s}$ form a $K$-basis for the center of $A$. In
      particular, $e_i$ is, up to a scalar multiple, the only central element in
      the Wedderburn component $A e_i$ generated by $e_i$, for $1 <= i <= s$.],
  )
] <prop:split-semisimple-character-idempotents>

#proof[
  (ii) follows from the Frobenius-Schur
  Theorem~@th:frobenius-schur-matrix-coordinates, while the other assertions are
  immediate from the results of §@ss:semisimple-algebras-fields.
]

For the remainder of this subsection, we restrict our attention to the special
case of greatest interest, where $char K=0$ and $A$ is a split semisimple
$K$-algebra. By @prop:eilenberg-nakayama-symmetric-semisimple, we know that $A$
is a symmetric $K$-algebra, that is, there exists a nondegenerate symmetric
associative bilinear form
$ beta:A times A -> K. $
The main results of this subsection show how $beta$ can be used to express the
central primitive idempotents ${e_1,dots,e_s}$ explicitly in terms of the
irreducible characters ${mu_i}$ of $A$.

We first require the fact that, because $beta$ is nondegenerate, there exist
$K$-bases ${a_1,dots,a_n}$ and ${b_1,dots,b_n}$ of $A$ which are
_dual_#footnote[See §@ss:duals-lattices.]#idx("dual basis") in the sense that
$ beta(a_i, b_j)=delta_(i j) quad ("Kronecker delta"). $

#source(226)
#example[
  Let $K G$ be a split semisimple group algebra, and as in
  @exm:associative-form-examples(b), let $beta$ be the nondegenerate form
  defined by $beta(a, b)=lambda(a b)$ for $a,b in K G$, where
  $lambda in (K G)^*$ is the linear map such that
  $lambda lr((sum_(x in G) alpha_x x))=alpha_1$. If $G={x_1,dots,x_n}$, where
  $x_1=1$, then ${x_1,dots,x_n}$ form a $K$-basis for $K G$, and it is easily
  checked that ${x_1^(-1),dots,x_n^(-1)}$ is the dual basis with respect to
  $beta$.
] <exm:group-algebra-dual-bases>

#proposition(title: [Kilmoyer])[
  Let $A$ be a split semisimple $K$-algebra over a field of characteristic zero,
  and let ${a_1,dots,a_n}$ and ${b_1,dots,b_n}$ be dual bases of $A$ with
  respect to a nondegenerate symmetric associative bilinear form
  $beta:A times A -> K$. Then the following statements hold:
  #enum(
    numbering: "(i)",
    [For each irreducible character $mu_i in "Irr"(A)$, let
      $d_i=sum_(j=1)^n mu_i lr((a_j))b_j$, $1 <= i <= s$. Then
      $beta(d_i, a)=mu_i lr((a))$, $a in A$. Thus, the elements
      ${d_i:1 <= i <= s}$ are defined independently of the choice of dual bases
      with respect to $beta$.],
    [We have $mu_i lr((d_i)) != 0$, and the central primitive idempotent $e_i$
      corresponding to $M_i$ is given by
      $ e_i=mu_i lr((1))mu_i lr((d_i))^(-1)d_i. $],
    [The element $mu_i lr((d_i)) in K$ can be expressed as
      $
        mu_i lr((d_i))=sum_(j=1)^n mu_i lr((a_j))mu_i lr((b_j))
        =mu_i lr((z))mu_i lr((1))^(-1),
      $
      where $z=sum_(j=1)^n a_j b_j$.],
  )
] <prop:kilmoyer-central-idempotents>

#proof[
  (i) Let $d_i=sum_(j=1)^n mu_i lr((a_j))b_j$. The fact that ${a_j}$ and ${b_j}$
  are dual bases implies at once that
  $ beta(d_i, a_k)=mu_i lr((a_k)),1 <= k <= n. $
  Then by linearity we have $beta(d_i, a)=mu_i lr((a))$ for all $a in A$. Hence
  each $d_i$ is independent of the choice of dual bases, since $beta$ is
  nondegenerate. In other words, $beta$ identifies $A$ with its dual space
  $A^*$, and the element of $A$ corresponding to $mu_i$ is precisely $d_i$.

  (ii) Let $A e_i$ be the Wedderburn component of $A$ corresponding to the
  central primitive idempotent $e_i$. Then for $i != j$,
  $ beta(A e_i, A e_j)=beta(A, e_i A e_j)=0. $
  #source(227)
  Therefore for each $i$, the restriction $beta|_(A e_i)$ is nondegenerate.
  Since $mu_i lr((A e_j))=0$, we obtain
  $ beta(d_i e_j, A e_j)=beta(d_i, A e_j)=mu_i lr((A e_j))=0; $
  hence $d_i e_j=0$ since $beta|_(A e_j)$ is nondegenerate. Since $1=sum e_k$,
  we obtain
  $ d_i=d_i e_i+sum_(j != i) d_i e_j=d_i e_i in A e_i,1 <= i <= s. $
  We prove next that $d_i$ is central in $A$. For each $x,y in A$ we have
  $
    beta(x d_i, y) & =beta(y, x d_i)=beta(y x, d_i)=mu_i lr((y x)) \
                   & =mu_i lr((x y))=beta(d_i, x y)=beta(d_i x, y),
  $
  using (i), the properties of $beta$, and the fact that $mu_i$ is a trace
  function (so that $mu_i lr((x y))=mu_i lr((y x))$). Therefore, by the
  nondegeneracy of $beta$, $x d_i=d_i x$ for all $x in A$; thus $d_i$ is central
  in $A$, and hence central in the Wedderburn component $A e_i$ to which it
  belongs. Moreover, $d_i != 0$ by (i). Since the center of $A e_i$ is
  one-dimensional, we have
  $ e_i=xi d_i,"for some" xi in K. $
  Then, applying $e_i$ to $M_i$ and taking the trace, we have
  $ mu_i lr((1))=mu_i lr((e_i))=xi mu_i lr((d_i)). $
  But $mu_i lr((1)) != 0$ because $K$ has characteristic zero, so
  $mu_i lr((d_i)) != 0$, as claimed, and $xi=mu_i lr((1))mu_i lr((d_i))^(-1)$;
  this gives the formula for $e_i$, and completes the proof of (ii).

  (iii) Consider the element $z=sum a_i b_i$, and let $rho$ be the character of
  $A$ afforded by the left regular module. For $a in A$, we put
  $
    a a_j=sum_(k=1)^n gamma_(k j) lr((a))a_k,
    gamma_(k j) lr((a)) in K,1 <= j <= n.
  $
  Then $gamma_(j j) lr((a))=beta(a a_j, b_j)=beta(a, a_j b_j)$; summing over
  $j$, we have
  $ rho(a)=sum_(j=1)^n gamma_(j j) lr((a))=beta(a, z),a in A. $
  <eq:regular-character-dual-basis-element>
  From @eq:regular-character-decomposition, we have $rho=sum mu_i lr((1))mu_i$.
  Therefore
  $
    rho(d_i)=sum_(j=1)^s mu_j lr((1))mu_j lr((d_i))
    =mu_i lr((1))mu_i lr((d_i))
  $
  #source(228)
  since $mu_j lr((A e_i))=0$ whenever $i != j$. Then by (i) and
  @eq:regular-character-dual-basis-element, we obtain
  $ mu_i lr((z))=beta(d_i, z)=rho(d_i)=mu_i lr((1))mu_i lr((d_i)), $
  which establishes (iii), and completes the proof of the proposition.
]

#proposition(title: [Orthogonality Relations])[
  Keep the notation of @prop:kilmoyer-central-idempotents, and let
  $z=sum_(i=1)^n a_i b_i$. Let $mu$ and $mu'$ be irreducible characters of $A$.
  Then
  $
    sum_(j=1)^n mu(a_j)mu'(b_j)=cases(
      mu(1)^(-1)mu(z) & "if" mu=mu',
      0 & "if" mu != mu',
    ).
  $
] <prop:algebra-character-orthogonality>
#idx("orthogonality relations", target: [@prop:algebra-character-orthogonality])

#proof[
  The result when $mu=mu'$ follows from @prop:kilmoyer-central-idempotents(iii).
  On the other hand, if $mu != mu'$ then
  $ sum_j mu(a_j)mu'(b_j)=mu' lr((sum mu(a_j)b_j))=0 $
  because, by @prop:kilmoyer-central-idempotents(ii), $sum mu(a_j)b_j$ is a
  multiple of the central primitive idempotent corresponding to $mu$.
]

#heading(level: 3)[
  Orthogonality Relations for Characters of Finite Groups
] <ss:finite-group-character-orthogonality>

Throughout this subsection, $G$ denotes a finite group, and $K$ a field of
characteristic $0$. We shall be interested mainly in the case where $K G$ is a
split semisimple $K$-algebra, but we shall not impose these restrictions until
later.

As in §@ss:split-semisimple-character-orthogonality, let $mu:K G -> K$ be the
character afforded by a left $K G$-module $M$. Then, by definition,
$ mu(a)="Trace"(a,M),a in K G. $
Restricting $mu$ to the elements of $G$, we obtain a function $mu:G -> K$, given
by
$ mu(x)="Trace"(x,M),x in G. $
Since the elements of $G$ form a $K$-basis for $K G$, the trace function
$mu:K G -> K$ can be recovered from the values ${mu(x):x in G}$, by means of the
formula
$ mu lr((sum_(x in G) alpha_x x))=sum_(x in G) alpha_x mu(x),alpha_x in K. $
The characters afforded by $K G$-modules, viewed as $K$-valued functions on $G$,
will be called _$K$-characters_#idx("character", "over K") of $G$; we shall use
the same notation for both a $K$-character of $G$ and its extension to $K G$.

#source(229)
In particular, the _irreducible $K$-characters_#idx(
  "irreducible character",
)#idx(
  "character",
  "irreducible",
) of $G$ are given by
$ "Irr"_K lr((G))={zeta^((1)),dots,zeta^((s))}, $
#idx("Irr")
where $zeta^((i))$ is the character afforded by $Z_i$, and ${Z_1,dots,Z_s}$ are
a basic set of simple left $K G$-modules. Let us show at once that every
$K$-character $mu$ of $G$ can be uniquely expressed as a linear combination
$ mu=a_1 zeta^((1))+dots+a_s zeta^((s)), $
with non-negative integer coefficients ${a_i}$. In fact, suppose that $mu$ is
afforded by the $K G$-module $M$, and let $M$ have composition factors $Z_1$
with multiplicity $a_1,dots,Z_s$ with multiplicity $a_s$. From
@prop:character-trace-properties(iii), we obtain the desired formula for $mu$ in
terms of the $zeta$'s.

The uniqueness of the coefficients ${a_i}$ above is a direct consequence of the
following assertion:

#proposition[
  Let
  $ "Irr"_K lr((G))={zeta^((1)),dots,zeta^((s))} $
  be a basic set of irreducible $K$-characters of $G$. Then
  ${zeta^((1)),dots,zeta^((s))}$ are linearly independent over $K$.
] <prop:irreducible-group-characters-independent>

#proof[
  We shall establish the result in the situation where $char K=0$. The result
  also holds when $char K != 0$, and is proved for that case in
  @th:modular-irreducible-character-independence.

  Suppose now that $char K=0$, and let $E$ be an algebraic closure of $K$. Then
  $E G$ is a semisimple $E$-algebra by Maschke's Theorem~@th:maschke, and is a
  split semisimple $E$-algebra by §@ss:semisimple-algebras-fields. Let
  ${W_1,dots,W_l}$ be a basic set of simple left $E G$-modules, and let
  $omega_j$ be the character of $G$ afforded by $W_j$, $1 <= j <= l$. By the
  Frobenius-Schur Theorem~@th:frobenius-schur-matrix-coordinates, the characters
  ${omega_1,dots,omega_l}$ are linearly independent over $E$.

  Now let
  $ Z_i^E=E times.o_K Z_i,1 <= i <= s. $
  Clearly $Z_i^E$ also affords the same character $zeta^((i))$ of $G$ as does
  $Z_i$. On the other hand, each module $Z_i^E$ is expressible as a direct sum
  of copies of the $W$'s, and no $W$ occurs as a summand of both $Z_i^E$ and
  $Z_k^E$ if $i != k$, by Exercise~@exc:hom-field-extension. It follows that for
  each $i$, we can express $zeta^((i))$ as an integral linear combination of the
  $omega$'s, and that a given $omega_j$ cannot occur in both $zeta^((i))$ and
  $zeta^((k))$ for $i != k$. Since the $omega$'s are linearly independent over
  $E$, the same must also hold for the $zeta$'s. Therefore
  ${zeta^((1)),dots,zeta^((s))}$ are linearly independent over $K$, and the
  proposition is established.
]

#source(230)
The above discussion shows the importance of considering integral linear
combinations $sum a_i zeta^((i))$ of the irreducible $K$-characters
${zeta^((i))}$ of $G$. As we shall see later, it is extremely useful to extend
this idea to the case where the ${a_i}$ are arbitrary rational integers, not
necessarily positive. This significant step was taken by Brauer, in his work on
the application of representation theory to the study of Artin $L$-functions.
Let us set
$
  "ch" K G=ZZ zeta^((1)) plus.o dots.c plus.o ZZ zeta^((s))
  =lr({sum_(i=1)^s a_i zeta^((i)):a_i in ZZ}).
$
We shall call the elements of $"ch" K G$ _virtual $K$-characters_#idx(
  "virtual characters",
)#idx("character", "virtual") of $G$; Brauer referred to them as _generalized
characters_#idx("generalized character")#idx(
  "character",
  "generalized",
) of $G$.

We also put
$ "ch"^+ K G=lr({sum a_i zeta^((i)):a_i in ZZ,a_i >= 0}), $
and call the elements of $"ch"^+ K G$ _ordinary characters_#idx(
  "ordinary character",
)#idx("character", "ordinary").

It should be pointed out that, by virtue of
@prop:irreducible-group-characters-independent, the sum $sum ZZ zeta^((i))$ is a
direct sum. Furthermore, $"ch" K G$ has the structure of a commutative ring with
unit. Indeed, let $M$ and $N$ be $K G$-modules affording the characters $mu$ and
$nu$, respectively. We may form the $K G$-module $M times.o_K N$, on which $G$
acts by the rule
$ x(m times.o n)=x m times.o x n,x in G,m in M,n in N. $
We extend the action from $G$ to $K G$ by linearity. Then the $K G$-module
$M times.o_K N$ affords the character $mu nu$, whose value at each $x in G$ is
$mu(x)nu(x)$. (See §@sec:induced-modules for further discussion of tensor
products of modules.)

In particular, for $i$ and $j$ between $1$ and $s$, the $K G$-module
$Z_i times.o_K Z_j$ affords the character $zeta^((i))zeta^((j))$, where this
product is viewed as a product of $K$-valued functions on $G$. Thus
$ (zeta^((i))zeta^((j)))(x)=zeta^((i))(x)zeta^((j))(x) "for" x in G. $
We caution the reader that this formula does _not_ hold for elements of $K G$,
and in fact we have
$
  (zeta^((i))zeta^((j))) lr((sum_(x in G) alpha_x x))
  =sum_(x in G) alpha_x zeta^((i))(x)zeta^((j))(x)
$
for constants ${alpha_x}$ from $K$.

The ring structure of $"ch" K G$ is now defined by using this multiplication
$zeta^((i))zeta^((j))$ for the irreducible $K$-characters of $G$. The unit
element of $"ch" K G$ is the
#source(231)
_trivial character_#footnote[
  The trivial character is sometimes called the _principal character_#idx(
    "principal character",
  )#idx("character", "principal").
]#idx("trivial character")#idx("character", "trivial") $zeta^((1))$, where
$ zeta^((1))(x)=1 "for all" x in G. $
This character is afforded by the _trivial representation_#idx(
  "trivial representation",
) of $G$, which maps each $x in G$ onto $1$; the underlying $K G$-module is the
field $K$ itself, on which $G$ acts trivially.

We shall call $"ch" K G$ the _ring of virtual $K$-characters_#idx(
  "ring of virtual characters",
)#idx("virtual characters", "ring of")#idx("character", "ring") of $G$. Clearly,
$"ch" K G$ is a commutative associative ring with unit. It should be emphasized
that multiplication in $"ch" K G$ has been defined by first defining
multiplication in $"ch"^+ K G$, and then extending the definition by linearity.
Multiplication of characters in $"ch"^+ K G$ corresponds to forming tensor
products of $K G$-modules, as described above.

Besides the properties of characters described in
§@ss:split-semisimple-character-orthogonality, the $K$-characters of $G$ have
the important property that they belong to the $K$-vector space of _class
functions_#idx("class functions") on $G$. The vector space of class functions
will be denoted by $"cf"_K lr((G))$, and consists of all functions constant on
conjugacy classes. Thus
$ "cf"_K lr((G))={phi:G -> K:phi(x y x^(-1))=phi(y),x,y in G}. $
#idx("$cf_K lr((G))$")
Let us prove that each $K$-character $mu$ belongs to $"cf"_K lr((G))$. Relative
to some $K$-basis, the module $M$ affords a matrix representation
$bold(M):G -> G L_n lr((K))$, where $n=dim_K M$. We have
$mu(x)="Trace" bold(M)(x)$, $x in G$. Since $bold(M)$ is a homomorphism, we have
$ bold(M)(x y x^(-1))=bold(M)(x)bold(M)(y)bold(M)(x)^(-1),x,y in G. $
Taking traces, we obtain
$
  mu(x y x^(-1))="Trace"{bold(M)(x)bold(M)(y)bold(M)(x)^(-1)}
  ="Trace" bold(M)(y)=mu(y),
$
so $mu in "cf"_K lr((G))$ as claimed.

#proposition[
  Let $K G$ be a split semisimple $K$-algebra, where $char K=0$.
  #enum(
    numbering: "(i)",
    [Let $zeta$ and $zeta'$ be irreducible $K$-characters of $G$. Then
      $
        |G|^(-1)sum_(x in G) zeta(x)zeta'(x^(-1))=cases(
          0 & "if" zeta != zeta',
          1 & "if" zeta=zeta',
        ).
      $],
    [The central primitive idempotent $e$ corresponding to $zeta$ is given by
      $ e=zeta(1)|G|^(-1)sum_(x in G) zeta(x^(-1))x. $],
  )
] <prop:group-character-orthogonality-idempotents>
#idx(
  "orthogonality relations",
  target: [@prop:group-character-orthogonality-idempotents],
)

#source(232)
#proof[
  Both results are immediate from
  Propositions~@prop:kilmoyer-central-idempotents and
  @prop:algebra-character-orthogonality, using the dual basis of $K G$ given in
  Example~@exm:group-algebra-dual-bases; in this situation, the element
  $z=sum a_i b_i$ becomes $|G| dot 1$.
]

#remark(numbered: false)[
  Other proofs of @prop:group-character-orthogonality-idempotents(i),
  independent of the Wedderburn theorems and based instead on Schur's Lemma, are
  given in @bib:CurtisReiner1962[CR §~31] and in the exercises at the end of
  this section.
]

We have shown that the irreducible $K$-characters ${zeta^((1)),dots,zeta^((s))}$
belong to the space of class functions $"cf"_K lr((G))$, and are linearly
independent (by the Frobenius-Schur
Theorem~@th:frobenius-schur-matrix-coordinates). Moreover, in
Theorem~@th:split-group-algebra-dimensions, it was proved that $s$ is equal to
the number of conjugacy classes in $G$. It follows that
${zeta^((1)),dots,zeta^((s))}$ is a $K$-basis of $"cf"_K lr((G))$. This result
is put in a more precise and useful form in the next part of our discussion.

In order to better understand the orthogonality formulas in
@prop:group-character-orthogonality-idempotents, it will be useful to interpret
them in terms of a hermitian scalar product on the space of complex-valued
functions on $G$. Suppose to begin with that $K G$ is a split semisimple
$K$-algebra, where $char K=0$. We shall show how to identify $"Irr"_K G$ with
$"Irr"_CC G$, where $CC$ is the complex field.

Let $L$ be a field which is a composite of $K$ and $CC$. Then $K$, $CC$ and $L$
are splitting fields for $G$. Moreover, basic sets of simple $K G$-modules and
simple $CC G$-modules yield isomorphic basic sets of simple $L G$-modules. Such
field extensions do not affect the characters viewed as class functions on $G$,
and we may therefore identify#footnote[
  This identification is made with respect to fixed embeddings of $K$ and $CC$
  in $L$.
] $"Irr"_K G$ with $"Irr"_CC G$. This shows that the character theory of $G$
over any splitting field of characteristic $0$ is identical with the character
theory of $G$ over $CC$.

For the rest of the subsection, we assume that $K$ is a subfield of $CC$, such
that $K G$ is a split semisimple $K$-algebra. As shown in §@ss:splitting-fields,
there exist such fields $K$ for which $dim_QQ K$ is finite. On the other hand,
we can choose $K=CC$ if desired.

We now introduce a hermitian scalar product on the space of all complex-valued
functions on $G$, by setting
$
  (phi,psi)_G=|G|^(-1)sum_(x in G) phi(x)overline(psi(x)),quad
  norm(phi)^2=(phi,phi)_G,
$
<eq:character-hermitian-scalar-product>
for arbitrary functions $phi,psi:G -> K$, where $overline(psi(x))$ denotes the
complex conjugate of $psi(x)$. We shall often write $(phi,psi)$ instead of
$(phi,psi)_G$ when it is clear from the context that $G$ is the group under
consideration.

We next observe that if $mu:G -> K$ is a $K$-character of $G$, then
$ mu(x^(-1))=overline(mu(x)), $
#source(233)
for the following reason. Let ${epsilon_1,dots,epsilon_n}$ denote the
eigenvalues of $bold(M)(x)$, where $bold(M):G -> G L_n lr((K))$ is a matrix
representation affording $mu$, and $n=deg mu$. Then the ${epsilon_i}$ are roots
of unity because $bold(M)$ is a homomorphism of the finite group $G$. Moreover,
$ mu(x)=epsilon_1+dots+epsilon_n, $
and hence
$
  mu(x^(-1))=epsilon_1^(-1)+dots+epsilon_n^(-1)
  =overline(epsilon)_1+dots+overline(epsilon)_n=overline(mu(x)).
$
We combine these observations as follows:

#proposition[
  Let $K$ be a subfield of the complex field such that $K G$ is split
  semisimple. Then
  #enum(
    numbering: "(i)",
    [The irreducible $K$-characters ${zeta^((1)),dots,zeta^((s))}$ form an
      orthonormal basis in the vector space $"cf"_K lr((G))$ of class functions,
      with respect to the hermitian scalar product
      @eq:character-hermitian-scalar-product. In particular, for
      $1 <= i,j <= s$,
      $ (zeta^((i)),zeta^((j)))_G=delta_(i j) quad ("Kronecker delta"). $],
    [Each class function $phi in "cf"_K lr((G))$ is a $K$-linear combination of
      the irreducible $K$-characters,
      $ phi=sum a_i zeta^((i)),a_i in K, $
      where the coefficients ${a_i}$ are given by $a_i=(phi,zeta^((i)))$,
      $1 <= i <= s$.],
  )
] <prop:class-function-orthonormal-basis>
#idx("$cf_K lr((G))$", target: [@prop:class-function-orthonormal-basis])

The proof is immediate from
Proposition~@prop:group-character-orthogonality-idempotents and the preceding
remarks, and is left as an exercise.

#remark(numbered: false)[
  Proposition~@prop:class-function-orthonormal-basis can be viewed as the
  foundation for what might be called “Fourier analysis” in the space of class
  functions on the finite group $G$. Here, $phi=sum a_i zeta^((i))$ is the
  Fourier series of $phi in "cf"_K lr((G))$, and ${a_i:1 <= i <= s}$ the Fourier
  coefficients of $phi$; by @prop:class-function-orthonormal-basis, these
  coefficients are expressed as the scalar products $(phi,zeta^((i)))$,
  $1 <= i <= s$.
]

Let $M$ be a $K G$-module. We shall write
$ M tilde.equiv product Z_i^((a_i)) $
to indicate that $M$ is isomorphic to the direct sum of $a_1$ copies of $Z_1$,
$a_2$ copies of $Z_2$, etc. The nonnegative integer $a_i$ is called the
_multiplicity_#idx("multiplicity") of $Z_i$ in $M$. The multiplicities ${a_i}$
are uniquely determined by the Jordan-Hölder Theorem. The next result shows that
they can be expressed in terms of the scalar product of characters.

#source(234)
#proposition[
  #enum(
    numbering: "(i)",
    [A class function $mu$ is a $K$-character if and only if $(mu,zeta^((i)))$
      is a nonnegative integer for $1 <= i <= s$. If $M$ is a left $K G$-module
      affording $mu$, then $(mu,zeta^((i)))$ is the multiplicity of $Z_i$ in
      $M$, for $1 <= i <= s$.],
    [Let $mu=sum a_i zeta^((i))$, $a_i in CC$. Then
      $ norm(mu)^2=(mu,mu)=sum |a_i|^2. $
      In particular, if $mu$ is a $K$-character (so that each $a_i$ is a
      nonnegative integer), then $mu$ is irreducible if and only if
      $(mu,mu)=1$.],
    [Let $mu=sum a_i zeta^((i))$ be a $K$-character afforded by a left
      $K G$-module $M$. Then the multiplicities ${a_i}$ satisfy
      $ a_i=dim_K lr((Hom_(K G) lr((Z_i,M)))),1 <= i <= s. $
      More generally, if $M$ affords the $K$-character $mu$, and $M'$ affords
      $mu'$, then
      $ dim_K lr((Hom_(K G) lr((M,M'))))=(mu,mu')_G. $
      (Because of this formula, $(mu,mu')_G$ is sometimes called the
      _intertwining number_#idx("intertwining number") of $mu$ and $mu'$.)],
    [A class function $mu$ is a virtual $K$-character (that is,
      $mu in "ch" K G$) if and only if each $(mu,zeta^((i))) in ZZ$.],
  )
] <prop:character-scalar-products-multiplicities>

#proof[
  (i) Suppose $mu$ is a $K$-character afforded by a left $K G$-module $M$, and
  let $M tilde.equiv product Z_i^((a_i))$. Then $mu=sum a_i zeta^((i))$ by
  @prop:character-trace-properties(iii). Moreover, $mu(1)=dim_K lr((M))$.
  Conversely, if $mu=sum a_i zeta^((i))$, with each $a_i in ZZ$, $a_i >= 0$,
  then $mu$ is the $K$-character afforded by $product Z_i^((a_i))$.

  (ii) is immediate from (i) and
  Proposition~@prop:class-function-orthonormal-basis(i).

  (iii) Let $M tilde.equiv product Z_j^((a_j))$, so that $mu=sum a_j zeta^((j))$
  as in (i). Then from @eq:hom-direct-sums,
  $
    Hom_(K G) lr((Z_i,M)) tilde.equiv
    plus.o_j {Hom_(K G) lr((Z_i,Z_j))}^((a_j)).
  $
  Moreover, by Schur's Lemma~@lem:schur and the fact that $K G$ is a split
  semisimple $K$-algebra, we have
  $ dim_K lr((Hom_(K G) lr((Z_i,Z_j))))=delta_(i j). $
  Therefore
  $ dim_K lr((Hom_(K G) lr((Z_i,M))))=a_i, $
  from which (iii) follows. Finally, (iv) follows from
  @prop:class-function-orthonormal-basis(ii), and the proof is completed.
]

#source(235)
We introduce next a detailed list of notation, fixed once and for all for a
given finite group $G$, which we shall use in a finer analysis of the
orthogonality relations and their consequences.

#definition[
  The _character table data_ of $G$ consists of the following information:
  $
    {Z_1=K^#footnote[Here, $Z_1$ is just the field $K$ on which each $x in G$
        acts trivially.],Z_2,dots,Z_s}="basic set of simple" K G "-modules."
  $
  $
    {zeta^((1))=1_G,zeta^((2)),dots,zeta^((s))}
    ="irreducible" K "-characters."
  $
  $
    {z_i=zeta^((i))(1),1 <= i <= s}
    ="degrees of the irreducible" K "-characters."
  $
  $
    {frak(C)_1={1},frak(C)_2,dots,frak(C)_s}
    ="conjugacy classes in" G, "with"
  $
  $ C_i=sum_(x in frak(C)_i) x,1 <= i <= s, $
  the class sums (see @lem:class-sums-center).
  $
    h_i=|frak(C)_i|=|G:C_G lr((x_i))|,
    "for" x_i in frak(C)_i,1 <= i <= s.
  $
  $ zeta_j^((i))=zeta^((i))(x),"for" x in frak(C)_j, $
  $ zeta_(j*)^((i))=zeta^((i))(x^(-1)),x in frak(C)_j. $
  The _character table_#idx("character", "table") of $G$ is the $s times s$
  matrix $bold(Z)=(zeta_j^((i)))$ whose rows are indexed by the irreducible
  characters ${zeta^((1)),dots,zeta^((s))}$, and columns by the conjugacy
  classes $frak(C)_1,dots,frak(C)_s$; this matrix can be displayed in the form
  #character-table-diagram
] <def:character-table-data>

In terms of the data assembled in @def:character-table-data, we have

#proposition(title: [First and Second Orthogonality Relations])[
  #enum(
    numbering: "(i)",
    [$sum_(i=1)^s h_i zeta_i^((m))zeta_(i*)^((n))=delta_(m n)|G|$.],
    [$sum_(m=1)^s zeta_i^((m))zeta_(j*)^((m))
      =delta_(i j)|C_G lr((x_i))|$, $x_i in frak(C)_i$.],
  )
] <prop:first-second-character-orthogonality>
#idx(
  "orthogonality relations",
  target: [@prop:first-second-character-orthogonality],
)

#source(236)
#proof[
  The First Orthogonality Relation (i) is simply a restatement of
  Proposition~@prop:group-character-orthogonality-idempotents(i), using the
  facts that the characters are class functions. To derive the Second
  Orthogonality Relation, let $bold(Z)=(zeta_j^((i)))$ be the character table,
  and let $bold(Y)$ be the $s times s$ matrix whose $(i,j)$ entry is
  $y_(i j)=h_i zeta_(i*)^((j))$. Then (i) implies that
  $ bold(Z)bold(Y)=|G|bold(I)_s, $
  where $bold(I)_s$ is the $s$-rowed identity matrix. It follows from linear
  algebra that
  $ bold(Y)bold(Z)=|G|bold(I)_s. $
  Using the entries of $bold(Z)$ and $bold(Y)$, we obtain
  $ sum_(m=1)^s h_i zeta_(i*)^((m))zeta_j^((m))=delta_(i j)|G|. $
  Therefore
  $
    sum_(m=1)^s zeta_(i*)^((m))zeta_j^((m))
    =delta_(i j)|G|h_i^(-1)=delta_(i j)|C_G lr((x_i))|,
    x_i in frak(C)_i,
  $
  as required.
]

=== The Character Table <ss:character-table>

In this section we indicate how information about the structure of a finite
group $G$ may be deduced from its character table $bold(Z)=(zeta_j^((i)))$
defined in @def:character-table-data.

First, we consider how normal subgroups of $G$ may be identified from a
knowledge of the characters of $G$. Let $K$ be a splitting field contained in
$CC$, as in §@ss:finite-group-character-orthogonality. Let $mu$ be a
$K$-character of $G$ afforded by a representation $bold(M):G -> G L_d lr((K))$,
where $d=mu(1)$. Let ${epsilon_1 lr((x)),dots,epsilon_d lr((x))}$ be the
eigenvalues of $bold(M)(x)$, for $x in G$. Then the ${epsilon_i lr((x))}$ are
roots of unity, so $|epsilon_i lr((x))|=1$ for each $i$, $1 <= i <= d$. By the
triangle inequality we have
$ |mu(x)|=|epsilon_1 lr((x))+dots+epsilon_d lr((x))| <= d, $
with equality if and only if $epsilon_1 lr((x))=dots=epsilon_d lr((x))$. In the
latter case, because $"min. pol."_K lr((bold(M)(x)))$ divides $X^(|G|)-1$, and
hence has no repeated factors, it follows that
$bold(M)(x)=epsilon_1 lr((x))bold(I)_d$. The preceding remarks yield at once:

#proposition[
  Let $mu$ be a $K$-character of $G$, afforded by a representation
  $bold(M):G -> G L_d lr((K))$. Then $|mu(x)| <= mu(1)$ for all $x in G$. The
  set ${x in G:|mu(x)|=mu(1)}$ is a normal subgroup of $G$, and coincides with
  the set ${x in G:bold(M)(x) in K dot bold(I)_d}$. The kernel of the
  homomorphism $bold(M):G -> G L_d lr((K))$ is given by
  $ ker bold(M)={x in G:mu(x)=mu(1)}. $
] <prop:character-bound-kernel-scalar-subgroup>

#source(237)
For a $K$-character $mu$, we define the _kernel of $mu$_#idx(
  "kernel of a character",
) (notation: $ker mu$) to be the kernel of a representation#idx(
  "kernel of a representation",
) of $G$ affording $mu$. Thus $ker mu$ is a normal subgroup of $G$, and
@prop:character-bound-kernel-scalar-subgroup can be used to find the kernels of
the irreducible characters. Another consequence is that the index $|G:G'|$ of
the derived group $G'$ in $G$ is equal to the number of irreducible
$K$-characters of $G$ of degree $1$. (For further details, see the exercises.)

Next we consider the multiplication of class sums. Recalling that the class sums
$C_i=sum_(x in frak(C)_i) x$ form a $K$-basis for the center of $K G$, we have
$ C_i C_j=sum c_(i j k)C_k, $
<eq:class-sum-structure-constants>
with structure constants $c_(i j k) in K$. Upon closer examination, we see that
the ${c_(i j k)}$ are nonnegative integers, and in fact
$ c_(i j k)="card" X_(i j k), $
where
$
  X_(i j k)={(x,y) in G times G:x in frak(C)_i,y in frak(C)_j,
    x y=z in frak(C)_k,quad "for a fixed element" z in frak(C)_k}.
$
Now let ${Z_m}$ be the irreducible $K$-representations as in
@def:character-table-data. Then $bold(Z)_m lr((C_i))$ is in the centralizer of
the left $K G$-module $Z_m$, and since $Z_m$ is absolutely simple, we have by
@th:absolute-simplicity-centralizer:
$ bold(Z)_m lr((C_i))=omega_i^((m))bold(I),1 <= i <= s,1 <= m <= s, $
for some $omega_i^((m)) in K$. Taking traces in this formula, we obtain
$ h_i zeta_i^((m))=omega_i^((m))z_m, $
and hence
$ omega_i^((m))=(h_i zeta_i^((m)))/z_m,1 <= i,m <= s. $
<eq:central-character-class-sum-values>
Applying $bold(Z)_m$ to the formula @eq:class-sum-structure-constants, we have
$
  omega_i^((m))omega_j^((m))=sum_(k=1)^s c_(i j k)omega_k^((m)),
  1 <= m <= s.
$
<eq:central-character-multiplicativity>
It follows that the system of $s$ linear homogeneous equations, with coefficient
matrix $(delta_(j k)omega_i^((m))-c_(i j k))_(1 <= j,k <= s)$, has a nontrivial
solution ${omega_k^((m)):1 <= k <= s}$, since for fixed $m$ at least one of
these ${omega_k^((m))}$ is nonzero. Therefore
$det(delta_(j k)omega_i^((m))-c_(i j k))=0$, so the elements ${omega_i^((m))}$
are eigenvalues of the $s times s$ matrix $(c_(i j k))_(1 <= j,k <= s)$. But the
characteristic polynomial of this matrix is a
#source(238)
monic polynomial in $ZZ[x]$, because the structure constants ${c_(i j k)}$ are
integers. Using §@ss:algebras-integral-closure, we obtain the following
important result, which gives the first connection between character theory and
the arithmetic structure of the field $K$:

#proposition[
  The elements $omega_i^((m)) in "alg. int."{K}$ for $1 <= i,m <= s$.
] <prop:central-character-values-integral>

An immediate consequence of @prop:central-character-values-integral is the
following important result about the degrees ${z_m}$ of the irreducible
characters ${zeta^((m))}$:

#proposition[
  The degree $z_m$ divides $|G|$, for $1 <= m <= s$.
] <prop:character-degree-divides-group-order>

#proof[
  We have
  $ QQ inter "alg. int."{K}=ZZ, $
  since $ZZ$ is integrally closed. It therefore suffices to prove that
  $frac(|G|, z_m) in "alg. int."{K}$ for each $m$. Let $n=|G|$; then for each
  $j$, $1 <= j <= s$, the character value $zeta_j^((m))$ is a sum of $n$-th
  roots of $1$, hence is an algebraic integer. But $zeta_j^((m))$ lies in $K$,
  so $zeta_j^((m)) in "alg. int."{K}$. Using
  @prop:central-character-values-integral, we obtain
  $ sum_(j=1)^s omega_j^((m))zeta_(j*)^((m)) in "alg. int."{K}. $
  But by @eq:central-character-class-sum-values and the First Orthogonality
  Relation @prop:first-second-character-orthogonality(i), we have
  $
    sum_j omega_j^((m))zeta_(j*)^((m))
    =z_m^(-1)sum_j h_j zeta_j^((m))zeta_(j*)^((m))=frac(|G|, z_m).
  $
  Therefore $frac(|G|, z_m) in "alg. int."{K}$ as claimed, and the result is
  proved.
]

#remark(numbered: false)[
  See @th:hecke-character-formulas(iv) for a much sharper result about the
  degrees ${z_m}$.
]

We next show that the structure constants ${c_(i j k)}$ in
@eq:class-sum-structure-constants can be recovered from the character table:

#proposition[
  We have for $1 <= i,j,k <= s$,
  $
    c_(i j k)=frac(h_i h_j, |G|) sum_(m=1)^s
    (zeta_i^((m))zeta_j^((m))zeta_(k*)^((m)))/z_m.
  $
] <prop:class-sum-constants-character-table>

#proof[
  From @eq:central-character-class-sum-values and
  @eq:central-character-multiplicativity, we have
  $
    h_i h_j zeta_i^((m))zeta_j^((m))
    =z_m sum_(k=1)^s c_(i j k)h_k zeta_k^((m)).
  $
  #source(239)
  Now multiply this formula by $zeta_(l*)^((m))/z_m$, and sum over $m$. The
  Second Orthogonality Relation implies that
  $
    h_i h_j sum_(m=1)^s
    z_m^(-1)zeta_i^((m))zeta_j^((m))zeta_(l*)^((m)) & =sum_(k=1)^s c_(i j k)h_k
    sum_(m=1)^s
    zeta_k^((m))zeta_(l*)^((m)) \
    & =c_(i j l)h_l dot frac(|G|, h_l)
  $
  which gives the desired formula for $c_(i j l)$. We remark again that each
  integer $c_(i j k)$ counts the number of solutions of the equations $x y=z$,
  with $x in frak(C)_i$, $y in frak(C)_j$, and $z$ fixed in $frak(C)_k$.
]

While it is easy to find examples of non-isomorphic groups with the same
character table (see Exercise~@exc:equal-character-tables-dihedral-quaternion),
no such examples of simple (nonabelian) groups are known. However,
@prop:class-sum-constants-character-table has been used to prove that certain
classes of finite simple groups, such as the alternating groups, are uniquely
determined by their character tables (see G. Higman~@bib:Higman1971).

We turn next to a beautiful result on multiplication of characters, due
originally to Burnside, with improvements by Steinberg and Brauer. Let $M$ and
$N$ be $K G$-modules affording characters $mu$ and $nu$, respectively. We may
form the $K G$-module $M times.o_K N$ on which $G$ acts by the rule
$ x(m times.o n)=x m times.o x n,x in G,m in M,n in N. $
We extend the action from $G$ to $K G$ by linearity. Then the module
$M times.o_K N$ affords the character $mu nu$, whose value at each $x in G$ is
$mu(x)nu(x)$. (See §@ss:mackey-theorems for further discussion of tensor
products of modules.)

We shall also need the concept of a _faithful $K$-character_#idx(
  "faithful character",
)#idx("character", "faithful") $mu$; by definition, this is a character such
that $ker mu={1}$. Equivalently, $mu$ is faithful if for $x in G$, $mu(x)=mu(1)$
implies that $x=1$. Note that the character table of $G$ enables us to decide
whether a given character $mu$ is faithful, provided we know the irreducible
characters occurring in $mu$, and their multiplicities.

Given a $K$-character $mu$, we put
$ mu(G)={mu(x):x in G}, $
and $"card" mu(G)$ the number of elements in the set $mu(G)$. Thus,
$"card" mu(G)$ is the number of distinct values which $mu$ assumes on $G$.

For a faithful $K$-character $mu$, the following striking result was proved by
Brauer~@bib:Brauer1964a, sharpening earlier results of
Burnside~@bib:Burnside1911 and Steinberg~@bib:Steinberg1962:

#theorem[
  Let $mu$ be a faithful $K$-character of $G$, and let $"card" mu(G)=t$. Then
  each irreducible $K$-character $zeta$ of $G$ appears with positive
  multiplicity in at least one of $mu^0(=1_G)$, $mu$, $mu^2,dots,mu^(t-1)$.
] <th:burnside-brauer-character-powers>
#idx("Burnside's Theorem", target: [@th:burnside-brauer-character-powers])

Before giving the proof, we note:

#source(240)
#example[
  Let $rho$ be the character of the left regular module $K G$, where $G != {1}$.
  Then
  $ rho(x)=cases(|G| & x=1, 0 & x != 1). $
  Thus $"card" rho(G)=2$, and @th:burnside-brauer-character-powers asserts that
  every irreducible character is either $1_G$ or appears in $rho$, which has
  already been proved in @th:split-group-algebra-dimensions(iii), using the
  Wedderburn Theorems.
] <exm:regular-character-two-values>

#proof(head: emph[Proof of @th:burnside-brauer-character-powers.])[
  Let $mu$ take on $t$ distinct values ${a_1,dots,a_t}$, and let
  $A_j={x in G:mu(x)=a_j}$, $1 <= j <= t$. Assume that for some $m$,
  $(mu^i,zeta^((m)))=0$ for all $i$, $0 <= i <= t-1$. Then for each $i$,
  $
    |G|(mu^i,zeta^((m)))_G=sum_(j=1)^t mu^i lr((x_j))
    sum_(x in A_j) overline(zeta^((m))(x))=0,
  $
  where $x_j in A_j$. The Vandermonde determinant
  $det(mu^i lr((x_j)))=det(a_j^i)$ is not zero, hence
  $ sum_(x in A_j) zeta^((m))(x)=0 $
  for all $j$. Number the ${a_i}$ so that $a_1=mu(1)$. Then $A_1={1}$ by
  @prop:character-bound-kernel-scalar-subgroup, since $mu$ is faithful. Taking
  $j=1$, the above-displayed equation gives $zeta^((m))(1)=0$, a contradiction,
  and the result is proved.
]

We next present what was historically the first approach to the problem of
constructing character tables (Frobenius~@bib:Frobenius1896; see also
Feit~@bib:Feit1967, §7 and McKay~@bib:McKay1979.)

#proposition[
  A knowledge of the structure constants ${c_(i j k)}$ for the center of $K G$
  (see @eq:class-sum-structure-constants) is equivalent to the knowledge of the
  character table $(zeta_j^((i)))$ of $G$.
] <prop:character-table-class-algebra-equivalence>

#proof[
  By @prop:class-sum-constants-character-table, the ${c_(i j k)}$ are determined
  by the character table, and by the constants ${h_i:1 <= i <= s}$ and $|G|$.
  The group order $|G|$ and the ${h_i}$ are also determined by the character
  table, using the Second Orthogonality Relation. Conversely, assume the
  ${c_(i j k)}$ are known, and let us see how to obtain the character table of
  $G$. We first show how to determine the constants ${omega_i^((m))}$ defined in
  @eq:central-character-class-sum-values. We have
  $ C_i C_j=sum c_(i j k)C_k, $
  and assume that $C_1=1$. Let $bold(A)_i$ be the $s times s$ matrix
  $(c_(i j k))_(j,k)$, for $1 <= i <= s$, and let $w_m$ be the column vector
  with entries $(omega_1^((m)),dots,omega_s^((m)))$, for $1 <= m <= s$. Note
  that $omega_1^((m))=1$ for $1 <= m <= s$, and that, by
  @eq:central-character-multiplicativity,
  $ bold(A)_i w_m=omega_i^((m))w_m,1 <= i,m <= s. $
  #source(241)
  Thus $w_m$ is a common eigenvector for the matrices
  ${bold(A)_1,dots,bold(A)_s}$, with eigenvalues
  ${omega_1^((m)),dots,omega_s^((m))}$, respectively.

  We next show that, up to multiplication by scalars, the vectors
  ${w_m:1 <= m <= s}$ are the only common eigenvectors for the matrices
  ${bold(A)_i:1 <= i <= s}$. Let $V$ be the vector space of $s$-rowed column
  vectors over $K$, and view the matrices ${bold(A)_i}$ as linear
  transformations on $V$. It follows readily from
  @prop:irreducible-group-characters-independent that the vectors
  ${w_m:1 <= m <= s}$ are linearly independent over $K$, and therefore
  $ V=op("⨁", limits: #true)_(m=1)^s K w_m. $
  It is clear from the definition that the matrices ${bold(A)_i}$ afford the
  regular matrix representation of the center of the group algebra with respect
  to the basis ${C_i}$. Therefore we have
  $ bold(A)_i bold(A)_j=sum_k c_(i j k)bold(A)_k $
  as operators on $V$. It follows that the map $C_i -> bold(A)_i$,
  $1 <= i <= s$, defines a representation of the center of $K G$ on the space
  $V$. Furthermore, the subspaces ${K w_m:1 <= m <= s}$ afford one-dimensional
  representations of the center. These $s$ representations are distinct, since
  for $m != n$ we cannot have $omega_i^((m))=omega_i^((n))$ for each $i$,
  $1 <= i <= s$. Thus these subspaces are a basic set of simple modules for the
  center of $K G$. It follows at once that any common eigenvector of the
  matrices ${bold(A)_1,dots,bold(A)_s}$ affords an irreducible (one-dimensional)
  representation of the center of $K G$, and hence must be a scalar multiple of
  one of the vectors ${w_m:1 <= m <= s}$.

  We have now shown that ${w_1,dots,w_s}$ are the uniquely determined common
  eigenvectors of the matrices ${bold(A)_i:1 <= i <= s}$, when normalized so
  that each $w_i$ has first entry $1$. Hence the ${omega_i^((m))}$ are
  computable from the ${c_(i j k)}$. We have, by
  @eq:central-character-class-sum-values,
  $ omega_i^((m))=(h_i zeta_i^((m)))/z_m,1 <= i,m <= s. $
  Since $c_(i j 1)=h_i delta_(i,j*)$, for $1 <= i,j <= s$, the numbers ${h_i}$
  are determined by the ${c_(i j k)}$, and hence so are the numbers
  ${zeta_i^((m))/z_m:1 <= i,m <= s}$. Finally,
  $ sum_(i=1)^s (zeta_i^((m)))/z_m dot omega_(i*)^((m))=frac(|G|, z_m^2), $
  by the First Orthogonality Relation. Thus the degrees ${z_m}$ can be
  calculated from the ${c_(i j k)}$, and hence so can the character values
  ${zeta_j^((i))}$. This completes the proof.
]

#source(242)
We conclude this subsection with some examples of character tables#idx(
  "character",
  "table",
), using the notation of @def:character-table-data, and letting $S_n$ and $A_n$
denote the symmetric and alternating groups on $n$ objects, respectively. Other
character tables, including that of $A_5$, appear in
§§@ss:a5-exceptional-characters, @ss:involution-centralizers-special-classes.
For the character tables of all simple groups of order $<10^6$, see
McKay~@bib:McKay1979. Details of computation of the character tables below are
left as exercises for the reader.

#s3-character-table
#d4-character-table
#a4-character-table
#s4-character-table

where $epsilon$ is a primitive cube root of $1$. Note that $A_4$ is isomorphic
to the group of rotations of the tetrahedron, and $D_4$ is the dihedral group of
order $8$.

#cube-rotation-character-table
#s5-character-table

For discussion of some of these examples, see @bib:CurtisReiner1962[CR §§32,46].

#source(243)
=== Burnside's $p^a q^b$-Theorem <ss:burnside-paqb>

It would be a mistake to leave the scene without a glimpse of the power of some
of the preceding results, when combined with a little algebraic number theory
and group theory. We shall keep the notations set in @def:character-table-data,
and assume that $dim_QQ K < infinity$.

We shall prove Burnside's Theorem#idx("Burnside's Theorem")
(Burnside~@bib:Burnside1911) that if the order of a finite group $G$ is of the
form $p^a q^b$, where $p$ and $q$ are primes, then $G$ is solvable. The
nonsolvable alternating group $A_5$, of order $60=2^2 dot 3 dot 5$, shows that
the theorem cannot be improved without imposing further restrictions. We shall
essentially follow Burnside's proof of the theorem, with emphasis on how the
character theory is brought into the picture.

Assume that the result is false, and let $G$ be a counterexample of minimal
order. From elementary group theory, it is easy to show that $G$ must be simple,
nonabelian, and that both exponents $a$ and $b$ must be positive. Now let $P$ be
a $p$-Sylow subgroup of $G$, and let $h != 1$ be an element in the center
$Z(P)$. Then $C_G lr((h)) supset.eq P$, and $C_G lr((h)) != G$ since otherwise
$Z(G) != {1}$, contrary to our assumption that $G$ is simple and nonabelian. It
follows that $|G:C_G lr((h))|=q^d$ for some $d != 0$. The proof is completed by
establishing the following result:

#proposition(title: [Burnside])[
  Let $G$ be a finite group containing a conjugacy class $frak(C)$ for which
  $|frak(C)|=q^d$ for some prime $q$ and some $d > 0$. Then $G$ cannot be
  simple.
] <prop:burnside-prime-power-conjugacy-class>

#proof[
  We first experiment with some easy consequences of the hypothesis. Let
  $frak(C)$ be the class $frak(C)_i$, so $i$ is fixed from now on, and (using
  the notation in @def:character-table-data) $h_i=q^d$ and $i > 1$. But
  $|G|=sum z_j^2$ by @th:split-group-algebra-dimensions or the Second
  Orthogonality Relation, so
  $ |G|=sum_(j=1)^s z_j^2=1+sum_(j > 1) z_j^2,quad |G| equiv 0 (mod q), $
  whence $q divides.not z_j$ for some $j > 1$.

  We next assert that $zeta_i^((j)) != 0$ for some $j > 1$ such that
  $q divides.not z_j$. Suppose otherwise, so $zeta_i^((j))=0$ whenever $j > 1$
  and $q divides.not z_j$. Let $R="alg. int."{K}$, so $QQ inter R=ZZ$ because
  $ZZ$ is integrally closed. From the Second Orthogonality Relation we obtain
  (since $i > 1$)
  $
    0=sum_(j=1)^s zeta_1^((j))zeta_i^((j))
    =1+sum_(j > 1) z_j zeta_i^((j)).
  $
  Our supposition implies that each $z_j zeta_i^((j)) in q R$ for $j > 1$,
  whence we obtain $1 in q R$. Then $q^(-1) in R inter QQ$, so $q^(-1) in ZZ$,
  which is impossible. This contradiction shows that $zeta_i^((j)) != 0$ for
  some $j > 1$ such that $q divides.not z_j$.
  #source(244)
  Now let $j > 1$ be such that $q divides.not z_j$ and $zeta_i^((j)) != 0$, and
  let us investigate $ker zeta^((j))$, hoping to use
  @prop:character-bound-kernel-scalar-subgroup to find a normal subgroup of $G$.
  By @prop:central-character-values-integral,
  $ omega_i^((j))=h_i zeta_i^((j))/z_j in R. $
  But $h_i=q^d$, whereas $q divides.not z_j$, so we may choose $a,b in ZZ$ such
  that $1=a h_i+b z_j$. Therefore
  $
    a omega_i^((j))=(a h_i zeta_i^((j)))/z_j
    =zeta_i^((j))/z_j-b zeta_i^((j)),
  $
  and we conclude that $zeta_i^((j))/z_j in R$. By
  @prop:character-bound-kernel-scalar-subgroup we have
  $|zeta_i^((j))/z_j| <= 1$, and if we could prove that equality holds, then by
  @prop:character-bound-kernel-scalar-subgroup $G$ would have a normal subgroup
  containing $frak(C)_i$. It is here that we must use some algebraic number
  theory. For convenience, let us denote the algebraic integer
  $zeta_i^((j))/z_j$ by $zeta$, so $zeta != 0$ and $|zeta| <= 1$. Since
  $zeta in R$ we have (see @prop:characteristic-polynomial-integrality)
  $ "char. pol."_(K slash QQ) lr((zeta)) in ZZ[X], $
  whence $N(zeta) in ZZ$, where $N$ denotes the norm map from $K$ to $QQ$. On
  the other hand (see @bib:CurtisReiner1962[CR §~20B]), $N(zeta)$ is the product
  of the algebraic conjugates of $zeta$ over $QQ$.

  Suppose now that $|zeta_i^((j))| < z_j$, so $zeta_i^((j))$ is a sum of $z_j$
  roots of unity, not all of which are equal. But then every algebraic conjugate
  of $zeta_i^((j))$ is also such a sum. This proves that if $|zeta| < 1$, then
  also $|zeta^sigma| < 1$ for every algebraic conjugate $zeta^sigma$ of $zeta$.
  Hence if $|zeta| < 1$, it follows that $|N(zeta)| < 1$; but this is
  impossible, since $N(zeta)$ is a nonzero rational integer. We have thus shown
  that $|zeta_i^((j))|=z_j$.

  Now let $bold(Z)_j$ be an irreducible matrix representation of $G$ affording
  the character $zeta^((j))$, and put
  $ H={x in G:bold(Z)_j lr((x)) in K dot bold(I)}. $
  Then by @prop:character-bound-kernel-scalar-subgroup $H$ is a normal subgroup
  of $G$ containing the class $frak(C)_i$. Thus $G$ cannot be simple unless
  $H=G$; but in that case, $bold(Z)_j$ is an irreducible representation of $G$
  by scalar matrices, and hence must be of degree $1$. Further, $bold(Z)_j$ is
  not the $1$-representation since $j > 1$. Thus $G$ has at least two distinct
  one-dimensional representations, so $G slash G' != 1$ by the remarks following
  @prop:character-bound-kernel-scalar-subgroup. Since $G' ⊴ G$ and $G$ is
  simple, it follows that $G'={1}$. But then $G$ is abelian, which contradicts
  the fact that $G$ has a conjugacy class $frak(C)$ with $|frak(C)| > 1$. This
  completes the proof.
]

#exercises-heading

Unless otherwise stated, all representations and characters are taken in the
field of complex numbers $CC$.

#source(245)
#exercise[
  Show that the maps
  $ a -> mat(i, 0; 0, -i),quad b -> mat(0, 1; 1, 0),"where" i=sqrt(-1), $
  and
  $ a -> mat(0, -1; 1, 0),b -> mat(0, 1; 1, 0), $
  define representations of the dihedral group $D_4$ defined in
  @exm:dihedral-quaternion-presentations(i).

  Discuss, from first principles, whether the representations are equivalent.
  Compute the characters of the representations, and use them to check
  equivalence.
] <exc:dihedral-two-matrix-representations>

#exercise[
  The _regular character_#idx("regular character")#idx("character", "regular")
  $rho_G$ of $G$ is the $CC$-character afforded by the left regular module
  $CC G$. Show that
  $ rho_G lr((x))=cases(|G| & "if" x=1, 0 & "if" x != 1). $
  Show that if $zeta in "Irr"(G)$, then $(zeta,rho_G)=deg zeta$ (compare with
  @th:split-group-algebra-dimensions(iii) and
  Exercise~@exc:idempotent-multiplicities).
] <exc:regular-character-multiplicities>

#exercise[
  Let $H ⊴ G$. Show that each character $mu$ of $G slash H$ can be lifted to a
  character $tilde(mu)$ of $G$, given by $tilde(mu)=mu compose f$, where
  $f:G -> G slash H$ is the natural homomorphism. Prove that $tilde(mu)$ is
  irreducible if and only if $mu$ is irreducible.

  Also show that
  $ tilde(rho)_(G slash H)=sum zeta(1)zeta, $
  where $rho_(G slash H)$ is the regular character of $G slash H$
  (Exercise~@exc:regular-character-multiplicities), and the sum is taken over
  all $zeta in "Irr"(G)$ such that $H subset.eq ker zeta$.
] <exc:quotient-character-lift>

#exercise[
  Prove that a set of distinct irreducible characters ${zeta_1,dots,zeta_t}$
  forms a basic set (that is, coincides with $"Irr"(G)$) if and only if
  $sum {zeta_i lr((1))}^2=|G|$.
] <exc:irreducible-degrees-basic-set>

#exercise[
  Prove that if $x in G$ satisfies the condition $zeta(x)=zeta(1)$ for all
  $zeta in "Irr"(G)$, then $x=1$.
] <exc:irreducible-character-kernel-intersection>

#exercise[
  Let $G=G_1 times G_2$, and let $zeta_i in "Irr"(G_i)$, $i=1,2$. Define
  $zeta_1 zeta_2$ by
  $(zeta_1 zeta_2)(g_1,g_2)=zeta_1 lr((g_1))zeta_2 lr((g_2))$, $g_i in G_i$.
  Show that $zeta_1 zeta_2 in "Irr"(G_1 times G_2)$. Using the orthogonality
  relations, prove that every irreducible complex character of $G$ can be
  expressed in the form $zeta_1 zeta_2$, with uniquely determined characters
  $zeta_i in "Irr"(G_i)$, $i=1,2$. (This result can also be proved by using
  representations, rather than characters, and applying Burnside's Theorem; see
  @th:outer-tensor-split-simple and @th:outer-tensor-separable below.)
] <exc:direct-product-characters>

#exercise[
  Find all characters of a finite abelian group $G$, and give explicit formulas
  for the corresponding central primitive idempotents in $CC G$. Prove that if
  $m$ is the exponent of $G$, and $omega_m$ is a primitive $m$-th root of $1$,
  then $QQ(omega_m)$ is a splitting field for $G$, (that is, $QQ(omega_m)G$ is a
  split semisimple $QQ(omega_m)$-algebra).
] <exc:abelian-group-cyclotomic-splitting-field>

#source(246)
#exercise[
  A _linear character_#idx("linear character")#idx("character", "linear") of $G$
  is a character of degree $1$. Prove that the number of distinct linear
  characters is $|G:G'|$, where $G'$ is the commutator subgroup of $G$. Show how
  $G'$ can be determined from the character table of $G$.
] <exc:linear-characters-derived-subgroup>

#exercise[
  Find the character tables of $S_3$, $D_4$, and $Q$, where $Q$ is the
  quaternion group of order $8$. Note that $D_4$ and $Q$ have the same character
  tables, but are not isomorphic. Show that the group algebras $CC D_4$ and
  $CC Q$ are isomorphic. (An example of two non-isomorphic groups, having
  isomorphic group algebras over algebraically closed fields of all
  characteristics, was found by Dade~@bib:Dade1971).
] <exc:equal-character-tables-dihedral-quaternion>

#exercise[
  Let $M$ be a left $CC G$-module, and let
  $"inv"_G lr((M))={m in M:g m=m,forall g in G}$#footnote[
    $"inv"_G lr((M))$ is the submodule of _$G$-invariants_#idx(
      "invariant (G-)",
    ) of $M$, and will often be called the _$G$-trivial submodule_#idx(
      "trivial submodule",
    ) of $M$.
  ]#idx("$\"inv\"_G M$ = $G$-invariants of $M$"). Prove that if $mu$ is the
  character afforded by $M$, then $(mu,1_G)=dim_CC lr(("inv"_G lr((M))))$. Also
  show that $(|G|^(-1)sum_(g in G) g)_l$ is a projection in
  $End_(CC G) lr((M))$, and that it carries $M$ onto $"inv"_G lr((M))$.
] <exc:character-invariants>

#exercise[
  (This exercise contains another approach to the orthogonality relations). Let
  $M,N$ be simple left $CC G$-modules, with characters $mu$ and $nu$,
  respectively. Let $M^*$ be the contragredient module of $M$, defined as
  $M^*=Hom_CC lr((M,CC))$, with the action of $G$ given by
  $ (x f)(m)=f(x^(-1)m),m in M,f in M^*,x in G. $
  #enum(
    numbering: "(i)",
    [Show that $M^*$ is a simple $CC G$-module, whose character $mu^*$ is given
      by $mu^*(x)=mu(x^(-1))=overline(mu(x))$, $x in G$.],
    [Prove that the vector spaces $M^* times.o_CC N$ and $Hom_CC lr((M,N))$ are
      isomorphic, via the map $sum f_i times.o n_i -> tau$, where
      $tau(m)=sum f_i lr((m))n_i$ for all $m in M$.],
    [View $M^* times.o_CC N$ as a $CC G$-module, with character $mu^* dot nu$,
      as in §@ss:finite-group-character-orthogonality. Prove that the
      isomorphism given in part (ii) carries $"inv"_G lr((M^* times.o_CC N))$
      onto $Hom_(CC G) lr((M,N))$.],
    [Prove that
      $
        "Tr" lr((frac(1, |G|) sum_(g in G) g,M^* times.o N))
        &=frac(1, |G|) sum_(g in G) mu^*(g)nu(g) \
        &=(nu,mu)=dim_CC lr(("inv"_G lr((M^* times.o N)))).
      $],
    [Using (iii) and Schur's Lemma, prove that
      $ (nu,mu)=cases(1 & "if" mu=nu, 0 & "otherwise"). $],
  )
  (A discussion of contragredient modules in a more general setting appears in
  §@ss:contragredient-modules).
] <exc:contragredient-character-orthogonality>

In problems
@exc:representation-character-summand–@exc:galois-conjugate-characters, $E$
denotes an arbitrary subfield of $CC$.

#source(247)
#exercise[
  Let $bold(T)$ be an $E$-representation of $G$, with $E$-character $tau$, and
  let $bold(U)$ be an irreducible $E$-representation, with character $eta$.
  Prove that $(tau,eta) != 0$ if and only if $bold(U)$ is a direct summand of
  $bold(T)$.
] <exc:representation-character-summand>

#exercise[
  Prove that if $M$ and $N$ are $E G$-modules, with characters $mu$ and $nu$,
  respectively, then $M tilde.equiv N$ if and only if $mu=nu$.
] <exc:equal-characters-isomorphic-modules>

#exercise[
  (Schur). Let $E$ be a subfield of $CC$, and $F$ a finite Galois extension of
  $E$ such that $F G$ is a split semisimple $F$-algebra (see
  §@ss:splitting-fields). Let $"Gal"(F slash E)$ denote the Galois group of $F$
  over $E$. For each $F$-representation $bold(M):G -> G L_n lr((F))$, and each
  automorphism $sigma in "Gal"(F slash E)$, let $attach(bold(M), tl: sigma)$ be
  the $F$-representation, which assigns to each $x in G$ the matrix obtained by
  applying $sigma$ to all the entries of $bold(M)(x)$ (see the last part of
  §@ss:splitting-fields for a more general version of this construction.) The
  representations ${attach(bold(M), tl: sigma):sigma in "Gal"(F slash E)}$ are
  called _$E$-conjugates_ of $bold(M)$. If $mu$ is the character of $bold(M)$,
  $sigma(mu)$ denotes the character of the representation
  $attach(bold(M), tl: sigma)$, and is called an _$E$-conjugate_#idx(
    "conjugate character",
  )#idx("character", "conjugate") of $mu$.
  #enum(
    numbering: "(i)",
    [Prove that if $zeta in "Irr"_F lr((G))$, then
      $sigma(zeta) in "Irr"_F lr((G))$ for all $sigma in "Gal"(F slash E)$.],
    [Prove that every character $mu in "Irr"_E lr((G))$ can be expressed in the
      form
      $ mu=m lr((sum_sigma sigma(zeta))), $
      where $zeta$ is an irreducible $F$-character $zeta$ such that
      $(zeta,mu) != 0$, ${sigma(zeta)}$ is the set of distinct conjugates of
      $zeta$, and $m$ is a positive integer.],
  )
  #hint([@exc:galois-conjugate-characters], caption: [Hints:])[
    (i) Show that $(sigma(mu),sigma(mu))=(mu,mu)$ for each $F$-character $mu$
    and each $sigma in "Gal"(F slash E)$.

    (ii) Let $bold(M)$ be an irreducible $E$-representation of $G$ with
    character $mu$. Apply Proposition~@prop:galois-orbit-simple-module-extension
    to conclude that $bold(M)^F$ is a direct sum of conjugates of one simple
    $F$-representation, with the different conjugates all appearing with the
    same multiplicity in the direct sum. Translate into the language of
    characters to obtain (ii).
  ]
] <exc:galois-conjugate-characters>

In the remaining problems, we return to $CC$-characters of $G$.

#exercise[
  (Feit-Thompson~@bib:Feit1963). Let $H ⊴ G$, and let $x in G$ be an element
  such that $C_G lr((x)) inter H=1$. Prove that $zeta^((i))(x)=0$ for all
  $zeta^((i)) in "Irr"(G)$ such that $H subset.eq.not ker zeta^((i))$.
  #hint([@exc:feit-thompson-character-vanishing])[
    The Second Orthogonality Relation @prop:first-second-character-orthogonality
    asserts that $sum |zeta^((i))(x)|^2=|C_G lr((x))|$. Letting
    $G slash H=overline(G)$, $x H=overline(x) in overline(G)$, etc., show that
    $|C_G lr((x))| <= |C_(overline(G)) lr((overline(x)))|$, and apply the Second
    Orthogonality Relation to the characters of $overline(G)$, lifted to $G$ as
    in Exercise~@exc:quotient-character-lift.
  ]
] <exc:feit-thompson-character-vanishing>

#exercise[
  (Littlewood). Let $e$ be a primitive idempotent in $CC G$ such that $CC G e$
  is a simple module affording the character $zeta$. Let
  $e=sum_(x in G) alpha_x x$. For each $t in G$ belonging to a conjugacy class
  $frak(C)$ of $G$, prove that
  $ zeta(t^(-1))=|C_G lr((t))|sum_(x in frak(C)) alpha_x. $
  #hint([@exc:littlewood-primitive-idempotent-character])[
    For each conjugacy class $frak(C)$ in $G$, define a linear map
    $T:CC G -> CC$, depending
    #source(248)
    on $frak(C)$, as follows:
    $ T lr((sum_(x in G) alpha_x x))=sum_(x in frak(C)) alpha_x. $
    Prove that $T(a b)=T(b a)$ for all $a,b in CC G$, and hence that
    $T(a b a^(-1))=T(b)$ if $a$ is invertible. Now let $e_zeta$ be a central
    primitive idempotent in $CC G$ corresponding to $zeta$, as in
    @prop:group-character-orthogonality-idempotents. Then
    $ e_zeta=e_1+dots+e_n,n=zeta(1), $
    where the ${e_i}$ are primitive orthogonal idempotents in the Wedderburn
    component $CC G e_zeta$. Prove that all such idempotents have the same
    elementary divisors, and hence are conjugate in $CC G$ (see also
    Exercise~@exc:semisimple-isomorphic-idempotents-conjugate). For each
    conjugacy class $frak(C)$ in $G$, apply $T$ as above to the expression for
    $e_zeta$, and obtain Littlewood's formula.
  ]
] <exc:littlewood-primitive-idempotent-character>

#exercise[
  (G. Higman~@bib:Higman1940; see also @bib:CurtisReiner1962[CR §~37]). Consider
  the integral group ring $ZZ G$, for a finite abelian group $G$. Let $u$ be a
  unit of finite order in $ZZ G$. Prove that $u=plus.minus x$, for some
  $x in G$.
  #hint([@exc:abelian-integral-group-ring-torsion-units])[
    Let $"Irr"(G)={zeta^((1)),dots,zeta^((s))}$. Show that the central primitive
    idempotents in $CC G$ are
    $ e_i=|G|^(-1)sum_(x in G) overline(zeta^((i))(x))x,1 <= i <= s. $
    Show that since $G$ is abelian, ${e_1,dots,e_s}$ is a basis of $CC G$, so
    that each $u in CC G$ can be expressed in two ways:
    $ u=sum_(x in G) alpha_x x=sum_(i=1)^s beta_i e_i. $
    Show that the coefficients ${alpha_x}$ and ${beta_i}$ are related by:
    $
      beta_i=sum_(x in G) alpha_x zeta^((i))(x),quad
      alpha_x=|G|^(-1)sum_(i=1)^s beta_i overline(zeta^((i))(x)).
    $
    Now let $u in ZZ G$, and suppose $u^m=1$ for some positive integer $m$. Then
    $beta_i^m=1$, $1 <= i <= s$. Suppose $x in G$ is an element such that
    $alpha_x != 0$. Then
    $
      |alpha_x|=|G|^(-1)|sum beta_i overline(zeta^((i))(x))|
      <= |G|^(-1)sum |beta_i overline(zeta^((i))(x))| <= 1.
    $
    Since $alpha_x in ZZ$, we have equality, and consequently
    $alpha_x=beta_i overline(zeta^((i))(x))$, $1 <= i <= s$. Hence, if $y != x$,
    $
      alpha_y=|G|^(-1)sum_(i=1)^s
      alpha_x zeta^((i))(x)overline(zeta^((i))(y))=0.
    $
  ]
] <exc:abelian-integral-group-ring-torsion-units>

#source(249)
#exercise[
  (Frobenius~@bib:Frobenius1896, pp.13,14). Let $g in G$, and let $N$ be the
  number of pairs $(x,y)$ such that $g=x y x^(-1)y^(-1)$. Prove that
  $ N=|G| dot sum_(zeta in "Irr"(G)) (zeta(g)/zeta(1)). $
  (See also Gallagher~@bib:Gallagher1962a.)
] <exc:frobenius-commutator-count>
