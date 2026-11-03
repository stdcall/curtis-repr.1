#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/16-decomposition.typ": *

#source(424)
== The Decomposition Map <sec:decomposition-map>

We begin in §@ss:modular-notation-terminology with a glossary of notation and
terminology, to be in force throughout the entire chapter. In
§@ss:grothendieck-groups we give a brief introduction to Grothendieck groups;
these will be studied more extensively in Chapter~10 of Volume~II. Finally, and
most important, §@ss:reduction-decomposition-map gives the definition and
elementary properties of the decomposition map, which assigns to each
$R G$-lattice $M$ the $k G$-module $overline(M)=M slash frak(p)M$, and induces a
homomorphism $G_0 lr((K G)) arrow G_0 lr((k G))$ of Grothendieck groups.

#heading(level: 3)[
  Notation and Terminology
] <ss:modular-notation-terminology>

All modules are assumed to be finitely generated, unless specifically stated
otherwise. Let $p$ be a rational prime number. A _$p$-modular system_ $(K,R,k)$
consists of a d.v.r. $R$ with quotient field $K$, maximal ideal $frak(p)=pi R$,
and residue class field $k=R slash frak(p)$ of characteristic $p$.#idx(
  "p-modular system",
) (Here, $pi$ is a prime element of the d.v.r. $R$.) Usually $K$ will be assumed
to have characteristic $0$, but we shall not impose this restriction in advance.

For example, a $p$-modular system arises from an algebraic number field $K$ by
choosing some non-archimedean $frak(p)$-adic valuation on $K$, and letting $R$
be its valuation ring, and $k$ the residue class field $R slash frak(p)$. We may
also choose $K$ to be the $frak(p)$-adic completion of such an algebraic number
field, and then its valuation ring $R$ is complete in the $frak(p)$-adic
topology (see §@ss:valuations-completions).

Throughout this section, $G$ denotes a finite group of order $|G|$. As in
§@ss:contragredient-modules, an _RG-lattice_ is a left $R G$-module having a
finite free $R$-basis. (Note that since $R$ is a P.I.D., every f.g. projective
$R$-module is necessarily $R$-free.) For each $R G$-lattice $M$, we set
$ overline(M)=M slash frak(p)M, $
so $overline(M)$ is a f.g. $k G$-module. Let bars denote “reduction mod
$frak(p)$”, so the element $m in M$ maps onto the element
$overline(m) in overline(M)$ under the natural map $M arrow overline(M)$.
Likewise, we shall occasionally write
$ overline(R)=R slash frak(p)=k, $
and denote the image of $a in R$, under the natural map $R arrow overline(R)$,
by $overline(a)$. Further (see §@ss:modules-dedekind-domains), we identify the
$R G$-lattice $M$ with its image $1 times.o M$ in $K times.o_R M$, so that
$K times.o_R M$ can be written in abbreviated form as $K M$, and viewed as the
set of $K$-linear combinations of the elements of $M$.

An element $x in G$ is called _$p$-regular_#idx("p-regular, Π-regular") if its
order is a $p'$-number (that is, its order is relatively prime to $p$), and
_$p$-irregular_#idx("p-irregular, Π-irregular") otherwise. Sometimes we will
call a $p$-regular element a _$p'$-element_ of $G$.#idx(
  "p′-element, Π′-element",
) We call $x in G$ a _$p$-element_ if the order of $x$ is a power of $p$.#idx(
  "p-element, Π-element",
) The identity element $1_G$ is the only $p$-element which is $p$-regular. As we
have seen in §@ss:background-group-theory, every $x in G$ is uniquely
expressible in the
#source(425)
form
$
  x=x' x'', quad "with" x' p"-regular, " x'' "a" p"-element, and"
  x' x''=x'' x'.
$
We call $x'$ the _$p$-regular part_ of $x$,#idx("p-regular part") and $x''$ the
_$p$-part_ of $x$.#idx("p-part") Finally, let
$ G_(p')={"all" p"-regular elements of" G}. $

#heading(level: 3)[
  Grothendieck Groups
] <ss:grothendieck-groups>

Let $A$ be an arbitrary ring, and let $cal(C)$ be some category of left
$A$-modules. A _short exact sequence_ (ses)#idx("short exact sequence") is an
exact sequence of $A$-modules
$ 0 arrow L arrow M arrow N arrow 0. $ <eq:short-exact-module-sequence>
If each module belongs to $cal(C)$, we call @eq:short-exact-module-sequence a
ses from $cal(C)$. We assume always that $0 in cal(C)$ and that if
$M,M' in cal(C)$, then also $M plus.o M' in cal(C)$. We assume further that the
collection of isomorphism classes of modules in $cal(C)$ forms a set. For
example, $cal(C)$ may be chosen as one of the following categories:
$ attach(frak(M), bl: A)="category of all left" A"-modules, " $
$ attach(op("mod"), bl: A)="category of all f.g. left" A"-modules, " $
$ cal(P)(A)="category of all f.g. projective left" A"-modules." $
In considering invariants of modules, one often constructs a map
$h:cal(C) arrow T$, which assigns to each module $M in cal(C)$ an element $h(M)$
in some fixed abelian group $T$. The map $h$ is usually additive on ses’s from
$cal(C)$, that is,
$ h(M)=h(L)+h(N) $ <eq:module-additive-invariant>
for each ses @eq:short-exact-module-sequence from $cal(C)$. In particular, this
implies that $h(M)$ depends only upon the isomorphism class of the module $M$.
For example, let $cal(C)$ be the category of all f.g. $CC G$-modules, and for
each $M in cal(C)$, let $h(M)$ be the character $mu$ afforded by $M$. Then $h$
maps $cal(C)$ into the additive group $op("ch")_(CC)G$ of virtual characters of
$G$. Clearly $h$ is additive on ses’s from $cal(C)$ in this case.

Returning to the general case, let $h:cal(C) arrow T$ be a map which is additive
on ses’s from $cal(C)$. We wish to extend $h$ so as to obtain an additive
homomorphism into $T$. Grothendieck groups provide the framework for such
extensions. We may think of this procedure as generalizing the passage from
ordinary characters to virtual characters.

#definition[
  Let $cal(C)$ be a category of $A$-modules. Let $upright(bold(F))$ be the free
  abelian group generated by symbols $(M)$, one for each isomorphism class of
  modules $M$ in $cal(C)$. Let $upright(bold(F))_0$ be the subgroup of
  $upright(bold(F))$ generated by all expressions
  $ (M)-(L)-(N) $
  #source(426)
  arising from all ses’s @eq:short-exact-module-sequence in $cal(C)$. The
  _Grothendieck group_ $K_0 lr((cal(C)))$ of the category $cal(C)$ is defined by
  $ K_0 lr((cal(C)))=upright(bold(F)) slash upright(bold(F))_0, $
  an abelian additive group. For $M in cal(C)$, let $[M]$ denote its image in
  $K_0 lr((cal(C)))$.
] <def:grothendieck-category-group>
#idx("Grothendieck group", target: [@def:grothendieck-category-group])

Each $x in K_0 lr((cal(C)))$ is expressible as a difference $[M]-[N]$ with
$M,N in cal(C)$, though not in a unique manner. Furthermore, it may occur that
$x=0$ even though $M$ is not isomorphic to $N$.

From the definition of $K_0 lr((cal(C)))$, we have at once:

#proposition[
  Let $T$ be some fixed abelian group, and let $h:cal(C) arrow T$ be a map which
  is additive on ses’s from $cal(C)$. Then there is a uniquely determined well
  defined additive homomorphism
  $ g:K_0 lr((cal(C))) arrow T $
  which extends $h$, and is given by the formula
  $ g([M]-[N])=h(M)-h(N) quad "for all" M,N in cal(C). $
] <prop:grothendieck-group-universal-property>

We postpone until Chapter~10 of Volume~II a more thorough investigation of such
Grothendieck groups, and concentrate here on those cases needed in our
discussion of modular representation theory.

#definition[
  The _Grothendieck group_ $G_0 lr((A))$ of the ring $A$ is defined by
  $ G_0 lr((A))=K_0 lr((attach(op("mod"), bl: A))). $
  Thus, $G_0 lr((A))$ is generated by expressions $[M]$, one for each
  isomorphism class $(M)$ of f.g. left $A$-modules $M$, with relations
  $ [M]=[M']+[M''] $
  for each ses $0 arrow M' arrow M arrow M'' arrow 0$ of f.g. left $A$-modules.

  The _projective class group_ $K_0 lr((A))$ of the ring $A$ is defined by
  $ K_0 lr((A))=K_0 lr((cal(P)(A))). $
  Thus, $K_0 lr((A))$ is generated by expressions $[P]$, one for each
  isomorphism class $(P)$ of f.g. projective left $A$-modules $P$, with
  relations
  $ [P plus.o P']=[P]+[P'] quad "for all" P,P' in cal(P)(A). $
] <def:ring-grothendieck-projective-groups>
#idx("G₀", target: [@def:ring-grothendieck-projective-groups])
#idx("K₀", target: [@def:ring-grothendieck-projective-groups])
#idx(
  "projective class group",
  target: [@def:ring-grothendieck-projective-groups],
)

(Note that each ses $0 arrow P' arrow P arrow P'' arrow 0$ of modules from
$cal(P)(A)$ must split, because $P''$ is $A$-projective. Hence, the defining
relations for $K_0 lr((A))$ can be expressed in the simpler form involving
direct sums, rather than exact sequences from $cal(P)(A)$.)

#source(427)
Given a $p$-modular system $(K,R,k)$ and a finite group $G$, we shall be
concerned mainly with the Grothendieck groups $G_0 lr((K G))$ and
$G_0 lr((k G))$, and with the projective class groups $K_0 lr((R G))$ and
$K_0 lr((k G))$. It should be remarked that each module $P in cal(P)(R G)$ is
necessarily a f.g. projective $R$-module, and is therefore an $R G$-lattice. Of
course, not every $R G$-lattice need be $R G$-projective. We shall show below
that if $char K=0$, then $G_0 lr((K G))$ is our old friend $op("ch") K G$, the
ring of virtual characters of $K G$-modules. As a first step in this direction,
we prove

#proposition[
  Let $A$ be a left artinian ring, and let ${V_1,dots,V_s}$ be a basic set of
  simple left $A$-modules. Then
  $ G_0 lr((A))=plus.o.big_(i=1)^s ZZ[V_i], $
  a free abelian group with basis ${[V_1],dots,[V_s]}$.
] <prop:artinian-grothendieck-simple-basis>
#proof[
  (All modules are assumed to be f.g. left $A$-modules.) Each $A$-module $U$ has
  a composition series
  $ U=U_0 supset U_1 supset dots supset U_(t+1)=0, $
  and the composition factors ${U_j slash U_(j+1)}$ are simple $A$-modules.
  Since the sequence
  $ 0 arrow U_(j+1) arrow U_j arrow U_j slash U_(j+1) arrow 0 $
  is exact for each $j$, it follows from the definition of $G_0 lr((A))$ that
  $ [U]=sum_(j=0)^t [U_j slash U_(j+1)] quad "in" G_0 lr((A)). $
  Hence we may write
  $ [U]=sum_(i=1)^s r_i lr((U))[V_i] quad "in" G_0 lr((A)), $
  where for each $i$, $r_i lr((U))$ is the multiplicity of $V_i$ as composition
  factor of $U$. Note that $r_i lr((U))$ is well-defined, by the Jordan-Hölder
  Theorem. Clearly, $r_i$ is additive on ses’s of $A$-modules. Thus by
  @prop:grothendieck-group-universal-property there is a well-defined additive
  homomorphism#footnote[
    $ZZ^((n))$ denotes the free abelian group on $n$ generators.
  ]
  $ g:G_0 lr((A)) arrow ZZ^((s)), $
  given by
  $ g[U]=(r_1 lr((U)),dots,r_s lr((U))),U=A"-module." $
  It is clear that $g$ is surjective.

  #source(428)
  On the other hand, there is an obvious homomorphism
  $f:ZZ^((s)) arrow G_0 lr((A))$, defined by
  $ f(r_1,dots,r_s)=sum r_i [V_i],r_i in ZZ. $
  We have $g f=1$, so $f$ and $g$ are isomorphisms, and are inverses of one
  another. This completes the proof that $[V_1],dots,[V_s]$ form a free
  $ZZ$-basis of $G_0 lr((A))$. An analogous argument will be used in the proof
  of Proposition @prop:semiperfect-projective-class-basis below.
]

Our next task is to determine the additive structure of $K_0 lr((A))$ for the
case where $A$ is a semiperfect ring. Recall from §@ss:projective-covers that
the ring $A$ is _semiperfect_ if it has the following two properties:

(i) $A slash (rad A)$ is a semisimple artinian ring.

(ii) Every idempotent in $A slash (rad A)$ can be lifted to an idempotent in
$A$.

The semiperfect rings with which we shall be mainly concerned are the rings
$R G$ and $k G$, where $(K,R,k)$ is a $p$-modular system. We proved in
§@sec:idempotents-krull-schmidt-projective-covers that $R G$ is semiperfect
provided that $R$ is complete in the $frak(p)$-adic topology, and that $k G$ is
semiperfect for an arbitrary field $k$. We should remark that $R G$ is also
semiperfect whenever $K$ is a splitting field for $G$, whether or not the d.v.r.
$R$ is complete; this follows at once from
@prop:finite-algebra-local-base-radical and Exercise
@exc:split-order-idempotent-lifting.

#proposition[
  Let $A$ be a semiperfect ring, and let ${P_1,dots,P_r}$ be a basic#footnote[
    This means that every f.g. indecomposable projective left $A$-module is
    isomorphic to exactly one of the ${P_i}$.
  ] set of f.g. indecomposable projective left $A$-modules. Then
  $ K_0 lr((A))=plus.o.big_(i=1)^r ZZ[P_i], $
  a free abelian group with basis ${[P_1],dots,[P_r]}$.
] <prop:semiperfect-projective-class-basis>
#idx(
  "basic set of indecomposable projective modules",
  target: [@prop:semiperfect-projective-class-basis],
)
#proof[
  All modules considered here are assumed f.g. For the purposes of this proof,
  let $overline(A)=A slash N$, where $N=rad A$. In §@ss:projective-covers (see
  especially @cor:semiperfect-projective-cover-properties) we proved that the
  isomorphism classes of projective left $A$-modules $P$ correspond bijectively
  to the classes of projective $overline(A)$-modules, the correspondence being
  given by $P arrow.l.r P slash N P$. The indecomposable projective $A$-modules
  then correspond to the simple $overline(A)$-modules. Since each
  $overline(A)$-module is expressible as a finite direct sum of simple
  $overline(A)$-modules with uniquely determined multiplicities, it follows that
  each projective $A$-module $P$ can be expressed as a direct sum
  $ P tilde.equiv product_(i=1)^r (P_i)^((n_i)) $
  with uniquely determined multiplicities ${n_i}$. It follows as in the proof of
  #source(429)
  @prop:artinian-grothendieck-simple-basis that there is a well defined additive
  map $g:K_0 lr((A)) arrow ZZ^((r))$, given by
  $ g[P]=(n_1,dots,n_r). $
  Then $g$ is surjective, and is an isomorphism because it has an inverse $f$
  given by
  $ f(n_1,dots,n_r)=sum_(i=1)^r n_i [P_i],n_i in ZZ. $
  This completes the proof.
]

#remark(numbered: false)[
  The vital point of the preceding proof is that the K-S-A Theorem is valid for
  f.g. projective modules over a semiperfect ring $A$. The hypothesis that $A$
  be semiperfect was needed only to insure the validity of this theorem. Thus,
  the assertions in @prop:semiperfect-projective-class-basis remain true for any
  ring $A$, semiperfect or not, as long as the K-S-A Theorem holds for f.g.
  projective $A$-modules.
]

Now let $K$ be an arbitrary field, $G$ a finite group, and let us show that the
Grothendieck group $G_0 lr((K G))$ can be made into a commutative ring, with
multiplication corresponding to (inner) tensor products of $K G$-modules. For
$M$ and $N$ a pair of f.g. left $K G$-modules, let $M times.o_K N$ be their
usual inner tensor product, which is again a $K G$-module. We intend to define
multiplication in $G_0 lr((K G))$ by starting with the formula
$ [M][N]=[M times.o_K N], $ <eq:grothendieck-tensor-multiplication>
and then extending the definition in an obvious manner to products of the form
$(sum a_i [M_i])(sum b_j [N_j])$, $a_i,b_j in ZZ$. The difficulty lies in
showing that multiplication is then well defined. We may overcome this
difficulty as follows. As in Definition
@def:ring-grothendieck-projective-groups, we may write
$ G_0 lr((K G))=upright(bold(F)) slash upright(bold(F))_0, $
where $upright(bold(F))$ is the free abelian group generated by symbols $(M)$,
one for each isomorphism class of f.g. $K G$-modules $M$, and
$upright(bold(F))_0$ is the subgroup of $upright(bold(F))$ generated by all
expressions
$ (M)-(L)-(N) $
arising from ses’s
$ 0 arrow L arrow M arrow N arrow 0 $
of f.g. $K G$-modules. Since $upright(bold(F))$ is a free abelian group, we may
define multiplication in $upright(bold(F))$ unambiguously by specifying how its
generators multiply. Specifically, we put
$ (M)(N)=(M times.o_K N) $ <eq:free-module-class-tensor-product>
#source(430)
for each pair of $K G$-modules $M$ and $N$. Then $upright(bold(F))$ becomes a
commutative associative ring with identity element. To insure that this
multiplication carries over to $G_0 lr((K G))$, it suffices to verify that
$upright(bold(F))_0$ is an _ideal_ of $upright(bold(F))$. Now let
@eq:short-exact-module-sequence be an exact sequence of $K G$-modules; it is
obviously split as a sequence of $K$-modules. But then for any $K G$-module $X$,
the sequence of $K G$-modules
$ 0 arrow X times.o_K L arrow X times.o_K M arrow X times.o_K N arrow 0 $
is exact (and split over $K$). Therefore
$
  (X){(M)-(L)-(N)}=(X times.o M)-(X times.o L)-(X times.o N)
  quad "in" upright(bold(F)),
$
which lies in $upright(bold(F))_0$, so $upright(bold(F))_0$ is an ideal in
$upright(bold(F))$. Therefore $G_0 lr((K G))$ is indeed a commutative ring with
identity element. Notice that @eq:grothendieck-tensor-multiplication
automatically holds true in $G_0 lr((K G))$, by virtue of formula
@eq:free-module-class-tensor-product used to make $upright(bold(F))$ into a
ring.

We are now ready to establish the connection between our Grothendieck ring
$G_0 lr((K G))$ and the ring of virtual characters $op("ch") K G$ defined in
§@ss:finite-group-character-orthogonality.

#proposition[
  Let $K$ be a field of characteristic $0$, and $G$ a finite group. Then there
  is an isomorphism of rings
  $ G_0 lr((K G)) tilde.equiv op("ch") K G, $
  obtained by assigning to each f.g. $K G$-module $M$ the character $mu$ of $G$
  afforded by $M$.
] <prop:grothendieck-character-ring>
#idx("ch KG", target: [@prop:grothendieck-character-ring])
#proof[
  Define $psi:G_0 lr((K G)) arrow op("ch") K G$ by $psi[M]=mu$. Since $psi$ is
  additive on ses’s of $K G$-modules, it is clear from
  @prop:grothendieck-group-universal-property that $psi$ is well defined on
  $G_0 lr((K G))$. Since $G_0 lr((K G))$ is $ZZ$-free on the simple
  $K G$-modules by @prop:artinian-grothendieck-simple-basis, while
  $op("ch") K G$ is $ZZ$-free on the irreducible $K$-characters of $G$, it is
  clear that $psi$ is an isomorphism of additive groups. Moreover, if $N$ is a
  $K G$-module with character $nu$, then $M times.o_K N$ affords the character
  $mu nu$. This implies at once that $psi$ is a ring isomorphism, as claimed.
]

For a $p$-modular system $(K,R,k)$ and a finite group $G$, we expect the
Grothendieck ring $G_0 lr((k G))$ to serve as an object of investigation, rather
than the character ring $op("ch") k G$. Indeed, a $k G$-module is _never_
uniquely determined by its character. In addition, we shall be using the
projective class group $K_0 lr((R G))$, which also has a ring structure, as we
shall see later on.

#heading(level: 3)[
  Reduction mod $frak(p)$ and the Decomposition Map
] <ss:reduction-decomposition-map>

Let $(K,R,k)$ be a $p$-modular system, and $G$ any finite group. Thus $R$ is a
d.v.r. with quotient field $K$, maximal ideal $frak(p)$, and residue class field
$k$ of characteristic $p$. We shall obtain the first of several important
connections
#source(431)
among $K G$-modules, $R G$-modules, and $k G$-modules. The construction begins
with a left $K G$-module $V$. We shall show that $V$ contains a full left
$R G$-lattice $M$. Then $overline(M)=M slash frak(p)M$ is a $k G$-module, which
we shall say is obtained from $M$ by “reduction mod $frak(p)$”. For a fixed
$K G$-module $V$, there are in general many choices for the full $R G$-lattice
$M$ in $V$, and the $k G$-modules $overline(M)$ thus obtained need not be
isomorphic to one another. Nevertheless, we shall prove that the above
construction yields a well-defined homomorphism
$G_0 lr((K G)) arrow G_0 lr((k G))$, called the _decomposition homomorphism_.
This observation is the starting point of the theory of modular representations.
In later sections, we shall interpret the decomposition map in terms of Brauer
characters, and relate it to $K_0 lr((R G))$ and $K_0 lr((k G))$.

As in §@ss:contragredient-modules and §@ss:modular-notation-terminology, an
$R G$-lattice is a left $R G$-module having a finite free $R$-basis. Since $R$
is a P.I.D., the structure theorem for $R$-modules shows that a f.g.
$R G$-module $M$ is an $R G$-lattice if and only if $M$ is $R$-torsionfree.
Therefore, submodules of $R G$-lattices are necessarily sublattices.

#definition[
  Let $V$ be a f.g. left $K G$-module. A _full RG-lattice_ $M$ in $V$ is an
  $R G$-lattice $M$ contained in $V$, such that $K M=V$.
] <def:full-group-lattice>

We remark that for each full $R G$-lattice $M$ in $V$, we have
$ K times.o_R M tilde.equiv K M $
as $K G$-modules. Indeed, the obvious surjection $K times.o_R M arrow K M$ is a
$K G$-homomorphism. On the other hand, it is a $K$-isomorphism because of the
fact that $M$ is $R$-torsionfree. For further discussion of this matter, see
§@ss:modules-dedekind-domains and @prop:localized-module-finite-model.

#lemma[
  Let $V$ be any f.g. left $K G$-module. An $R G$-submodule $M$ of $V$ is a full
  $R G$-lattice in $V$ if and only if $M$ satisfies the conditions:

  (i) $M$ has a finite $R$-basis, and

  (ii) $K M=V$.
] <lem:full-group-lattice-basis-criterion>
#proof[
  If $M$ is a full $R G$-lattice in $V$, then (i) and (ii) clearly hold.
  Conversely, if $M$ is an $R G$-submodule of $V$ satisfying (i), then $M$ is an
  $R G$-lattice, and (ii) shows that $M$ is full in $V$.
]

We remark that if $M$ is a full $R G$-lattice in $V$, then for each $R$-basis
${m_1,dots,m_d}$ of $M$, the elements ${1 times.o m_1,dots,1 times.o m_d}$ form
a $K$-basis of $K times.o_R M$. After the usual identification of $M$ with
$1 times.o M$, we may conclude:

#corollary[
  If $M$ is a full $R G$-lattice in $V$, then every $R$-basis of $M$ is also a
  $K$-basis of $V$.
] <cor:full-lattice-basis-field-basis>

#source(432)
Since equivalence (over $K$) of $K$-representations of $G$ is the result of
change of $K$-basis in a $K G$-module, the following remark is an immediate
consequence of @cor:full-lattice-basis-field-basis (see also
@prop:field-representation-integral-form):

#corollary[
  Every $K$-representation of $G$ is equivalent (over $K$) to an
  $R$-representation of $G$, that is, a representation by matrices with entries
  in $R$.
] <cor:modular-representation-integral-form>

If $R$ is an arbitrary Dedekind domain with quotient field $K$, rather than a
d.v.r., then it is not necessarily true that every $K$-representation of $G$ is
$K$-equivalent to an $R$-representation (see §@sec:lattices-orders for a full
discussion of this situation). Another subtlety is that two $R$-representations
of $G$ which are $K$-equivalent need not be $R$-equivalent (see Exercise
@exc:nonisomorphic-full-lattice-reductions and §@sec:lattices-orders).

We now turn to the question of _existence_ of full $R G$-lattices in
$K G$-modules. For the rest of the section, $(K,R,k)$ continues to denote a
$p$-modular system. The next result is a special case of a general statement
about $R$-orders in $K$-algebras (see @cor:full-order-lattice-existence).

#proposition[
  Every f.g. left $K G$-module $V$ contains full $R G$-lattices.
] <prop:full-group-lattice-existence>
#proof[
  We have $V=sum_(i=1)^d K v_i$ for some $K$-basis ${v_i}$ of $V$. Put
  $ M=sum_(i=1)^d R G v_i. $
  Then $M$ is f.g./$R$, and is $R$-torsionfree, hence is an $R G$-lattice in
  $V$. Clearly $K M=V$, so $M$ is a full $R G$-lattice, as required.
]

Now let $a arrow overline(a)$, $a in R$, denote the natural map
$R arrow R slash frak(p)=k$. Let $M$ be a full $R G$-lattice in a $K G$-module
$V$. Then $overline(M)=M slash frak(p)M$ is an $R G$-module annihilated by
$frak(p)$, and hence can be made into a $k G$-module, with the action of $k G$
given by
$
  lr((sum_(x in G) overline(a_x) x)) overline(m)
  =sum_(x in G) overline(a_x x m),quad a_x in R,m in M.
$
We call $overline(M)$ the $k G$-module obtained from $M$ by _reduction mod
$frak(p)$_.

This construction can be reformulated in various ways. First, every
$K$-representation of $G$ is equivalent to an $R$-representation of $G$, by
@cor:modular-representation-integral-form. Let
$upright(bold(T)):G arrow GL_d lr((R))$ be an $R$-representation of $G$, given
by
$ upright(bold(T))(x)=(a_(i j) lr((x))),a_(i j) lr((x)) in R,x in G. $
Then define $overline(upright(bold(T))):G arrow GL_d lr((k))$ by
$ overline(upright(bold(T)))(x)=(overline(a_(i j) lr((x)))),x in G. $

#source(433)
Clearly $overline(upright(bold(T)))$ is a $k$-representation of $G$. If
$upright(bold(T))$ is the $R$-representation of $G$ afforded by a full
$R G$-lattice $M$ in $V$, with respect to an $R$-basis ${m_1,dots,m_d}$ of $M$,
then ${overline(m_1),dots,overline(m_d)}$ is a $k$-basis of $overline(M)$, and
$overline(upright(bold(T)))$ is the $k$-representation of $G$ afforded by
$overline(M)$ with respect to the basis ${overline(m_1),dots,overline(m_d)}$.

A second interpretation of $overline(M)$ is given by the formula
$ overline(M) tilde.equiv k times.o_R M. $
To prove this, we apply $ast times.o M$ to the exact sequence
$ 0 arrow frak(p) arrow R arrow k arrow 0, $
so we obtain an exact sequence
$ frak(p) times.o M arrow R times.o M arrow k times.o M arrow 0, $
where $times.o$ means $times.o_R$. Identifying $R times.o M$ with $M$, the image
of $frak(p) times.o M$ is identified with $frak(p)M$, and we have
$M slash frak(p)M tilde.equiv k times.o M$, as claimed.

As we pointed out at the beginning of the subsection, two full $R G$-lattices
$M$ and $N$ in $V$ may yield non-isomorphic $k G$-modules $overline(M)$ and
$overline(N)$. Some order is restored to the situation, however, if we work with
Grothendieck groups. We remark that two matrix-theoretic proofs of the next
result, due to Brauer-Nesbitt~@bib:Brauer1937, are given in
@bib:CurtisReiner1962[CR §82].

#proposition[
  Let $M$ and $N$ be a pair of full $R G$-lattices in a $K G$-module $V$. Then
  $[overline(M)]=[overline(N)]$ in $G_0 lr((k G))$, or equivalently, the
  $k G$-modules $overline(M)$ and $overline(N)$ have the same composition
  factors.
] <prop:lattice-reduction-composition-factors>
#proof[
  By Lemma @lem:full-group-lattice-basis-criterion, the sum $M+N$ is a full
  $R G$-lattice in $V$ containing both $M$ and $N$. Therefore it is sufficient
  to prove the result for full $R G$-lattices $L$ and $M$ in $V$ such that
  $L subset.eq M$. Since $L$ and $M$ are full lattices in $V$, we have
  $frak(p)^n M subset.eq L$ for some $n$. Thus $M slash L$ is a finitely
  generated $R$-module annihilated by $frak(p)^n$, and has finite length. Hence
  it also has finite length as an $R G$-module. An $R G$-composition series of
  $M slash L$ therefore shows that it suffices to assume that $L$ is a maximal
  submodule of $M$. We claim that $frak(p)M subset.eq L$. Otherwise,
  $L+frak(p)M$ is an $R G$-lattice in $M$ properly containing $L$, so that
  $L+frak(p)M=M$ by maximality of $L$. This implies that $L=M$, by Nakayama’s
  Lemma @lem:nakayama, contrary to assumption. Thus $frak(p)M subset.eq L$, and
  we have
  $ frak(p)L subset.eq frak(p)M subset.eq L subset.eq M. $
  Now by @prop:artinian-grothendieck-simple-basis, $[overline(L)]=[overline(M)]$
  in $G_0 lr((k G))$ if and only if $overline(L)$ and $overline(M)$ have the
  same composition factors, so we have to prove that the composition factors of
  $M slash frak(p)M$ and $L slash frak(p)L$ are the same (up to order of
  occurrence). These $k G$-modules have the composition factors of
  $L slash frak(p)M$ in common, so it suffices to prove that $M slash L$ and
  $frak(p)M slash frak(p)L$ have the same composition factors. But $frak(p)$ is
  a principal ideal $pi R$, so that $frak(p)M=pi M$, $frak(p)L=pi L$, and
  $ frak(p)M slash frak(p)L=pi M slash pi L. $

  #source(434)
  Hence $M slash L tilde.equiv frak(p)M slash frak(p)L$ as $R G$-modules, with
  the isomorphism given by multiplication by $pi$. Thus the $k G$-modules
  $frak(p)M slash frak(p)L$ and $M slash L$ are isomorphic over $k G$, and the
  proof is complete.
]

#proposition[
  There exists a homomorphism of abelian groups
  $ d:G_0 lr((K G)) arrow G_0 lr((k G)). $
  For a f.g. left $K G$-module $V$, the map assigns to $[V]$ in $G_0 lr((K G))$
  the element $[overline(M)]$ in $G_0 lr((k G))$, where $M$ is any full
  $R G$-lattice in $V$.
] <prop:decomposition-homomorphism-existence>
#proof[
  We propose to define $d$ by setting $d[V]=[overline(M)]$, where $M$ is a full
  $R G$-lattice in $V$. By @prop:lattice-reduction-composition-factors, the
  image $[overline(M)]$ is independent of the choice of $M$ in $V$. We have to
  prove that $d$ is additive on short exact sequences (ses’s). Given a ses of
  $K G$-modules
  $ 0 arrow V_1 arrow V_2 arrow^phi V_3 arrow 0, $
  let $M_2$ be a full $R G$-lattice in $V_2$, and set $M_3=phi(M_2)$. Then $M_3$
  is an $R G$-lattice in $V_3$, and
  $ K M_3=K phi(M_2)=phi(K M_2)=V_3, $
  so $M_3$ is full in $V_3$. Letting $V_1 arrow V_2$ be the inclusion map, we
  set $M_1=M_2 inter V_1$, and obtain a ses of $R G$-modules
  $ 0 arrow M_1 arrow M_2 arrow^phi M_3 arrow 0. $
  <eq:decomposition-lattice-exact-sequence>
  Then $0 arrow K M_1 arrow K M_2 arrow K M_3 arrow 0$ is exact, whence
  $K M_1=V_1$, and $M_1$ is full in $V_1$. Since $M_3$ is $R$-projective, the
  sequence @eq:decomposition-lattice-exact-sequence is split as a sequence of
  $R$-modules. Hence, tensoring it with $k$ over $R$ preserves exactness. But
  $k times.o M_i tilde.equiv overline(M_i)$, as we observed in the remarks
  following the definition of $overline(M)$. We therefore have an exact sequence
  of $k G$-modules
  $
    0 arrow overline(M_1) arrow overline(M_2)
    arrow overline(M_3) arrow 0.
  $
  Hence $[overline(M_2)]=[overline(M_1)]+[overline(M_3)]$ in $G_0 lr((k G))$, so
  that $d[V_2]=d[V_1]+d[V_3]$, completing the proof.
]

By Proposition @prop:artinian-grothendieck-simple-basis, $G_0 lr((K G))$ and
$G_0 lr((k G))$ have $ZZ$-bases ${[Z_1],dots,[Z_s]}$ and ${[F_1],dots,[F_r]}$,
respectively, where ${Z_i}_(1 <= i <= s)$ and ${F_j}_(1 <= j <= r)$ are basic
sets of simple modules over the group algebras $K G$ and $k G$, respectively.
Then
$ d[Z_i]=sum_(j=1)^r d_(i j)[F_j],1 <= i <= s, $
<eq:decomposition-coefficients>
#source(435)
where $d_(i j)$ is the multiplicity of $F_j$ as a composition factor of the
$k G$-module obtained by reduction mod $frak(p)$ of a full $R G$-lattice in
$Z_i$, $1 <= i <= s$. The $s times r$ matrix $(d_(i j))$, whose entries are
defined by @eq:decomposition-coefficients, is the transpose of the matrix of $d$
with respect to the ordered bases ${[Z_i]}$ of $G_0 lr((K G))$ and ${[F_j]}$ of
$G_0 lr((k G))$, respectively.

#definition[
  The homomorphism of abelian groups
  $ d:G_0 lr((K G)) arrow G_0 lr((k G)), $
  defined in @prop:decomposition-homomorphism-existence, is called the
  _decomposition map_ (or _decomposition homomorphism_) associated with the
  $p$-modular system $(K,R,k)$ and the finite group $G$. The $s times r$ matrix
  $upright(bold(D))=(d_(i j))$, defined by @eq:decomposition-coefficients, is
  called the _decomposition matrix_.
] <def:decomposition-map-matrix>
#idx("decomposition map", target: [@def:decomposition-map-matrix])
#idx("decomposition matrix", target: [@def:decomposition-map-matrix])

#examples(numbered: false)[
  (i) $G=S_3,p=2$, and the $p$-modular system is $(QQ,R,k)$, where $QQ$ is the
  rational field, $R$ is the ring of $2$-adic integers in $QQ$, $frak(p)=2R$,
  and $k=R slash frak(p)=ZZ slash 2ZZ$. In this case there are three simple
  $QQ G$-modules $Z_1,Z_2,Z_3$, affording the trivial representation, the sign
  representation, and the simple module of dimension $2$, respectively. There
  are two simple $k G$-modules $F_1$ and $F_2$, affording the trivial
  representation, and the $2$-dimensional representation obtained by reduction
  mod $2$ from $Z_3$, respectively. We leave it to the reader to verify this
  fact, and that the decomposition matrix is
  $ upright(bold(D))=mat(delim: "[", 1, 0; 1, 0; 0, 1). $

  (ii) Let $G=S_4,p=2$, and let $(QQ,R,k)$ be the $2$-modular system defined in
  Example (i). There are $5$ simple $QQ G$-modules ${Z_1,dots,Z_5}$ of
  dimensions $1,1,2,3,3$, respectively. Let $H$ be the elementary abelian normal
  $2$-subgroup of $G$ generated by products of commuting transpositions. Then
  $G slash H tilde.equiv S_3$, and $Z_1,Z_2,Z_3$ are the simple modules of $G$
  on which $H$ acts trivially, and correspond to the simple modules in Example
  (i). The representation of $G$ on ${1,2,3,4}$ is $2$-transitive, hence by
  Exercise @exc:doubly-transitive-character it can be expressed as the direct
  sum of the trivial representation and an irreducible representation of degree
  $3$, which is realized in the rational field $QQ$. The other $3$-dimensional
  representation arises by tensoring the first one with the sign representation.
  By @prop:normal-p-subgroup-brauer-kernel, the normal $2$-subgroup $H$ acts
  trivially on each simple $k G$-module, and hence there are $2$ simple
  $k G$-modules $F_1$ and $F_2$, which arise from those of $S_3$ described in
  example (i). The decomposition matrix is
  $ upright(bold(D))=mat(delim: "[", 1, 0; 1, 0; 0, 1; 1, 1; 1, 1). $
] <exm:small-symmetric-decomposition-matrices>

#source(436)
#heading(level: 3)[
  Behavior of Grothendieck Groups under Extension of Ground Field
] <ss:grothendieck-ground-field-extension>

Let $(K,R,k)$ be a $p$-modular system,#idx("p-modular system") where $char K=0$,
and let $K'$ be a finite extension field of $K$. We wish to find a $p$-modular
system $(K',R',k')$ which extends the original system $(K,R,k)$. This can always
be done, by the following result:

#proposition[
  Let $(K,R,k)$ be a $p$-modular system, where $R$ is a d.v.r. with maximal
  ideal $frak(p)$ and residue class field $k=R slash frak(p)$. Let $v$ denote
  the discrete valuation on $K$ whose valuation ring is $R$. Then for each field
  $K'$ which is a finite extension of $K$, the valuation $v$ can be extended to
  a discrete valuation $v'$ on $K'$. Let $R'$ be the valuation ring of $v'$,
  $frak(p)'$ the maximal ideal of $R'$, and set $k'=R' slash frak(p)'$. Then
  $ R' inter K=R,frak(p)' inter K=frak(p), $
  and $k'$ is a finite extension of the field $k$, in a natural manner.
] <prop:modular-system-valuation-extension>
#proof[
  This is a standard result in algebraic number theory; see, for example,
  Weiss~@bib:Weiss1963, section~2-4, as well as the discussion in
  §@ss:valuations-completions and in §@ss:extension-ground-ring-local-theory
  below, or @bib:Reiner1975[MO §12]. Here, we shall give a brief summary of the
  relevant facts, omitting proofs.

  The d.v.r. $R$ is the valuation ring associated with some discrete (rank $1$)
  valuation $v$ on $K$, and we have
  $ R={x in K:v(x) >= 0},frak(p)={x in K:v(x)>0}. $
  Let $hat(K)$ be the $frak(p)$-adic completion of $K$ (see
  §@ss:valuations-completions); the valuation $v$ extends to a discrete
  valuation $hat(v)$ on $hat(K)$. Let $Omega$ be some algebraic closure of
  $hat(K)$. Then $hat(v)$ extends to a valuation $w$ on $Omega$, defined by
  $ w(x)=1/n hat(v)(N x),n=dim_(hat(K)) hat(K)(x),x in Omega, $
  where $N x$ denotes the norm of $x$ from $hat(K)(x)$ to $hat(K)$. For each
  field $E$ such that $hat(K) subset.eq E subset.eq Omega$, with
  $dim_(hat(K)) E$ finite, the restriction of $w$ to $E$ yields a discrete
  valuation $w_E$ on $E$, and $w_E$ is the unique extension of $hat(v)$ from
  $hat(K)$ to $E$.

  Now $Omega$ is an algebraically closed field containing $K$. Choose a
  $K$-embedding $theta:K' arrow Omega$, and put $v'=w compose theta$. Then $v'$
  is a discrete valuation on $K'$ extending $v$, with valuation ring $R'$ and
  maximal ideal $frak(p)'$, where
  $
    R'={a in K':v' lr((a)) >= 0},
    frak(p)'={a in K':v' lr((a))>0}.
  $

  #source(437)
  The composite map $R arrow R' arrow k'$ has kernel $R inter frak(p)'$. This
  intersection is $frak(p)$, so we obtain a natural embedding of $k$ in $k'$, as
  desired.
]

For convenience, we will call the above $p$-modular system $(K',R',k')$ a
_finite extension_ of the $p$-modular system $(K,R,k)$.#idx(
  "finite extension of p-modular system",
) We are going to investigate the behavior of $G_0 lr((K G))$, $K_0 lr((k G))$
and $G_0 lr((k G))$, under ground field extension.

#proposition[
  Let $(K',R',k')$ be a finite extension of the $p$-modular system $(K,R,k)$.
  Then there are additive homomorphisms
  $
    G_0 lr((K G)) arrow G_0 lr((K' G)),
    K_0 lr((k G)) arrow K_0 lr((k' G)),
    G_0 lr((k G)) arrow G_0 lr((k' G)),
  $
  defined by tensoring with $K'$, $k'$ and $k'$, respectively. All three maps
  are injections. Further, both of the maps
  $
    K_0 lr((k G)) arrow K_0 lr((k' G)),
    G_0 lr((k G)) arrow G_0 lr((k' G)),
  $
  are split injections, that is, the embeddings identify $K_0 lr((k G))$ and
  $G_0 lr((k G))$ as $ZZ$-direct summands of $K_0 lr((k' G))$ and
  $G_0 lr((k' G))$, respectively.
] <prop:grothendieck-scalar-extension-injections>
#proof[
  Let ${V_1,dots,V_s}$ be a basic set of simple $K G$-modules. Since $char K=0$,
  ${V_1^(K'),dots,V_s^(K')}$ are semisimple $K' G$-modules, no two of which have
  a simple submodule in common, by Exercise
  @exc:base-extension-common-composition-factor. It then follows from
  @prop:artinian-grothendieck-simple-basis and the fact that tensoring with $K'$
  preserves ses’s, that there exists an injection of $ZZ$-modules
  $G_0 lr((K G)) arrow G_0 lr((K' G))$, which takes the element $[V_i]$ in
  $G_0 lr((K G))$ onto $[V_i^(K')]$ in $G_0 lr((K' G))$.

  Now let ${F_1,dots,F_r}$ be a basic set of simple $k G$-modules. By Corollary
  @cor:group-algebra-multiplicity-free-extension, each module $F_i^(k')$ is a
  direct sum of simple $k' G$-modules, no two of which are isomorphic. By
  Exercise @exc:base-extension-common-composition-factor, the modules $F_i^(k')$
  and $F_j^(k')$ have no simple submodules in common, if $i!=j$. It is then
  clear, using @prop:artinian-grothendieck-simple-basis again, that the map
  given by $[F_i] arrow [F_i^(k')]$, $1 <= i <= r$, defines an injection
  $G_0 lr((k G)) arrow G_0 lr((k' G))$. This injection identifies
  $G_0 lr((k G))$ with a $ZZ$-direct summand of $G_0 lr((k' G))$.

  Finally, tensoring with $k'$ is easily seen to define an homomorphism of
  $ZZ$-modules $K_0 lr((k G)) arrow K_0 lr((k' G))$. By
  @prop:semiperfect-projective-class-basis, $K_0 lr((k G))$ has a $ZZ$-basis
  ${[P_1],dots,[P_r]}$, where ${P_1,dots,P_r}$ are a basic set of f.g.
  indecomposable projective $k G$-modules. From §@ss:projective-covers, each
  module $P_i$ is the projective cover of the simple $k G$-module
  $P_i slash (rad P_i)$. It is easily checked that $P_i^(k')$ is the projective
  cover of $(P_i slash (rad P_i))^(k')$. By
  @prop:semiperfect-projective-class-basis and the uniqueness of projective
  covers, the fact that $K_0 lr((k G)) arrow K_0 lr((k' G))$ is a split
  injection follows from the corresponding result about the map
  $G_0 lr((k G)) arrow G_0 lr((k' G))$, and the proof is complete.
]

Examples show that the map $G_0 lr((K G)) arrow G_0 lr((K' G))$ is not always a
split injection (see Exercise @exc:grothendieck-extension-nonsplit).

#source(438)
#proposition[
  Let $(K',R',k')$ be a finite extension of the $p$-modular system $(K,R,k)$.
  Then there exists a commutative diagram

  #decomposition-extension-diagram

  where the vertical maps are decomposition homomorphisms (see
  @def:decomposition-map-matrix), and the horizontal maps are the injections
  defined in @prop:grothendieck-scalar-extension-injections.
] <prop:decomposition-scalar-extension-square>

The proof is left as an exercise for the reader.

#exercises-heading

#exercise[
  Verify the statements made in Examples (i) and (ii) at the end of
  §@ss:reduction-decomposition-map. Note in particular that if $M$ is a full
  $R G$-lattice in either of the simple modules $Z_4$ or $Z_5$ in Example (ii),
  then $overline(M)$ is not a simple $k G$-module.
] <exc:symmetric-decomposition-matrices-two>

#exercise[
  Find the decomposition matrix for the groups $S_3$ and $S_4$ considered in
  Exercise @exc:symmetric-decomposition-matrices-two, in case $p=3$ and the
  $p$-modular system is $(QQ,R,k)$, where $R$ is the ring of $3$-adic integers
  in $QQ$ and $k=ZZ slash 3ZZ$.
] <exc:symmetric-decomposition-matrices-three>

#exercise[
  Find an example of a $p$-modular system $(K,R,k)$, a finite group $G$, and two
  full $R G$-lattices $M_1$ and $M_2$ in a simple $K G$-module $V$, such that
  $overline(M_1)$ and $overline(M_2)$ are not $k G$-isomorphic.
] <exc:nonisomorphic-full-lattice-reductions>

#exercise[
  Let $A$ be an arbitrary ring. Show that each element $x$ of the projective
  class group $K_0 lr((A))$ can be expressed in the form
  $ x=[P]-[A^((n))] $
  for some $P in cal(P)(A)$ and some non-negative integer $n$. Show also that
  $x$ may be expressed as
  $ x=[A^((m))]-[P'] $
  for some $m >= 0$ and some $P' in cal(P)(A)$.
  #hint([@exc:projective-class-free-difference])[
    Write $x=[P_1]-[P_2]$ with each $P_i in cal(P)(A)$, and choose
    $Q in cal(P)(A)$ such that $P_2 plus.o Q tilde.equiv A^((n))$ for some
    $n >= 0$. Then
    $ x=[P_1 plus.o Q]-[P_2 plus.o Q]=[P_1 plus.o Q]-[A^((n))], $
    as desired.
  ]
] <exc:projective-class-free-difference>

#exercise[
  If $A$ is a semisimple ring, show that $K_0 lr((A))=G_0 lr((A))$.
] <exc:semisimple-grothendieck-projective-equality>

#source(439)
#exercise[
  Let $A$ be a f.d. separable $K$-algebra, and let $E$ be an extension field of
  $K$. Set $A^E=E times.o_K A$. Show that the map
  $ beta:G_0 lr((A)) arrow G_0 lr((A^E)), $
  given by $beta[V]=[V^E]$ for each $A$-module $V$, is a monomorphism.
  #hint([@exc:separable-grothendieck-injection])[
    Let ${V_1,dots,V_s}$ be a basic set of simple left $A$-modules. Then
    $ G_0 lr((A))=plus.o.big_(i=1)^s ZZ[V_i]. $
    For each $i$, we may write
    $ V_i^E tilde.equiv product_(j=1)^(n_i) W_(i j)^((m_(i j))), $
    where the ${W_(i j)}$ are simple $A^E$-modules. By
    @th:separable-extension-radical-simples(ii), the modules
    ${W_(i j):1 <= j <= n_i,1 <= i <= s}$ are a basic set of simple
    $A^E$-modules. Since
    $ G_0 lr((A^E))=plus.o.big_(i,j) ZZ[W_(i j)], $
    it is clear that $beta$ is monic.
  ]
] <exc:separable-grothendieck-injection>

#exercise[
  Let $G$ be a finite group, and let $R$ be a d.v.r. with quotient field $K$.
  Let $V$ be a simple $K G$-module. Show that every full $R G$-lattice $M$ in
  $V$ is indecomposable, and in fact, that $M$ contains no nonzero
  $R G$-submodules of smaller $R$-rank.
] <exc:simple-module-lattice-indecomposable>

#exercise[
  Let $G$ be the quaternion group of order $8$, and $K$ a splitting field for
  $G$ of finite dimension over the rational field $QQ$. Let
  $M=QQ plus.o QQ i plus.o QQ j plus.o QQ k$ be the simple $QQ G$-module
  consisting of rational quaternions (see Example @exm:serre-outer-tensor). Show
  that
  $ [M^K]=2[W] quad "in" G_0 lr((K G)), $
  where $W$ is the simple $K G$-module such that $dim_K W=2$. Deduce that the
  image of $G_0 lr((QQ G))$ in $G_0 lr((K G))$ is not a $ZZ$-direct summand of
  $G_0 lr((K G))$.
] <exc:grothendieck-extension-nonsplit>
