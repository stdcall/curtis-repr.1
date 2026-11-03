#import "main-defs.typ": *
#import "statements.typ": *

== Induced Modules <sec:induced-modules>

The technique of induced representations is one of the most important methods in
the entire theory of representations of groups. It establishes strong
connections between the representation theory of a group $G$ and the
representations of the subgroups of $G$. The method does not extend readily to
algebras, however, and is used primarily in the context of group algebras. We
shall develop most of the theory, including the Frobenius Reciprocity Theorem,
and the Mackey Decomposition Theorems, for the group algebra $R G$ of a finite
group $G$ over an arbitrary commutative ring $R$. In case the coefficient ring
is a splitting field $K$ contained in the complex field, as in
§@ss:finite-group-character-orthogonality, more precise versions of the theorems
are available, and will be established at the appropriate places in the
discussion.

#heading(level: 3)[
  Definition of Induced Modules. Frobenius Reciprocity
] <ss:induction-frobenius>

In this section, $R$ denotes an arbitrary commutative ring, $G$ a finite group,
and $H$ a fixed subgroup of $G$.

The problem to be considered is the construction of $R G$-modules from
$R H$-modules, and the reverse problem. Both can be understood in a general
ring-theoretical setting. Let $phi: B -> A$ be a homomorphism from a ring $B$
into a ring $A$ such that $phi(1)=1$. One way is easy. Let $M$ be a left
$A$-module; then we obtain a $B$-module $phi_* lr((M))$, whose underlying
abelian group is $M$, and for which the composition is given by
$ b dot m=phi(b)m, b in B, m in M. $
Then $phi_*$ defines a covariant functor (see §@ss:categories-functors) from the
category $attach(frak(M), bl: A)$ of left $A$-modules to the category
$attach(frak(M), bl: B)$ of left $B$-modules. The operation
$M arrow.r phi_* lr((M))$ is called _restriction of scalars_#idx("restriction").

For the reverse construction, we first note that $A$ becomes an
$(A,B)$-bimodule, with the action of $b in B$ on $A$ given by right
multiplication by $phi(b)$. Then each left $B$-module $L$ defines a left
$A$-module $phi^* lr((L))$, where
$ phi^* lr((L))=A times.o_B L. $
This time we obtain a covariant function
$phi^*: attach(frak(M), bl: B) -> attach(frak(M), bl: A)$, called _induction_.
Note that $phi^* lr((B))=A$.

#source(250)
Now let us apply these constructions to the categories of left $R G$-modules and
left $R H$-modules, where $phi: R H -> R G$ is the injective homomorphism from
$R H$ into $R G$ arising from the inclusion map $H subset G$. We shall view
$phi$ as an inclusion map whenever $H subset.eq G$, and write
$R H subset.eq R G$.

Then the operation of restriction of scalars from $R G$ to $R H$ assigns to each
left $R G$-module $M$ a left $R H$-module $op("res")_H^G lr((M))$, which we
shall often write in abbreviated form as $M|_H$, or $M_H$.#idx("restriction") If
$upright(bold(M)): G -> GL(M)$ is a matrix representation of $G$ afforded by an
$R$-free $R G$-module $M$ with a finite basis, then the representation
$upright(bold(M))|_H$ of $H$ afforded by the restriction $M|_H$ is simply the
restriction of the homomorphism $upright(bold(M)): G -> GL(M)$ to the subgroup
$H$. Similarly, if $mu: G -> R$ is the trace function (or character) of an
$R$-matrix representation $upright(bold(M))$, then the character $mu|_H$ of the
restriction $M|_H$ is again the restriction of the function $mu: G -> R$ to $H$.

The operation of induction from $R H$-modules to $R G$-modules assigns to each
left $R H$-module $L$ a left $R G$-module $op("ind")_H^G lr((L))$, given by
$ op("ind")_H^G lr((L))=R G times.o_(R H) L. $
We shall often abbreviate $op("ind")_H^G lr((L))$ as $L^G$. Note that
$op("ind")_H^G lr((R H))=R G$.

As we pointed out in the introduction to this section, $R G$ is an
$(R G,R H)$-bimodule, with operations given by left and right multiplication in
$R G$. Thus $op("ind")_H^G lr((L))$ consists of all elements
$sum g_i times.o l_i$, with $g_i in G$, $l_i in L$, with the action of $g in G$
given by
$ g lr((sum g_i times.o l_i))=sum g g_i times.o l_i. $
If $upright(bold(L))$ is a matrix representation of $H$ over the ring $R$, then
$upright(bold(L))^G$ (or $op("ind")_H^G lr((upright(bold(L))))$) denotes the
matrix representation of $G$ afforded by induction from the $R H$-module defined
by $upright(bold(L))$. If $lambda: H -> R$ is the character of
$upright(bold(L))$, then $lambda^G$ (or $op("ind")_H^G lr((lambda))$) denotes
the character of the induced representation $upright(bold(L))^G$. We call
$lambda^G$ an _induced character_.#idx("induced character")#idx(
  "character",
  "induced",
) #idx("induced module")#idx("induction")

Our first task is to work out in detail the action of $G$ on $L^G$, so that when
$L$ affords a matrix representation $upright(bold(L))$, the induced
representation $upright(bold(L))^G$ and induced character $lambda^G$ can be
computed explicitly.

Let $G=g_1 H union dots union g_n H$ be a left coset decomposition of $G$
relative to $H$, with $n=|G:H|$, and $g_1=1 in H$. Then
$ R G=plus.o.big_(i=1)^n g_i R H. $
Now let $L$ be a left $R H$-module. From the direct sum theorem for tensor
products @eq:tensor-direct-sums, we have
$
  L^G=R G times.o_(R H) L=plus.o.big_(i=1)^n g_i R H times.o L
  =plus.o.big_(i=1)^n g_i times.o L,
$
#source(251)
using the fact that $g_i R H times.o L=g_i times.o (R H)L=g_i times.o L$ because
the tensor product is taken with respect to $R H$.

We next observe that $g_1 times.o L=1 times.o L$ is an $R H$-submodule of
$L^G|_(R H)$, and the map
$ l arrow.r 1 times.o l, l in L, $
is an $R H$-monomorphism from $L$ into $L^G$, because of the isomorphism
$R H times.o_(R H) L tilde.equiv L$ (see @eq:tensor-regular-module). Finally,
each summand $g_i times.o L$ of $L^G$ can be expressed as
$g_i lr((1 times.o L))$, and hence $1 times.o L tilde.equiv g_i times.o L$ as
$R$-modules, with the isomorphism given by left multiplication by $g_i$.

Now let $g in G$; for each $i$, $1 <= i <= n$, we have $g g_i in g_j H$ for some
left coset $g_j H$. Hence there is a uniquely determined coset representative
$g_j$ and an element $h in H$ such that
$ g g_i=g_j h. $
Thus $g(g_i times.o L)=g_j times.o L$, so that $g$ permutes the summands
${g_i times.o L}$. The action of $g$ on an individual summand $g_i times.o L$ is
given by
$ g(g_i times.o l)=g_j h times.o l=g_j times.o h l, l in L. $
We next suppose that $L$ affords a matrix representation $upright(bold(L))$,
with respect to a finite $R$-basis ${l_1,dots,l_m}$ of $L$, so that
$ h l_j=sum_(i=1)^m alpha_(i j) lr((h)) l_i, alpha_(i j) lr((h)) in R, $
and $upright(bold(L))(h)=(alpha_(i j) lr((h)))$ for $h in H$. To compute
$upright(bold(L))^G lr((g))$ for $g in G$, we first note that from what has been
shown, the elements ${g_i times.o l_j}$, $1 <= i <= n$, $1 <= j <= m$, form an
$R$-basis for $L^G$. Letting $g g_i=g_j h$ as above, we have
$
  g(g_i times.o l_s)=g_j times.o h l_s
  =sum_(t=1)^m alpha_(t s) lr((h))(g_j times.o l_t)
$
for $1 <= s <= m$. These formulas can be described efficiently in the following
way. Note first that the equation $g g_i=g_j h$ is equivalent to the statement
$g_j^(-1) g g_i=h$. We next extend the matrix coefficient functions
${alpha_(i j)}$ to maps $dot(alpha)_(i j): G -> R$, where
$
  dot(alpha)_(i j) lr((g))=cases(
    alpha_(i j) lr((g)) & quad g in H,
    0 & quad g in.not H
  ).
$

#source(252)
Then the action of $g$ on the $R$-basis ${g_i times.o l_s}$ of $L^G$ is given by
$
  g(g_i times.o l_s)=sum_(t=1)^m alpha_(t s) lr((h))(g_j times.o l_t)
  =sum_(j=1)^n sum_(t=1)^m dot(alpha)_(t s) lr((g_j^(-1) g g_i))(g_j times.o
    l_t).
$
Likewise, we extend $upright(bold(L))$ from $H$ to $G$ by defining
$ dot(upright(bold(L))) lr((g))=(dot(alpha)_(i j) lr((g))), g in G. $
Then, relative to the $R$-basis
$
  g_1 times.o l_1,dots,g_1 times.o l_m,g_2 times.o l_1,dots,g_2 times.o
  l_m,dots,
$
the matrix representation afforded by $L^G$ is given by
$
  g arrow.r upright(bold(L))^G lr((g))=
  mat(
    delim: "[",
    dot(upright(bold(L))) lr((g_1^(-1) g g_1)), dots.h,
    dot(upright(bold(L))) lr((g_1^(-1) g g_n));
    dots.v, dots.down, dots.v;
    dot(upright(bold(L))) lr((g_n^(-1) g g_1)), dots.h,
    dot(upright(bold(L))) lr((g_n^(-1) g g_n))
  ).
$ <eq:induced-matrix>
Letting $lambda: H -> R$ be the character afforded by $upright(bold(L))$, that
is,
$ lambda(h)=op("Trace") upright(bold(L))(h), h in H, $
it is immediate from @eq:induced-matrix that the character $lambda^G$ afforded
by $upright(bold(L))^G$ is given by
$ lambda^G lr((g))=sum_(i=1)^n dot(lambda) lr((g_i^(-1) g g_i)), g in G. $
<eq:induced-character-cosets>
Here $dot(lambda)$ is the extension to $G$ of the function $lambda$, and is
defined by
$ dot(lambda) lr((g))=cases(lambda(g) & quad g in H, 0 & quad g in.not H). $
In case $|H|$ is a unit in $R$, the formula for $lambda^G$ can be written in the
useful form
$ lambda^G lr((g))=frac(1, |H|) sum_(x in G) dot(lambda) lr((x^(-1) g x)), $
<eq:induced-character-average>
which does not involve the coset representatives ${g_i}$. We note in passing the
important formula: #equation-suffix(base: [@eq:induced-character-average])[
  $ deg lambda^G=lambda^G lr((1))=|G:H|lambda(1). $
] <eq:induced-character-degree>

#source(253)
#example[
  Let $1_H$ denote the trivial representation of $H$, and let $V=R v$ be a free
  $R$-module affording $1_H$, so $h v=v$ for all $h in H$. The action of
  $g in G$ on the summands $R(g_i times.o v)$ of the module affording $1_H^G$ is
  given by
  $ g(g_i times.o v)=g_j times.o v, "where" g g_i in g_j H. $
  This formula shows that the $G$-set#idx("G-set") of submodules
  $R(g_i times.o v)$ of $V^G$, with the action of $G$ given as above, is
  isomorphic to the $G$-set $G slash H$ of left cosets ${g_i H}$ of $H$, with
  action of $G$ given by left translation $g_i H arrow.r g g_i H$, $g in G$,
  $1 <= i <= n$. Thus the induced representation $1_H^G$ is equivalent to the
  permutation representation of $G$ over $R$ afforded by the $G$-set
  $G slash H$, defined by introducing an $R$-basis ${v_i}$ corresponding to the
  left cosets ${g_i H}$, with action of $g in G$ on the basis defined by
  $ g v_i=v_j "if" g g_i H=g_j H, 1 <= i <= n. $
  In particular, the left regular module $R G$ of $G$ over $R$ is isomorphic to
  the induced module $1_H^G$, induced from the trivial representation $1_H$ of
  the trivial subgroup $H={1}$.
] <exm:induced-trivial-permutation>

We now turn to some general properties of induced modules. We begin with an
important characterization of induced modules:

#proposition[
  Let $M$ be a left $R G$-module whose restriction $M|_H$ contains an
  $R H$-submodule $L$ such that $M$ is the direct sum $plus.o.big_(i=1)^n g_i L$
  of $R$-submodules ${g_i L}$, where ${g_i:1 <= i <= n}$ is a set of left coset
  representatives of $H$ in $G$. Then $M tilde.equiv L^G$ as left $R G$-modules.
] <prop:induced-module-criterion>
#proof[
  One checks that the map $R G times L -> M$, given by $(g,l) arrow.r g l$, is
  $R$-bilinear and $R H$-balanced. It follows that there is an $R$-surjection
  $phi: R G times.o_(R H) L -> M$, such that $phi(g_i times.o L)=g_i L$,
  $1 <= i <= n$. The hypothesis implies the existence of an $R$-homomorphism
  from $M$ to $L^G$ which is an inverse to $phi$, and takes $g_i L$ onto
  $g_i times.o L$, $1 <= i <= n$. Thus $phi$ is an $R$-isomorphism, which from
  its definition is in fact an $R G$-isomorphism; this completes the proof.
]

#proposition[
  #enum(
    numbering: "(i)",
    [(Additivity of induction). Let $H <= G$, and let $L_1$ and $L_2$ be left
      $R H$-modules. Then
      $
        op("ind")_H^G lr((L_1 plus.o L_2)) tilde.equiv
        op("ind")_H^G lr((L_1)) plus.o op("ind")_H^G lr((L_2)).
      $],
    [(Transitivity of induction).#idx("Transitivity of Induction") Let
      $H_1 <= H_2 <= G$, and let $L$ be a left $R H_1$-module. Then
      $
        op("ind")_(H_2)^G lr((op("ind")_(H_1)^(H_2) lr((L))))
        tilde.equiv op("ind")_(H_1)^G lr((L)).
      $],
  )
] <prop:induction-transitive>
#source(254)
#proof[
  (i) follows immediately from the distributivity of tensor products over direct
  sums @eq:tensor-direct-sums.

  (ii) By associativity of the tensor product @prop:tensor-associativity,
  together with the isomorphism $M times.o_A A tilde.equiv M$ for a right
  $A$-module $M$ (see @eq:tensor-regular-module), we have
  $
    op("ind")_(H_2)^G lr((op("ind")_(H_1)^(H_2) lr((L))))
    &=R G times.o_(R H_2)(R H_2 times.o_(R H_1) L) \
    &tilde.equiv (R G times.o_(R H_2) R H_2) times.o_(R H_1) L \
    &tilde.equiv R G times.o_(R H_1) L=op("ind")_(H_1)^G lr((L))
  $
  as $R$-modules. The isomorphisms all commute with the action of $G$ from the
  left and the result follows.
]
#corollary[
  Let $lambda$ be the character of $H_1$ afforded by a left $R H_1$-module $L$
  with a finite free $R$-basis, and let $H_1 <= H_2 <= G$ as above. Then
  $ (lambda^(H_2))^G=lambda^G. $
] <cor:character-induction-transitive>

#theorem(name: "Frobenius Reciprocity Theorem", title: [for $R G$-modules])[
  Let $H <= G$, and let $L$ be a left $R H$-module, and $M$ a left $R G$-module.
  Then there exists an isomorphism of $R$-modules
  $ Hom_(R H) lr((L,M|_H)) tilde.equiv Hom_(R G) lr((L^G,M)). $
  #idx("Frobenius Reciprocity Theorem")
] <th:frobenius-reciprocity>
#proof[
  We shall apply the Adjointness Theorem @th:hom-tensor-adjointness, which
  asserts that there is an isomorphism of additive groups
  $
    Hom_A lr((L',Hom_B lr((M',N'))))
    tilde.equiv Hom_B lr((M' times.o_A L',N')),
  $
  for any pair of rings $A$ and $B$, and modules
  $
    L' in attach(frak(M), bl: A), M' in attach(frak(M), bl: B, br: A),
    N' in attach(frak(M), bl: B).
  $
  In order to prove @th:frobenius-reciprocity, we let $A=R H$, $B=R G$,
  $L'=L in attach(frak(M), bl: R H)$, as in @th:frobenius-reciprocity,
  $M'=R G in attach(frak(M), bl: R G, br: R H)$, and
  $N'=M in attach(frak(M), bl: R G)$. Then there exists an isomorphism of
  additive groups
  $ Hom_(R H) lr((L,Hom_(R G) lr((R G,M)))) tilde.equiv Hom_(R G) lr((L^G,M)). $
  From the construction of the isomorphism in @th:hom-tensor-adjointness, it is
  clear that the above is an $R$-isomorphism.

  #source(255)
  It remains to check that the left $R H$-module $Hom_(R G) lr((R G,M))$ is
  isomorphic to $M|_H$. It is clear that the map
  $ tau: f in Hom_(R G) lr((R G,M)) arrow.r f(1) in M $
  is an isomorphism of $R$-modules. From
  §@sec:hom-tensor-projective-injective-flat, the action of $R H$ on
  $Hom_(R G) lr((R G,M))$ is given by
  $ (b f)(a)=f(a b), a in R G, b in R H. $
  Then for all $b in R H$ and $f in Hom_(R G) lr((R G,M))$, we have
  $ tau(b f)=(b f)(1)=f(b)=b(f(1))=b tau(f), $
  proving that $Hom_(R G) lr((R G,M)) tilde.equiv M|_H$ as $R H$-modules, and
  completing the proof.
]

We conclude this section with some remarks on the Frobenius Reciprocity Theorem,
when the ring $R$ is a subfield $K$ of the field of complex numbers. First
assume as in §@ss:finite-group-character-orthogonality that $K$ is a splitting
field for $K G$ and $K H$. Let $M$ be a left $K G$-module with $K$-character
$mu$, and let $L$ be a left $K H$-module with $K$-character $lambda$. By
Proposition @prop:character-scalar-products-multiplicities(iii) we have
$ dim_K lr((Hom_(R H) lr((L,M|_H))))=(lambda,mu|_H)_H, $
while
$ dim_K lr((Hom_(R G) lr((L^G,M))))=(lambda^G,mu)_G. $
Therefore, the preceding result implies that
$ (lambda^G,mu)_G=(lambda,mu|_H)_H. $
It will be useful to note that this identity can easily be proved in a more
general form (for class functions), without making use of the adjointness
theorem as in @th:frobenius-reciprocity, using instead the formula
@eq:induced-character-average for $lambda^G$.

#theorem(name: "Frobenius Reciprocity Theorem", title: [for class functions])[
  Let $K$ be a subfield of $CC$, and let $H <= G$. Let $lambda in cf_K lr((H))$
  and $mu in cf_K lr((G))$, and define $lambda^G: G -> K$ by
  $ lambda^G lr((g))=frac(1, |H|) sum_(x in G) dot(lambda) lr((x^(-1) g x)), $
  where $dot(lambda)$ is the function $lambda$ extended to $G$ as in
  @eq:induced-character-average. Then $lambda^G in cf_K lr((G))$, and we
  #source(256)
  have
  $ (lambda^G,mu)_G=(lambda,mu|_H)_H. $
  #idx("Frobenius Reciprocity Theorem")
] <th:frobenius-class-functions>
#proof[
  It is immediate from the definition that $lambda^G in cf_K lr((G))$. We have
  $
    (lambda^G,mu)_G
    &=frac(1, |G||H|) sum_(x in G) sum_(y in G)
    dot(lambda) lr((y^(-1) x y)) overline(mu(x)) \
    &=frac(1, |G||H|) sum_(x in G) sum_(y in G)
    dot(lambda) lr((y^(-1) x y)) overline(mu(y^(-1) x y)) \
    &=frac(1, |H|) sum_(z in G) dot(lambda) lr((z)) overline(mu(z))
    =frac(1, |H|) sum_(z in H) lambda(z) overline(mu(z))=(lambda,mu|_H)_H,
  $
  using the facts that $mu$ is a class function, and that for fixed $z$, the
  equation $y^(-1) x y=z$ has exactly $|G|$ solutions.
]

*Examples.* In both of the following examples of the use of the Frobenius
Reciprocity Theorem, $K$ denotes the field of complex numbers.

#examples(name: none)[
  As a first example of @th:frobenius-class-functions, we show how to prove that
  for a $K$-character $lambda$ of $H$, the induced class function
  $lambda^G in cf_K lr((G))$, as defined in @th:frobenius-class-functions, is a
  $K$-character of $G$. The proof uses only @th:frobenius-class-functions and
  the orthogonality relations in §@ss:finite-group-character-orthogonality, and
  is independent of the interpretation of $lambda^G$ as the character of an
  induced module $L^G$, given in the first part of this section.

  In order to prove that $lambda^G$ is a $K$-character of $G$, it is sufficient
  to prove that for all irreducible $K$-characters ${zeta}$ of $G$, the
  multiplicity $(lambda^G,zeta)_G$ is a non-negative integer. From
  @th:frobenius-class-functions, we have
  $ (lambda^G,zeta)_G=(lambda,zeta|_H)_H="non-negative integer", $
  because both $lambda$ and $zeta|_H$ are $K$-characters of $H$, and our
  assertion now follows from Proposition
  @prop:character-scalar-products-multiplicities(i).
] <exm:induced-class-function-character>

#examples(name: none)[
  *Characters of the dihedral groups.*#idx("dihedral characters") #idx(
    "dihedral group",
  )#idx("group", "dihedral") Let $D_m$ be the dihedral group of order $2m$, with
  the presentation
  $ ⟨ a,b: a^m=b^2=(a b)^2=1 ⟩. $
  We shall compute all the irreducible $K$-characters of $D_m$. Let
  $lambda: ⟨ a ⟩ -> K^times$ be an irreducible character of $⟨ a ⟩$ of degree
  $1$. Letting $epsilon$ be a primitive $m$-th root of $1$, we have
  $lambda(a)=epsilon^i$ for some $i$. Using formula @eq:induced-character-cosets
  for the induced character $lambda^G$, we obtain
  $ lambda^G lr((x))=dot(lambda) lr((x))+dot(lambda) lr((b x b^(-1))). $
  #source(257)
  For $x in ⟨ a ⟩$, $b x b^(-1)=x^(-1)$, so we have
  $ lambda^G|_(⟨ a ⟩)=lambda+overline(lambda), $
  and by Theorem @th:frobenius-class-functions,
  $
    (lambda^G,lambda^G)_G=(lambda,lambda^G|_(⟨ a ⟩))_(⟨ a ⟩)
    =(lambda,lambda+overline(lambda))_(⟨ a ⟩).
  $
  From §@ss:finite-group-character-orthogonality, $lambda^G$ is irreducible if
  and only if $(lambda^G,lambda^G)=1$. Therefore $lambda^G$ is irreducible if
  and only if $lambda != overline(lambda)$. Moreover, if both $lambda^G$ and
  $mu^G$ are irreducible, for homomorphisms $lambda,mu: ⟨ a ⟩ -> K^times$, we
  have
  $
    (lambda^G,mu^G)_G=(lambda,mu+overline(mu))_(⟨ a ⟩)
    =cases(
      0 & quad lambda != mu","overline(mu), 1 & quad lambda=mu "or"
      overline(mu)
    ).
  $
  We now distinguish two cases:
  #enum(
    numbering: "(i)",
    [$m$ is odd. In this case there are two characters of degree $1$ (because
      $|D_m:D'_m|=2$), and $1/2(m-1)$ distinct irreducible characters of the
      form $lambda^G$ as above. Adding up the squares of the degrees we obtain
      $ 2+1/2(m-1)(4)=2+2(m-1)=2m=|D_m|, $
      and it follows that we have determined all the irreducible characters (by
      Theorem @th:split-group-algebra-dimensions(i)).],
    [$m$ is even. In this case there are $4$ characters of $D_m$ of degree $1$,
      and $1/2(m-2)$ distinct irreducible characters of degree $2$. Adding up
      the squares of the degrees, we have
      $ 4+1/2(m-2)(4)=4+2(m-2)=2m=|D_m|, $
      and again we have a complete set of irreducible characters. (See also
      Example @exm:dihedral-group-algebra-reduced-norm.)],
  )
] <exm:dihedral-group-characters>

=== Mackey’s Subgroup Theorem and Tensor Product Theorem <ss:mackey-theorems>

The results in this section were proved by Mackey @bib:Mackey1951 for
representations of finite groups over fields of characteristic zero, and served
as an introduction to the corresponding theorems on induced representations of
locally compact groups.

As in §@ss:induction-frobenius, we shall be concerned in this section with
finite groups $G$ and left $R G$-modules, where $R$ is an arbitrary commutative
ring. The extension of Mackey’s results to the case of an arbitrary commutative
coefficient ring will be crucial for J. A. Green’s approach to modular
representations of finite groups, as we shall see in §@sec:vertices-sources.

#source(258)
Let $H$ be a subgroup of $G$, and recall our notation for conjugates of elements
of $H$:
$
  attach(h, tl: a)=a h a^(-1), h^b=b^(-1) h b=attach(h, tl: b^(-1)),
  a,b in G, h in H.
$
Then
$
  attach(h, tl: a b)=attach(lr((attach(h, tl: b))), tl: a),
  h^(a b)=(h^a)^b.
$
Similarly, the conjugates $attach(H, tl: a)$ and $H^a$ of the subgroup $H$ are
defined by
$ attach(H, tl: a)=a H a^(-1)=H^(a^(-1)), a in G. $
In the theory of modules, it is sometimes convenient to change from left modules
to right modules, and the same is true for notations involving conjugations. We
shall give a one-sided version of most formulas, but it will be useful for the
reader to become ambidextrous.

Now let $L$ be a left $R H$-module, and let $a in G$. The _conjugate_
$attach(L, tl: a)$ of $L$ is the left $R(attach(H, tl: a))$-module, with
underlying $R$-module $L$, and $attach(H, tl: a)$-action $ast$ defined by
$ attach(h, tl: a) ast l=h dot l, h in H, l in L. $
#idx("conjugate module")
If $L$ is $R$-free with a finite $R$-basis, and $upright(bold(L))$ is the
representation of $H$ afforded by $L$, with character $lambda$, we define the
conjugate representation $attach(upright(bold(L)), tl: a)$ and conjugate
character $attach(lambda, tl: a)$ of $attach(H, tl: a)$ by the formulas
$
  attach(upright(bold(L)), tl: a) lr((attach(h, tl: a)))=upright(bold(L))(h),
  attach(lambda, tl: a) lr((attach(h, tl: a)))=lambda(h), h in H.
$
#idx("conjugate character")#idx("character", "conjugate") It is easily checked
that these definitions are consistent with the definition of the conjugate
module, so that $attach(L, tl: a)$ affords the representation
$attach(upright(bold(L)), tl: a)$ of $attach(H, tl: a)$, with character
$attach(lambda, tl: a)$.

We collect a few useful facts about conjugates.

#lemma[
  Let $H$ be a subgroup of $G$, and $L$ a left $R H$-module.
  #enum(
    numbering: "(i)",
    [If $L$ is a submodule of $M|_H$ for some $R G$-module $M$, then $a L$ is a
      left $R(attach(H, tl: a))$-module, and
      $a L tilde.equiv attach(L, tl: a)$.],
    [$(attach(L, tl: a))^G tilde.equiv L^G$ as $R G$-modules, for all
      $a in G$.],
    [$attach(L, tl: a) tilde.equiv L$ as $R H$-modules if $a in H$.],
  )
] <lem:conjugate-modules>
#proof[
  (i) The map $phi: l arrow.r a l$ is an $R$-isomorphism from $L$ to $a L$.
  Moreover, $(attach(h, tl: a))(a l)=a(h l)$ for all $h in H$, $l in L$, so that
  $a L$ is an $R(attach(H, tl: a))$-module. Finally, for $h in H$ and $l in L$,
  we have
  $
    phi(attach(h, tl: a) ast l)=phi(h l)=a h l
    =attach(h, tl: a)(a l)=(attach(h, tl: a))phi(l),
  $
  as required.

  #source(259)
  (ii) Let $L^G=plus.o.big_(i=1)^n g_i times.o L=plus.o.big_(i=1)^n g_i lr(
    (1 times.o
      L)
  )$, for a set of left coset representatives ${g_i}_(1 <= i <= n)$ of $H$ in
  $G$. Then $G=union.big_i g_i H$ implies that
  $G=union.big_i a g_i a^(-1) attach(H, tl: a)$, and it follows that
  ${a g_i a^(-1)}_(1 <= i <= n)$ is a set of left coset representatives of
  $attach(H, tl: a)$ in $G$. Moreover, we have
  $
    L^G=plus.o.big_(i=1)^n g_i lr((1 times.o L))
    =plus.o.big_(i=1)^n a g_i lr((1 times.o L))
    =plus.o.big_(i=1)^n (a g_i a^(-1))(a(1 times.o L)).
  $
  From §@ss:induction-frobenius, $1 times.o L tilde.equiv L$ as left
  $R H$-modules, hence $a(1 times.o L) tilde.equiv attach(L, tl: a)$ by part (i)
  of this lemma. Finally, we have $L^G tilde.equiv (attach(L, tl: a))^G$ by
  Proposition @prop:induced-module-criterion.

  (iii) The map $l in attach(L, tl: a) arrow.r a l in L$ gives the desired
  isomorphism.
]

For the next result, and subsequently in this book, we shall use the notation
$X backslash G slash Y$ to denote the $(X,Y)$-double cosets $X g Y$ of $G$
relative to a pair of subgroups $X$ and $Y$, and $X backslash G$ for the right
cosets ${X g}_(g in G)$, and $G slash Y$ for the left cosets ${g Y}$. We shall
also use the symbols $H,X,Y,Z$ for subgroups of $G$, and $L,M,N$, etc., for
modules.

#theorem(name: "Subgroup Theorem")[
  Let $X,Y$ be subgroups of $G$, and let $L$ be a left $R X$-module. Then
  $
    L^G|_Y tilde.equiv plus.o.big_(D=Y a X)
    (attach(L, tl: a)|_(attach(X, tl: a) inter Y))^Y,
  $
  where the sum is taken over $Y backslash G slash X$. The summands are
  independent of the choice of the double coset representatives, in the sense
  that
  $
    (attach(L, tl: a)|_(attach(X, tl: a) inter Y))^Y tilde.equiv
    (attach(L, tl: b)|_(attach(X, tl: b) inter Y))^Y
  $
  as $R Y$-modules whenever $Y a X=Y b X$. #idx("Mackey Subgroup Theorem")#idx(
    "Subgroup Theorem",
  )
] <th:mackey-subgroup>
*Note.* In terms of our notations $op("ind")$ and $op("res")$, the Theorem
reads:
$
  op("res")_Y^G lr((op("ind")_X^G lr((L)))) tilde.equiv
  plus.o.big_(D=Y a X) op("ind")_(attach(X, tl: a) inter Y)^Y
  lr(
    (op("res")_(attach(X, tl: a) inter Y)^(attach(X, tl: a)) lr(
        (attach(
            L,
            tl: a
          ))
      ))
  ).
$
#proof[
  Letting $G=union.dot.big_(i=1)^n g_i X$, we have
  $ L^G=plus.o.big_(i=1)^n g_i times.o L. $
  For each double coset $D in Y backslash G slash X$, let
  $ W(D)=plus.o.big_(g_i X subset D) g_i times.o L. $
  #source(260)
  Then $W(D)$ is an $R Y$-submodule of $L^G|_Y$, clearly independent of the
  choice of the coset representatives ${g_i}$. Moreover, we have
  $ L^G|_Y=plus.o.big_D W(D). $
  It remains to work out the structure of the $R Y$-modules $W(D)$. Let
  $D=Y a X$, and let
  $ Y=union.dot.big_j s_j lr((attach(X, tl: a) inter Y)). $
  Then
  $
    Y a X=union.big_j s_j lr((attach(X, tl: a) inter Y))a X=union.dot.big_j
    s_j a X,
  $
  because
  $ s a X=s' a X <=> s^(-1)s' in attach(X, tl: a) inter Y. $
  Thus the elements ${s_j a}$ are representatives of the left $X$-cosets in $D$,
  and we have
  $ W(D)=plus.o.big_j s_j a times.o L=plus.o.big_j s_j lr((a(1 times.o L))). $
  By Lemma @lem:conjugate-modules, $a(1 times.o L) tilde.equiv attach(L, tl: a)$
  as $R(attach(X, tl: a))$-modules; hence
  $a(1 times.o L) tilde.equiv attach(L, tl: a)$ as
  $R(attach(X, tl: a) inter Y)$-modules, so by Proposition
  @prop:induced-module-criterion, we have
  $ W(D) tilde.equiv (attach(L, tl: a)|_(attach(X, tl: a) inter Y))^Y. $
  Finally, the same argument proves that
  $ W(D) tilde.equiv (attach(L, tl: b)|_(attach(X, tl: b) inter Y))^Y $
  for any other $b in D$, and the theorem is proved.
]

#remarks[
  We give two illustrations of the use of the Subgroup Theorem.
  #enum(
    numbering: "(i)",
    [Let $X ⊴ G$ (normal subgroup) and let $L$ be an $R X$-module. Then, putting
      $Y=X$ in @th:mackey-subgroup, we have
      $ L^G|_X tilde.equiv plus.o.big_(a X in G slash X) attach(L, tl: a), $
      where the sum is taken over all cosets in $G slash X$; in this case, the
      conjugates $attach(L, tl: a)$ are $R X$-modules because $X ⊴ G$.],
    [#source(261)
      We apply the theorem to permutation representations (see Example
      @exm:induced-trivial-permutation). Let $X <= G$. By @th:mackey-subgroup,
      $
        1_X^G|_X tilde.equiv plus.o.big_(X a X in X backslash G slash X)
        (1_(attach(X, tl: a) inter X))^X,
      $
      a direct sum of induced permutation representations. In terms of $G$-sets,
      we have the result that
      $
        op("res")_X^G lr((G slash X)) tilde.equiv
        union.dot.big_(X a X in X backslash G slash X) X slash (attach(
            X, tl: a
          ) inter X),
      $
      giving the decomposition of a transitive $G$-set $G slash X$ as a direct
      sum of transitive $X$-sets, where $X$ is the stabilizer of a point in
      $G slash X$. (See Chapter~5 of Volume~II for amplification of these
      remarks on $G$-sets.)

      By Frobenius Reciprocity @th:frobenius-class-functions and Exercise
      @exc:permutation-character-orbits we have
      $
        (1_X^G,1_X^G)_G=(1_X,(1_X^G)|_X)
        =sum_(X a X in X backslash G slash X)(1_X,(1_(attach(X, tl: a) inter
            X))^X)
        =|X backslash G slash X|,
      $
      where $|X backslash G slash X|$ is the number of $(X,X)$-double cosets in
      $G$.

      The number $(1_X^G,1_X^G)$ is called the _rank_#idx("rank") of the
      transitive permutation representation $1_X^G$, and the numbers
      $|X:attach(X, tl: a) inter X|$ corresponding to the degrees of the direct
      summands $(1_(attach(X, tl: a) inter X))^X$ of $(1_X^G)|_X$, the
      _subdegrees_.#idx("subdegrees") These numerical invariants provide a
      starting point for the decomposition of permutation representations (see
      §@ss:hecke-algebras).],
  )
] <rem:subgroup-theorem-applications>

For the next result, we consider two subgroups $H_1$ and $H_2$ of $G$, and
modules $L_1$ over $R H_1$ and $L_2$ over $R H_2$. Let $H_1 times H_2$ be the
direct product of $H_1$ and $H_2$.

#definition[
  The _outer tensor product_#idx("outer tensor product") $L_1 \# L_2$ of $L_1$
  and $L_2$ is the $R(H_1 times H_2)$-module with underlying $R$-module
  $L_1 times.o_R L_2$, and action of $H_1 times H_2$ given by
  $ (h_1,h_2) dot (l_1 times.o l_2)=h_1 l_1 times.o h_2 l_2. $
  In case $H_1=H_2=H$, the _(inner) tensor product_#idx("inner tensor product")
  #idx("tensor product") $L_1 times.o L_2$ is the $R H$-module whose underlying
  $R$-module is $L_1 times.o_R L_2$, with $H$-action given by
  $ h(l_1 times.o l_2)=h l_1 times.o h l_2. $
] <def:outer-inner-tensor-products>

#remark(numbered: true)[
  Let $L_1$ and $L_2$ be $R H$-modules, and let $H_0$ be the diagonal subgroup
  of $H times H$ consisting of all pairs ${(h,h):h in H}$ in $H times H$. Then
  $H_0 tilde.equiv H$ under the isomorphism $(h,h) arrow.r h$; if we identify
  $H_0$ with $H$ using this
  #source(262)
  isomorphism, then it is clear that
  $ (L_1 \# L_2)|_(H_0) tilde.equiv L_1 times.o L_2 $
  as $R H$-modules. To put it another way, there is an $R$-isomorphism
  $L_1 \# L_2 tilde.equiv L_1 times.o L_2$, which intertwines the actions of
  $H_0$ and $H$.
] <rem:diagonal-tensor-product>

#lemma[
  The formation of outer tensor products commutes with induction. More
  precisely, let $H_1 <= G_1$, $H_2 <= G_2$, and let $L_1$ and $L_2$ be modules
  as in Definition @def:outer-inner-tensor-products. Then we have
  $
    L_1^(G_1) \# L_2^(G_2) tilde.equiv (L_1 \# L_2)^(G_1 times G_2)
    "as" R(G_1 times G_2)"-modules".
  $
] <lem:outer-tensor-induction>
#proof[
  We may identify $R(G_1 times G_2)$ with $R G_1 times.o R G_2$ as $R$-algebras.
  It is left to the reader to check that there is an isomorphism of
  $R(G_1 times G_2)$-modules
  $
    phi: R(G_1 times G_2) times.o_(R(H_1 times H_2))(L_1 times.o_R L_2)
    -> (R G_1 times.o_(R H_1) L_1) times.o_R (R G_2 times.o_(R H_2) L_2),
  $
  such that
  $
    phi(a times.o b times.o l_1 times.o l_2)=a times.o l_1 times.o b times.o
    l_2,
  $
  with the tensor products taken as indicated.
]

#theorem(name: "Tensor Product Theorem")[
  Let $H_1,H_2 <= G$, and let $L_1$ and $L_2$ be left modules over $R H_1$ and
  $R H_2$, respectively. Then
  $
    L_1^G times.o L_2^G tilde.equiv plus.o.big_(x^(-1)y in D)
    ((attach(L_1, tl: x) times.o attach(L_2, tl: y))|_(attach(H_1, tl: x)
      inter attach(H_2, tl: y)))^G,
  $
  where the sum extends over all $(H_1,H_2)$-double cosets $D$ in $G$. There is
  one summand for each $D$; namely, we choose a pair $(x,y)$ with
  $x^(-1)y in D$, and take the indicated summand. If also $u^(-1)v in D$, then
  $
    ((attach(L_1, tl: x) times.o attach(L_2, tl: y))|_(attach(H_1, tl: x)
      inter attach(H_2, tl: y)))^G
    tilde.equiv ((attach(L_1, tl: u) times.o attach(
          L_2, tl: v
        ))|_(attach(H_1, tl: u) inter attach(H_2, tl: v)))^G.
  $
  #idx("Mackey Tensor Product Theorem")#idx("Tensor Product Theorem")
] <th:mackey-tensor-product>
#proof[
  Let $G_0$ denote the diagonal subgroup of $G times G$. Upon identifying $G_0$
  with $G$ using the map $(g,g) arrow.r g$, $g in G$, we have an isomorphism of
  $R G$-modules
  $ L_1^G times.o L_2^G tilde.equiv (L_1 \# L_2)^(G times G)|_(G_0), $
  by @rem:diagonal-tensor-product. We can now apply the Subgroup Theorem
  @th:mackey-subgroup to the right hand
  #source(263)
  side, using the following identifications:
  #table(
    columns: 2,
    stroke: none,
    align: center,
    [Tensor Product Theorem], [Subgroup Theorem],
    $G times G$, $G$,
    $H_1 times H_2$, $X$,
    $G_0$, $Y$,
    $L_1 \# L_2$, $L$,
  )
  The result is that
  $
    (L_1 \# L_2)^(G times G)|_(G_0) tilde.equiv
    plus.o.big_(tilde(D)) (attach((L_1 \# L_2), tl: (x,y))|_(attach(
        (H_1
          times H_2), tl: (x,y)
      ) inter G_0))^(G_0),
  $
  where the sum is taken over double cosets
  $ tilde(D)=G_0 lr((x,y))(H_1 times H_2) "in" G times G. $
  It remains to translate the information on the right hand side from $G_0$ to
  $G$, using the isomorphism between them. We may identify
  $attach((L_1 \# L_2), tl: (x,y))$ with $(x,y) times.o (L_1 \# L_2)$ in
  $(L_1 \# L_2)^(G times G)$, and hence there is an $R$-isomorphism, defined in
  Lemma @lem:outer-tensor-induction, as follows:
  $
    attach((L_1 \# L_2), tl: (x,y)) tilde.equiv (x times.o L_1) times.o (y
      times.o L_2)
    subset.eq L_1^G times.o L_2^G.
  $
  The subgroup $attach((H_1 times H_2), tl: (x,y)) inter G_0$ of $G times G$
  corresponds to the subgroup $attach(H_1, tl: x) inter attach(H_2, tl: y)$ of
  $G$ under the isomorphism from $G_0$ to $G$. Moreover,
  $x times.o L_1 tilde.equiv attach(L_1, tl: x)$ and
  $y times.o L_2 tilde.equiv attach(L_2, tl: y)$, so that we can identify the
  $R(attach((H_1 times H_2), tl: (x,y)) inter G_0)$-module
  $attach((L_1 \# L_2), tl: (x,y))$ with the
  $R(attach(H_1, tl: x) inter attach(H_2, tl: y))$-module
  $(attach(L_1, tl: x) times.o attach(L_2, tl: y))|_(attach(H_1, tl: x) inter
  attach(H_2, tl: y))$, using the $R$-isomorphism given above. Hence the summand
  $(attach((L_1 \# L_2), tl: (x,y))|_(attach((H_1 times H_2), tl: (x,y))
    inter G_0))^(G_0)$
  of $(L_1 \# L_2)^(G times G)|_(G_0)$ corresponds to the direct summand
  $((attach(L_1, tl: x) times.o attach(L_2, tl: y))|_(attach(H_1, tl: x)
    inter attach(H_2, tl: y)))^G$
  of $L_1^G times.o L_2^G$.

  Finally, we have to check that the $(G_0,H_1 times H_2)$-double cosets in
  $G times G$ correspond to the $(H_1,H_2)$-double cosets in $G$. More
  precisely, we have to show that $(x,y)$ and $(u,v)$ belong to the same
  $(G_0,H_1 times H_2)$-double coset if and only if
  $H_1 x^(-1)y H_2=H_1 u^(-1)v H_2$. Suppose
  $ G_0 lr((x,y))(H_1 times H_2)=G_0 lr((u,v))(H_1 times H_2). $
  #source(264)
  Then for some elements $h_1,h'_1 in H_1$, $h_2,h'_2 in H_2$, and $g,g' in G$,
  we have
  $ (g x h_1,g y h_2)=(g' u h'_1,g' v h'_2). $
  Upon eliminating $g$ and $g'$ from these equations, we obtain
  $H_1 x^(-1)y H_2=H_1 u^(-1)v H_2$. The steps can be reversed, and our
  assertion is proved. This completes the proof of the theorem.
]

#corollary[
  Let $H_1,H_2,G,L_1,L_2$ be as in @th:mackey-tensor-product, and assume that
  $L_1$ and $L_2$ are $R$-free modules with finite bases, affording characters
  $lambda_1$ and $lambda_2$ of $H_1$ and $H_2$, respectively. Then the modules
  $L_1^G$, $L_2^G$, $L_1^G times.o L_2^G$ and
  $[(attach(L_1, tl: x) times.o attach(L_2, tl: y))_(attach(H_1, tl: x) inter
    attach(H_2, tl: y))]^G$
  are all $R$-free modules with finite bases. The character
  $lambda_1^G lambda_2^G$ afforded by $L_1^G times.o L_2^G$ is given by
  $
    lambda_1^G lambda_2^G=sum_(x^(-1)y in D)
    [(attach(lambda_1, tl: x) attach(lambda_2, tl: y))|_(attach(H_1, tl: x)
      inter attach(H_2, tl: y))]^G,
  $
  where the sum is taken over the $(H_1,H_2)$-double cosets $D$. Moreover,
  $
    [(attach(lambda_1, tl: x) attach(lambda_2, tl: y))|_(attach(H_1, tl: x)
      inter attach(H_2, tl: y))]^G
    =[(attach(lambda_1, tl: u) attach(lambda_2, tl: v))|_(attach(H_1, tl: u)
      inter attach(H_2, tl: v))]^G
  $
  whenever $x^(-1)y$ and $u^(-1)v$ belong to the same double coset $D$.
] <cor:mackey-character-product>
The proof is immediate from Theorem @th:mackey-tensor-product, using the fact
that the character of the inner tensor product of $R$-free $R G$-modules is the
product of the characters of the factors. The fact that the modules $L_1^G$,
$L_2^G$, etc., are $R$-free with finite basis follows from the discussion in
§@ss:induction-frobenius and the proof of the Subgroup Theorem.

#example(numbered: false)[
  We interpret Corollary @cor:mackey-character-product in the context of
  permutation characters (see Example @exm:induced-trivial-permutation). Let
  $H_1$ and $H_2$ be subgroups of $G$, and $1_(H_1)$ and $1_(H_2)$ the
  $R$-characters of $H_1$ and $H_2$ afforded by the trivial modules. Then
  $
    1_(H_1)^G dot 1_(H_2)^G=plus.o.big_(x^(-1) in D)
    (1_(attach(H_1, tl: x) inter H_2))^G,
  $
  where the sum is taken over the double cosets $D$ in
  $H_1 backslash G slash H_2$. Thus the set of $ZZ$-linear combinations of the
  induced permutation characters from subgroups of $G$ is closed under
  multiplication, and is called the _Burnside ring_#idx("Burnside ring") of $G$
  (see Chapter~5 of Volume~II).
]

We conclude this section with a useful special case of the Tensor Product
Theorem:

#source(265)
#corollary[
  Let $L$ be a left $R H$-module, for a subgroup $H$ of $G$, and let $M$ be a
  left $R G$-module. Then there is an isomorphism of $R G$-modules:
  $ M times.o_R L^G tilde.equiv (M_H times.o_R L)^G. $
] <cor:induction-tensor-identity>

=== The Intertwining Number Theorem <ss:intertwining-number>

Our objective is to compute $Hom_(R G) lr((L_1^G,L_2^G))$, where $L_1$ is an
$R H_1$-module, $L_2$, an $R H_2$-module, with $H_1$ and $H_2$ subgroups of $G$.
Throughout this subsection, $G$ denotes a finite group and $R$ an arbitrary
commutative ring. We begin with a new version of the Frobenius Reciprocity
Theorem:

#proposition[
  Let $H <= G$, and let $M$ be an $R G$-module, $L$ an $R H$-module. Then there
  is an $R$-isomorphism
  $ Hom_(R G) lr((M,L^G)) tilde.equiv Hom_(R H) lr((M_H,L)). $
  #idx("Frobenius Reciprocity Theorem")
] <prop:frobenius-right-adjoint>
#proof[
  Let $G=union.dot.big_(i=1)^n g_i H$, $n=|G:H|$, $g_1=1$. Given
  $phi in Hom_(R G) lr((M,L^G))$ we may write
  $ phi(m)=sum_(i=1)^n g_i times.o theta_i lr((m)), m in M, $
  with each $theta_i in Hom_R lr((M,L))$. From the equation
  $g_i^(-1)phi(m)=phi(g_i^(-1)m)$ we obtain
  $theta_1 lr((g_i^(-1)m))=theta_i lr((m))$, so
  $
    phi(m)=1 times.o theta(m)+g_2 times.o theta(g_2^(-1)m)+dots
    +g_n times.o theta(g_n^(-1)m), m in M,
  $ <eq:frobenius-right-adjoint-map>
  where $theta$ denotes $theta_1$. Clearly $theta in Hom_(R H) lr((M_H,L))$, and
  we claim that the desired isomorphism is given by $phi arrow.r theta$. It
  suffices to show that for each $theta$, formula
  @eq:frobenius-right-adjoint-map defines a $G$-homomorphism $phi$. For
  $x in G$, we have
  $
    phi(x m)=sum g_j times.o theta(g_j^(-1)x m),
    x phi(m)=sum x g_i times.o theta(g_i^(-1)m), m in M.
  $
  Write $x g_i=g_j h$, where $h in H$; as $i$ ranges from $1$ to $n$, so does
  $j$. Further, for $m in M$ we have
  $
    x g_i times.o theta(g_i^(-1)m)=g_j times.o h theta(g_i^(-1)m)
    =g_j times.o theta(h g_i^(-1)m)=g_j times.o theta(g_j^(-1)x m).
  $
  It follows that $phi(x m)=x phi(m)$ for all $x in G$, $m in M$, which
  completes the proof.
]

Using this, we obtain our first main result:

#source(266)
#theorem[
  Let $L_1$ be an $R H_1$-module, $L_2$ an $R H_2$-module, where $H_1$ and $H_2$
  are subgroups of $G$. For $x,y in G$, the $R$-module
  $
    Hom_(R(attach(H_1, tl: x) inter attach(H_2, tl: y))) lr(
      (attach(L_1, tl: x),attach(L_2, tl: y))
    )
  $
  depends only upon the double coset $D in H_1 backslash G slash H_2$ to which
  $x^(-1)y$ belongs. Moreover,
  $
    Hom_(R G) lr((L_1^G,L_2^G)) tilde.equiv plus.o.big_(x^(-1)y in D)
    Hom_(R(attach(H_1, tl: x) inter attach(H_2, tl: y))) lr(
      (attach(L_1, tl: x),attach(L_2, tl: y))
    )
  $
  as $R$-modules, where the sum is taken over all
  $D in H_1 backslash G slash H_2$.
] <th:intertwining-modules>
#proof[
  By the Subgroup Theorem and the two versions of the Frobenius Reciprocity
  Theorem, we have $R$-isomorphisms
  $
    Hom_(R G) lr((L_1^G,L_2^G))
    &tilde.equiv Hom_(R H_1) lr((L_1,L_2^G|_(H_1))) \
    &tilde.equiv plus.o.big_(D=H_1 a H_2) Hom_(R H_1)
    lr((L_1,(attach(L_2, tl: a)|_(H_1 inter attach(H_2, tl: a)))^(H_1))) \
    &tilde.equiv plus.o.big_D Hom_(R(H_1 inter attach(H_2, tl: a)))
    lr((L_1,attach(L_2, tl: a))).
  $
  If we write $a=x^(-1)y$ and apply conjugation by $x$ to all of the modules and
  subgroups occurring in the $D$-th summand above, we obtain the result in the
  originally-stated form.
]

Let us apply this result to the familiar situation where $K$ is a subfield of
the complex field, and is a splitting field for $G$ and all its subgroups (as in
§@ss:finite-group-character-orthogonality). Then
@prop:character-scalar-products-multiplicities(iii) gives
$ dim_K Hom_(K G) lr((M,M'))=(mu,mu')_G, $
where $M$ and $M'$ are f.g. left $K G$-modules affording characters $mu$ and
$mu'$, respectively. As an immediate consequence of @th:intertwining-modules, we
obtain:

#theorem(name: "Intertwining Number Theorem")[
  Let $K$ be a subfield of $CC$ which is a splitting field for $G$ and its
  subgroups, and let $lambda_i$ be the $K$-character of $H_i$ afforded by a
  $K H_i$-module $L_i$, where $H_i <= G$, $i=1,2$. Then
  $
    (lambda_1^G,lambda_2^G)=sum_(x^(-1)y in D)
    (attach(lambda_1, tl: x),attach(lambda_2, tl: y))_(attach(H_1, tl: x)
    inter attach(H_2, tl: y)),
  $
  where the sum extends over $D in H_1 backslash G slash H_2$.
  #idx("Intertwining Number Theorem")
] <th:intertwining-number>

As a corollary, we have

#source(267)
#theorem(name: "Criterion for Irreducibility of Induced Characters")[
  Let $K$ be a splitting field for $G$ as above, and let $lambda$ be an
  irreducible $K$-character of $H$. Then $lambda^G$ is an irreducible
  $K$-character of $G$ if and only if
  $ (lambda,attach(lambda, tl: x))_(H inter attach(H, tl: x))=0 $
  for all $x in.not H$.
  #idx("Criterion for Irreducibility of Induced Characters")
] <th:induced-character-irreducibility>
#proof[
  The criterion for irreducibility of $lambda^G$ is that
  $(lambda^G,lambda^G)=1$, by
  @prop:character-scalar-products-multiplicities(ii). The equivalence of this
  statement with the assertion of @th:induced-character-irreducibility is
  immediate from the Intertwining Number Theorem.
]

=== Contragredient Modules <ss:contragredient-modules>

Throughout this section let $G$ be a finite group and $R$ an arbitrary
commutative ring. An _$R$-lattice_#idx("R-lattice")#idx("lattice") is a f.g.
projective left $R$-module. An _$R G$-lattice_#idx("RG-lattice") is a left
$R G$-module whose underlying $R$-module is an $R$-lattice.

The _dual_ $L^*$ of an $R$-lattice $L$ is the $R$-module $Hom_R lr((L,R))$.
#idx("dual lattices")#idx("dual of module") The following lemma shows that duals
of $R$-lattices are again $R$-lattices:

#lemma[
  Let $L$ and $M$ be $R$-lattices. Then
  #enum(
    numbering: "(i)",
    [$(L plus.o M)^* tilde.equiv L^* plus.o M^*$,],
    [$L^*$ is an $R$-lattice,],
    [$(L^*)^* tilde.equiv L$,],
    [$Hom_R lr((L,M))$ and $L times.o_R M$ are $R$-lattices.],
  )
] <lem:lattice-duals>
#proof[
  (i) follows from the additivity of the Hom functor (see
  §@sec:hom-tensor-projective-injective-flat). Next, assertions (ii)–(iv) are
  easily checked when $L$ and $M$ are $R$-free $R$-lattices. Since direct
  summands of lattices are lattices, and since the expressions in (ii)–(iv) are
  additive in the variables involved, it follows that (ii)–(iv) are true for
  arbitrary lattices.
]

Given a left $R G$-lattice $L$, we wish to define an action of $G$ on $L^*$ so
as to make $L^*$ into a left $R G$-lattice. By @lem:lattice-duals(ii), $L^*$ is
already an $R$-lattice, so we must make $L^*$ into a left $G$-module. For
$x in G$ and $phi in L^*$, define $x phi in L^*$ by
$ (x phi)(l)=phi(x^(-1)l), l in L. $
Then $(x y)phi=x(y phi)$ for all $x,y in G$, $phi in L^*$, so $L^*$ is indeed a
left $R G$-lattice, called the _contragredient_ of $L$.#idx(
  "contragredient module",
) The action of $sum alpha_x x in R G$ on $L^*$ is given by
$ {(sum alpha_x x)phi}l=sum alpha_x phi(x^(-1)l), l in L. $

#source(268)
#remarks[
  #enum(
    numbering: "(i)",
    [Since $L$ is an $(R G,R)$-bimodule, $Hom_R lr((L,R))$ acquires the
      structure of a right $R G$-module by virtue of the action of $R G$ from
      the left on $L$ (see §@ss:homomorphisms). We then use the
      anti-automorphism $sum alpha_x x arrow.r sum alpha_x x^(-1)$ of $R G$ to
      make $Hom_R lr((L,R))$ into a left $R G$-module, thereby obtaining the
      contragredient $L^*$ of $L$.],
    [It is easily verified that the isomorphisms in @lem:lattice-duals are
      $R G$-isomorphisms in case $L$ and $M$ are $R G$-lattices.],
  )
] <rem:contragredient-actions>

When $L$ is an $R$-free $R G$-lattice, affording the matrix representation
$upright(bold(L))$ of $G$ with respect to an $R$-basis ${l_i}$ of $L$, we may
compute the matrix representation afforded by the contragredient $L^*$ as
follows: let ${phi_j}$ be the dual basis of $L^*$, so
$phi_j lr((l_i))=delta_(i j)$. Relative to this basis ${phi_j}$, $L^*$ affords
the matrix representation $upright(bold(L))^*$, where
$
  upright(bold(L))^* lr((x))=attach(upright(bold(L)), tl: t) lr((x^(-1))), x
  in G,
$
#idx("contragredient representation")
and the superscript $t$ denotes “transpose”. If $L$ affords the character
$lambda$ of $G$, and $L^*$ affords $lambda^*$, we have
$ lambda^* lr((x))=lambda(x^(-1)), x in G. $
In particular, if $L$ is a f.g. $K G$-module, where $K$ is a subfield of the
complex field as in §@ss:finite-group-character-orthogonality, then the
contragredient character $lambda^*$ is given by
$ lambda^* lr((x))=overline(lambda(x)), x in G, $
#idx("contragredient character")
where bar denotes complex conjugation.

#proposition[
  Let $H <= G$, and let $L$ be an $R H$-lattice. Then $L^G$, $(L^G)^*$ and
  $(L^*)^G$ are $R G$-lattices, and there is an $R G$-isomorphism
  $ (L^G)^* tilde.equiv (L^*)^G. $
] <prop:contragredient-induction>
#remark(numbered: false)[
  If $R$ is a subfield of the complex field, the character afforded by $L^*$ is
  $overline(lambda)$, where $L$ affords $lambda$. In this case, the proposition
  is the simple fact that $overline(lambda^G)=(overline(lambda))^G$.
]
#proof[
  Let $G=union.dot.big_(i=1)^n g_i H$, where $n=|G:H|$. As already pointed out
  in §@ss:induction-frobenius, $L^G$ is $R$-isomorphic to the direct sum of $n$
  copies of $L$, and is thus an $R$-lattice. Thus $L^*$ and $(L^G)^*$ are also
  $R$-lattices by @lem:lattice-duals. We have $R$-module decompositions
  $
    L^G=plus.o.big_(i=1)^n g_i times.o L,
    (L^*)^G=plus.o.big_(i=1)^n g_i times.o L^*.
  $
  #source(269)
  For each $i$, $1 <= i <= n$, define $f_i: L^* -> (L^G)^*$ by
  $
    f_i lr((phi))(g_j times.o l)=delta_(i j) phi(l),
    delta_(i j)="Kronecker delta".
  $
  The map $F: (L^*)^G -> (L^G)^*$ given by
  $ F lr((sum g_i times.o phi_i))=sum f_i lr((phi_i)) $
  is easily shown to be an $R$-isomorphism. To check that it is an
  $R G$-isomorphism, we must verify that
  $ F(x g_i times.o phi)=x f_i lr((phi)) "for all" x in G, phi in L^*. $
  As usual, write $x g_i=g_j h$ where $h in H$ and $1 <= j <= n$; then
  $ F(x g_i times.o phi)=F(g_j times.o h phi)=f_j lr((h phi)). $
  For $1 <= k <= n$ and $l in L$, we obtain
  $
    F(x g_i times.o phi) dot (g_k times.o l)
    ={f_j lr((h phi))} dot (g_k times.o l)
    =delta_(j k)(h phi)l=delta_(j k)phi(h^(-1)l),
  $
  while
  $
    {x f_i lr((phi))} dot (g_k times.o l)
    =f_i lr((phi)) dot (x^(-1)g_k times.o l)
    =cases(0 & quad k != j, phi(h^(-1)l) & quad k=j),
  $
  and the proof is completed.
]

An important consequence is as follows:

#corollary[
  The group ring $R G$ is _self-contragredient_,#idx("self-contragredient") that
  is, $(R G)^* tilde.equiv R G$ as left $R G$-modules. For each f.g. projective
  $R G$-module $P$, its contragredient $P^*$ is also projective.
] <cor:group-ring-self-contragredient>
#proof[
  The formula $(R G)^* tilde.equiv R G$ follows from
  @prop:contragredient-induction, by taking $H={1}$ and $L$ the $R H$-module $R$
  on which $H$ acts trivially. If $P$ is projective, then
  $P plus.o Q tilde.equiv (R G)^((n))$ for some $Q$ and $n$, whence $P^*$ is a
  summand of $((R G)^*)^((n))$.
]

Given a pair of $R G$-lattices $M$ and $N$, we constructed a new $R G$-lattice
$M times.o_R N$ by using the actions of $G$ on $M$ and $N$. There is an
analogous construction in which we form the $R$-lattice $Hom_R lr((M,N))$, and
let $G$ act on it. Since $G$ acts from the left on both $M$ and $N$, it follows
from §@ss:homomorphisms that $Hom_R lr((M,N))$ is naturally a $(G,G)$-bimodule.
In order to make it into a left $G$-module, we define
$ (x ast f)m=x f(x^(-1)m) "for" x in G, f in Hom_R lr((M,N)), m in M. $

#source(270)
Then $Hom_R lr((M,N))$ becomes a left $R G$-lattice (by linearity). Its relation
to inner tensor products is given by

#proposition[
  Let $M$ and $N$ be left $R G$-lattices. Then
  $ M^* times.o_R N tilde.equiv Hom_R lr((M,N)) $
  as left $R G$-lattices.
] <prop:contragredient-hom-tensor>
#proof[
  We define a map
  $ theta: M^* times.o_R N -> Hom_R lr((M,N)) $
  by
  $
    f times.o n arrow.r [f,n] "for" f in M^*, n in N,
    "where" [f,n]m=f(m)n "for" m in M.
  $
  Since $M$ is an $R$-lattice, $theta$ is an $R$-isomorphism by
  @prop:projective-hom-tensor. We must verify that $theta$ is a left
  $G$-homomorphism. For $x in G$, we have
  $ theta{x(f times.o n)}=theta(x f times.o x n)=[x f,x n]. $
  For all $m in M$,
  $ [x f,x n]m=(x f)(m) dot x n=f(x^(-1)m)x n=x f(x^(-1)m)n. $
  On the other hand,
  $ {x ast theta(f times.o n)}m=(x ast [f,n])m=x[f,n]x^(-1)m=x f(x^(-1)m)n. $
  This shows that $theta$ is a left $G$-homomorphism, and establishes the
  Proposition.
]

We now introduce the functor
$ op("inv")_G: attach(frak(M), bl: R G) -> attach(frak(M), bl: R) $
which assigns to each $R G$-module $M$ the $R$-module $op("inv")_G lr((M))$
defined by
$ op("inv")_G lr((M))={m in M: x m=m "for all" x in G}. $
We call $op("inv")_G lr((M))$ the module of _$G$-invariants_ of $M$. #idx(
  "G-invariants",
)#idx("invariant (G-)")
#idx("$\"inv\"_G M$ = $G$-invariants of $M$")
It is clear from the definition that $op("inv")_G$ is a functor (see
§@ss:categories-functors).

The connection between the functor $op("inv")_G$ and $Hom_(R G)$, given in (ii)
below, already occurred in a special case in Exercise
@exc:contragredient-character-orthogonality.

#proposition[
  #enum(
    numbering: "(i)",
    [Let $H <= G$, and let $L$ be an $R H$-lattice. Then
      $ op("inv")_H lr((L)) tilde.equiv op("inv")_G lr((L^G)) $
      as $R$-modules.],
    [#source(271)
      Let $M$ and $N$ be $R G$-lattices. Then
      $ op("inv")_G lr((M^* times.o_R N)) tilde.equiv Hom_(R G) lr((M,N)) $
      as $R$-modules.],
  )
] <prop:invariants-induction-hom>
#proof[
  (i) If $G=union.dot g_i H$, then $L^G=plus.o g_i times.o L$ by
  §@ss:induction-frobenius. It is then easily checked that
  $ op("inv")_G lr((L^G))=(sum g_i) times.o op("inv")_H lr((L)), $
  which implies (i).

  For (ii), use the isomorphism in @prop:contragredient-hom-tensor, so
  $
    op("inv")_G lr((M^* times.o_R N)) tilde.equiv
    op("inv")_G Hom_R lr((M,N)).
  $
  But an element $f in Hom_R lr((M,N))$ is $G$-invariant if and only if
  $x ast f=f$ for all $x in G$, that is, $x f x^(-1)=f$ for all $x in G$, and
  this in turn means that $f in Hom_(R G) lr((M,N))$.
]

Each left $R G$-lattice $M$ determines another left $R G$-lattice $M^*$, the
contragredient of $M$. If $L$ and $M$ are left $R G$-lattices, then each
$f in Hom_(R G) lr((L,M))$ determines a map $f^* in Hom_(R G) lr((M^*,L^*))$.
Indeed, for each $phi in M^*$ we have
$ f^* lr((phi))=phi f $
(compare with §@ss:homomorphisms), and it is easily checked that $f^*$ is an
$R G$-homomorphism. The correspondence $M arrow.r M^*$, $f arrow.r f^*$, thus
yields a contravariant functor from the category of left $R G$-lattices to
itself. This functor is an involution, that is,
$ M^(**) tilde.equiv M, f^(**) tilde.equiv f. $
It follows at once that there is an isomorphism of $R$-modules
$ Hom_(R G) lr((L,M)) tilde.equiv Hom_(R G) lr((M^*,L^*)), $
<eq:contragredient-hom-duality>
given by $f arrow.r f^*$, $f in Hom_(R G) lr((L,M))$. This also follows from
@prop:invariants-induction-hom(ii), since both sides of
@eq:contragredient-hom-duality are $R$-isomorphic to
$op("inv")_G lr((L^* times.o_R M))$.

=== Outer Tensor Products <ss:outer-tensor-products>

Throughout this subsection, $K$ denotes an arbitrary field, and all modules
which occur are assumed to be f.d./$K$. Given a left $K G$-module $M$ and a left
$K H$-module $N$, we may form their outer tensor product $M \# N$. #idx(
  "outer tensor product",
)#idx("Tensor Product Theorem") This is a left $K(G times H)$-module, defined as
the $K$-vector space $M times.o_K N$, on which the direct product $G times H$
acts according to the formula
$
  (g,h) dot sum m_i times.o n_i=sum g m_i times.o h n_i,
  g in G, h in H, m_i in M, n_i in N.
$
#source(272)
In §@ss:mackey-theorems, we have already seen the importance of this concept.
Our aim here is to study the relation between simple modules for $G$, $H$ and
$G times H$.

Our first main result is that if the field $K$ is a splitting field for both $G$
and $H$, and if both $M$ and $N$ are simple modules, then $M \# N$ is also a
simple module. Furthermore, in this case, every simple $K(G times H)$-module is
of the form $M \# N$, with $M$ and $N$ unique up to isomorphism. (This
generalizes the result of Exercise @exc:direct-product-characters.) As Example
@exm:serre-outer-tensor shows, the hypothesis on $K$ cannot be omitted in
general. We should emphasize the fact that the results given below are valid
even when $char K$ divides $|G|$ or $|H|$.

As we shall see, these facts about simple modules over group algebras are
special cases of more general results about modules over $K$-algebras $A$ for
which $A slash rad A$ is a separable $K$-algebra. Group algebras have this
property, as we have already proved in
@th:group-algebra-separable-radical-quotient.

We begin with:

#theorem[
  Let $K$ be a field which is a splitting field for the finite groups $G$ and
  $H$. Then:
  #enum(
    numbering: "(i)",
    [For each simple $K G$-module $M$ and each simple $K H$-module $N$, the
      outer tensor product $M \# N$ is a simple $K(G times H)$-module.],
    [Every simple $K(G times H)$-module is of the above form $M \# N$, with $M$
      and $N$ uniquely determined (up to isomorphism).],
  )
] <th:outer-tensor-split-simple>
#proof[
  We shall use the isomorphism of $K$-algebras
  $ End_K lr((M times.o N)) tilde.equiv (End_K M) times.o (End_K N), $
  <eq:endomorphisms-tensor-product>
  where $times.o$ means $times.o_K$, and $M,N$ are any f.d. $K$-spaces. Now let
  $M$ be a simple left $K G$-module; then the ring of left multiplications
  $(K G)_l$ on $M$ coincides with $End_K M$ by Burnside’s Theorem
  @th:burnside-full-matrix-algebra, since $K$ is a splitting field for $G$.
  Likewise, $(K H)_l=End_K N$ as rings of operators on $N$. From
  @eq:endomorphisms-tensor-product we obtain
  $ End_K lr((M times.o N)) tilde.equiv (K G)_l times.o (K H)_l. $
  But there is an obvious isomorphism of $K$-algebras
  $
    K(G times H) tilde.equiv K G times.o K H,
  $ <eq:group-algebra-direct-product>
  which we treat as an identification. Therefore
  $ End_K lr((M times.o N))={K(G times H)}_l. $
  Since $M times.o N$ is simple as ${End_K lr((M times.o N))}$-module, it
  follows that $M times.o N$ is simple as $K(G times H)$-module, so (i) is
  proved.

  #source(273)
  Now let $M'$ and $N'$ be simple $K G$- and $K H$-modules, respectively, such
  that
  $ M' \# N' tilde.equiv M \# N "as" K(G times H)"-modules". $
  Restricting the operator domain to $K(G times 1)$, we obtain
  $ (M')^((n')) tilde.equiv M^((n)) "as" K G"-modules", $
  where $n'=dim_K N'$, $n=dim_K N$. Since $M$ is simple, it follows that
  $M' tilde.equiv M^((k))$ for some $k$. Likewise, $N' tilde.equiv N^((j))$ for
  some $j$. But then $k=j=1$, so $M' tilde.equiv M$, $N' tilde.equiv N$, as
  desired.

  Finally, let ${M_i:1 <= i <= s}$ be a basic set of simple left $K G$-modules,
  and let ${N_j:1 <= j <= t}$ be a corresponding set for $K H$. To complete the
  proof of the theorem, we need to show that the $s t$ modules ${M_i \# N_j}$
  are a basic set of simple $K(G times H)$-modules. This is clear from
  @th:split-group-algebra-dimensions when $char K=0$, since $s$ and $t$ are the
  number of conjugacy classes in $G$ and $H$, respectively, while $s t$ is the
  corresponding number for $G times H$. On the other hand, when $char K=p>0$,
  the desired result follows from @cor:brauer-number-simple-modules, since $s$
  and $t$ are the number of $p$-regular conjugacy classes in $G$ and $H$,
  respectively. This establishes the theorem. For another proof, see
  @th:outer-tensor-separable below. Also see Exercise
  @exc:direct-product-characters for the case where $K=CC$.
]

Before generalizing the above theorem, let us give Serre’s example to show that
the hypothesis on $K$ cannot be omitted.

#example[
  Let $G={plus.minus 1,plus.minus i,plus.minus j,plus.minus k}$ be the
  quaternion group of order $8$, acting from the left on the skewfield of
  rational quaternions
  $ bb(H)=QQ plus.o QQ i plus.o QQ j plus.o QQ k. $
  #idx("quaternion group")#idx("group", "quaternion") By
  @exm:quaternion-group-algebra-reduced-norm, $bb(H)$ is a simple left
  $QQ G$-module. Now let $H=⟨ x ⟩$ be a cyclic group of order $3$, and let
  $ xi=-(1+i+j+k)/2 in bb(H). $
  Then $xi^3=1$ in $bb(H)$, and we may let $x$ act on $bb(H)$ by right
  multiplication by $xi$. Then $bb(H)$ is a simple left $QQ(G times H)$-module,
  and $bb(H)$ cannot be expressed in the form $M \# N$, with $M$ and $N$ simple
  $QQ G$- and $QQ H$-modules. For further discussion of this point, see the last
  paragraph in this subsection.
] <exm:serre-outer-tensor>

In the proof of Theorem @th:outer-tensor-split-simple, we needed to work with
group algebras (rather than arbitrary f.d. $K$-algebras) in order to use
@eq:group-algebra-direct-product, and also for counting the number of modules in
a basic set of simple modules. We shall give a generalization of
@th:outer-tensor-split-simple, whose proof is based on somewhat different ideas.
This has the advantage of avoiding the counting argument, as well as providing
information about what happens when $K$ is not a splitting field.

#source(274)
As a first step, we prove an easy lemma:

#lemma[
  Let $A$ and $B$ be f.d. $K$-algebras, and let $M$ and $N$ be left $A$- and
  $B$-modules, respectively. Denote $times.o_K$ by $times.o$, for brevity. Let
  $M times.o N$ be the left $(A times.o B)$-module on which $A times.o B$ acts
  by the formula
  $
    (sum a_i times.o b_i)(sum m_j times.o n_j)=sum_(i,j) a_i m_j times.o b_i
    n_j.
  $
  Then
  $
    End_(A times.o B) lr((M times.o N)) tilde.equiv (End_A M) times.o (End_B N).
  $
] <lem:outer-tensor-endomorphisms>
#proof[
  It suffices to prove that
  $ End_(A times.o B) lr((M times.o N)) subset (End_A M) times.o (End_B N), $
  the reverse inclusion being obvious. By @eq:endomorphisms-tensor-product, each
  $z in End_(A times.o B) lr((M times.o N))$ is expressible as
  $ z=sum alpha_i times.o beta_i, alpha_i in End_K M, beta_i in End_K N, $
  where we may assume the ${beta_i}$ are linearly independent over $K$. For each
  $a in A$, we have $(a times.o 1)z=z(a times.o 1)$, so
  $ sum (a alpha_i-alpha_i a) times.o beta_i=0 "for all" a in A. $
  Therefore
  $ a alpha_i=alpha_i a "for each" i "and for all" a in A, $
  and thus each $alpha_i in End_A M$. We may now rewrite $z$ as
  $ z=sum lambda_j times.o mu_j, lambda_j in End_A M, mu_j in End_K N, $
  with the ${lambda_j}$ linearly independent over $K$. The preceding argument
  then shows that each $mu_j in End_B N$, and the lemma is established.
]

Our second main result, which includes @th:outer-tensor-split-simple as a
special case, is as follows:

#theorem[
  Let $A$ and $B$ be f.d. $K$-algebras such that both $A slash rad A$ and
  $B slash rad B$ are separable $K$-algebras. Let $times.o$ denote $times.o_K$.
  Then
  #enum(
    numbering: "(i)",
    [For each simple $A$-module $M$ and each simple $B$-module $N$, the
      $(A times.o B)$-module $M times.o N$ is semisimple. Furthermore,
      $M times.o N$ is a simple $(A times.o B)$-module if and only if
      $ (End_A M) times.o_K (End_B N) "is a division algebra". $],
    [#source(275)
      If either $A slash rad A$ or $B slash rad B$ is a split semisimple
      $K$-algebra, then for each simple $A$-module $M$ and each simple
      $B$-module $N$, $M times.o N$ is a simple $(A times.o B)$-module.],
    [Under the hypotheses of (ii), every simple $(A times.o B)$-module is of the
      form $M times.o N$, with $M$ and $N$ as above. Further, if
      $M' times.o N' tilde.equiv M times.o N$, then $M' tilde.equiv M$ and
      $N' tilde.equiv N$.],
  )
] <th:outer-tensor-separable>
#proof[
  Let $overline(A)=A slash rad A$, $overline(B)=B slash rad B$, so $overline(A)$
  and $overline(B)$ are f.d. separable $K$-algebras, by hypothesis. Then
  $overline(A) times.o overline(B)$ is also a separable $K$-algebra, by Exercise
  @exc:separable-field-base-extension. Let us show that
  $
    overline(A) times.o overline(B) tilde.equiv
    (A times.o B) slash rad(A times.o B).
  $ <eq:tensor-semisimple-quotients>
  We note first that the homomorphism theorem implies:
  $
    overline(A) times.o overline(B) tilde.equiv
    (A times.o B) slash {(rad A) times.o B+A times.o (rad B)}.
  $
  The denominator (on the right hand side above) is a nilpotent ideal of
  $A times.o B$, and is therefore contained in $rad(A times.o B)$. On the other
  hand, this denominator contains $rad(A times.o B)$, since
  $overline(A) times.o overline(B)$ is separable (and therefore semisimple).
  This establishes formula @eq:tensor-semisimple-quotients.

  Now let ${M_i}$ be a basic set of simple left $A$-modules, and let ${N_j}$ be
  a basic set of simple left $B$-modules. There are isomorphisms (of modules):
  $
    overline(A) tilde.equiv product.co M_i^((m_i)),
    overline(B) tilde.equiv product.co N_j^((n_j)).
  $
  Therefore
  $
    overline(A) times.o overline(B) tilde.equiv
    product.co_(i,j)(M_i times.o N_j)^((m_i n_j)).
  $
  It follows at once from @eq:tensor-semisimple-quotients that each
  $M_i times.o N_j$ is a semisimple $(A times.o B)$-module, so the first part of
  (i) is proved. However, once we know that $M_i times.o N_j$ is semisimple, we
  can test whether it is simple by calculating its endomorphism ring
  $End_(A times.o B) lr((M_i times.o N_j))$; indeed, by Exercise
  @exc:semisimple-module-endomorphisms, $M_i times.o N_j$ is simple if and only
  if this ring is a division algebra. Taking @lem:outer-tensor-endomorphisms
  into account, the proof of (i) is completed.

  (ii) Suppose that $A slash rad A$ is a split semisimple $K$-algebra. Then
  $End_A M tilde.equiv K$, while $End_B N$ is a division algebra $D$. Therefore
  $ (End_A M) times.o (End_B N) tilde.equiv K times.o D tilde.equiv D, $
  so $M times.o N$ is a simple module. Finally, (iii) follows at once from (ii),
  since every simple $(A times.o B)$-module occurs as a direct summand of
  $overline(A) times.o overline(B)$, and is
  #source(276)
  therefore of the form $M_i times.o N_j$ for some $i$ and $j$. This completes
  the proof of the Theorem, since the uniqueness assertion follows as in the
  proof of @th:outer-tensor-split-simple.
]

We may now analyze Example @exm:serre-outer-tensor in more detail. Let
$M=QQ plus.o QQ i plus.o QQ j plus.o QQ k$, viewed as left $QQ G$-module; then
$End_(QQ G) M tilde.equiv bb(H)$, the skewfield of rational quaternions. The
simple $QQ H$-modules are $QQ$ and $QQ(omega)$, where $omega$ is a primitive
cube root of $1$, and where $x$ acts as $1$ and $omega$, respectively, on these
modules. If $N=QQ(omega)$, then $End_(QQ H) N tilde.equiv QQ(omega)$, and
$ End_(QQ(G times H)) lr((M \# N)) tilde.equiv bb(H) times.o_(QQ) QQ(omega). $
It is easily verified that
$ bb(H) times.o_(QQ) QQ(omega) tilde.equiv M_2 lr((QQ(omega))), $
and therefore $M \# N tilde.equiv W plus.o W$, where $W$ is a simple
$QQ(G times H)$-module. (In fact, $W$ is precisely the module constructed in
Example @exm:serre-outer-tensor).

#exercises-heading

Throughout these exercises, $R$ denotes a commutative ring, $G$ is a finite
group, and $K$ is a field of characteristic $0$ which is a splitting field for
$G$ and all of its subgroups.

#exercise[
  Let $G$ be a finite group of order $n$, and $R$ a commutative ring. Let
  $1_({1})$ denote the trivial $R$-representation of the trivial subgroup ${1}$.
  Prove that the induced representation $1_({1})^G$ is equivalent to the
  representation afforded by the left regular module $R G$. Further, prove that
  $R G$ affords a matrix representation $upright(bold(U)): G -> M_n lr((R))$,
  where
  $ upright(bold(U))(g)=(delta_(g_i,g g_j))_(1 <= i,j <= n), g in G, $
  and $G={g_1,dots,g_n}$.
  #hint([@exc:regular-induced-trivial])[
    Compare $upright(bold(U))(g)$ with the matrix @eq:induced-matrix.
  ]
] <exc:regular-induced-trivial>

#exercise[
  Let $G$ be a finite group, $Omega$ a $G$-set, and $K$ a splitting field of
  characteristic zero, as in §@ss:finite-group-character-orthogonality. Let
  $theta$ be the character of the permutation representation of $G$ on $Omega$
  (see @exm:induced-trivial-permutation); we shall call $theta$ the _permutation
  character_ associated with the $G$-set $Omega$. #idx(
    "permutation character",
  )#idx("character", "permutation")
  #enum(
    numbering: "(i)",
    [For each $x in G$, prove that $theta(x)$ is the number of points in $Omega$
      fixed by $x$, so
      $ theta(x)=op("card"){w in Omega: x w=w}. $],
    [Prove that the scalar product $(theta,1_G)$ is the number of $G$-orbits in
      $Omega$, where $1_G$ is the trivial character of $G$. In particular, show
      that $Omega$ is a _transitive_#idx("transitive") $G$-set if and only if
      $(theta,1_G)=1$.],
    [If $Omega$ and $Omega'$ are transitive $G$-sets with permutation characters
      $theta$ and $theta'$, respectively, prove that $theta theta'$ is the
      character of the $G$-set $Omega times Omega'$ with diagonal action of
      #source(277)
      $G$. Hence
      $
        (theta,theta')=(theta theta',1_G)
        ="number of" G"-orbits in" Omega times Omega'.
      $
      As an application, show that if $X,Y <= G$, then
      $ (1_X^G,1_Y^G)=op("card"){X backslash G slash Y}. $],
  )
] <exc:permutation-character-orbits>

#exercise[
  Keep the notation of Exercise @exc:permutation-character-orbits. A transitive
  $G$-set $Omega$ with $abs(Omega)>=2$ is called _2-transitive_ (or _doubly
  transitive_) #idx("doubly transitive") if for any two ordered pairs $(u,v)$,
  $(u',v')$ from $Omega times Omega$, with $u != v$, $u' != v'$, there exists
  $g in G$ such that $g u=u'$ and $g v=v'$.
  #enum(
    numbering: "(i)",
    [Prove that $Omega$ is $2$-transitive if and only if $(theta,theta)=2$, or
      equivalently, if and only if $op("card"){H backslash G slash H}=2$, where
      $theta$ is the permutation character and $H=op("Stab")_G w$ for some
      $w in Omega$.],
    [Prove that if $Omega$ is $2$-transitive, then
      $ theta=1_G+zeta $
      for some non-trivial character $zeta in Irr_K G$.],
  )
] <exc:doubly-transitive-character>

#exercise[
  (Gluck). Let $G=GL_3 lr((k))$, where $k$ is a finite field, and let $Omega$ be
  the left $G$-set consisting of all nonzero $3 times 1$ column vectors over
  $k$. The stabilizer of
  $
    e_1=vec(1, 0, 0) in Omega "is" H={mat(
        delim: "[", 1, ast, ast; 0, ast,
        ast; 0, ast, ast
      ) in G}.
  $
  Now $G$ acts transitively on $Omega$, so $Omega tilde.equiv G slash H$ as left
  $G$-sets, by §@ss:background-group-theory. For $g in G$, we have
  $ 1_H^G lr((g))=op("card"){w in Omega:(g-1)w=0}. $
  Now let $Omega'$ be the set of nonzero $1 times 3$ row vectors, and view
  $Omega'$ as a left $G$-set with action given by
  $ g w'=w' g^(-1), g in G, w' in Omega'. $
  The stabilizer of $(1,0,0)$ in $G$ is
  $ H'={mat(delim: "[", 1, 0, 0; ast, ast, ast; ast, ast, ast) in G}. $
  Show that $H'$ is not $G$-conjugate to $H$, since $H'$ does not stabilize any
  element of $Omega$. For $g in G$, show that
  $ 1_H^G tilde.equiv 1_(H')^G, $
  but the $G$-sets $G slash H$ and $G slash H'$ are not isomorphic.
] <exc:gluck-permutation-characters>

#source(278)
#exercise[
  Let $H$ be a subgroup of $G$, and $psi$ a $K$-character of $H$. Let $x in G$,
  and let $frak(C)$ be the conjugacy class containing $x$. Prove that
  $ psi^G lr((x))=frac(|C_G lr((x))|, |H|) sum_(y in frak(C) inter H) psi(y). $
] <exc:induced-character-centralizer>

#exercise[
  Prove that the Frobenius Reciprocity Formula characterizes induction of class
  functions. In other words, show that if $psi in cf_K H$ and $psi' in cf_K G$
  satisfy the condition
  $ (psi',zeta)=(psi,zeta_H) $
  for all $zeta in cf_K G$, then $psi'=psi^G$.
] <exc:induction-characterized-reciprocity>

#exercise[
  (Janusz @bib:Janusz1966). Let $H <= G$, $zeta in Irr_K G$, and
  $psi in Irr_K H$. Assume that $(zeta,psi^G)=1$. Let $epsilon$ be the central
  primitive idempotent in $K G$ corresponding to $zeta$, and $e$ a primitive
  idempotent in $K H$ such that $K H e$ affords $psi$. Prove that the left ideal
  $K G e$ affords $psi^G$, and that $epsilon e$ is a primitive idempotent in
  $K G$ such that $K G epsilon e$ affords $zeta$. #hint(
    [@exc:induced-primitive-idempotent],
  )[
    First show that $K G e tilde.equiv K G times.o_(K H) K H e$, so $K G e$
    affords $psi^G$. Then show that $epsilon K G e=K G epsilon e$ is the
    homogeneous component of $K G e$ which is the sum of all simple submodules
    of $K G e$ affording $zeta$.
  ] (See @cor:induced-primitive-idempotent for another proof.)
] <exc:induced-primitive-idempotent>

#exercise[
  Let $H ⊴ G$. Prove that $1_H^G=tilde(rho)_(G slash H)$, where
  $tilde(rho)_(G slash H)$ is the lift of the regular character of $G slash H$
  (see Exercise @exc:quotient-character-lift).
] <exc:normal-induced-trivial>

#exercise[
  Let $H ⊴ G$, and let $psi in Irr_K H$. Then for each $x in G$, the conjugate
  character $attach(psi, tl: x) in Irr_K H$. Prove that $psi^G in Irr_K G$ if
  and only if $psi != attach(psi, tl: x)$ for all $x in.not H$.
  #hint([@exc:normal-subgroup-irreducible-induction])[
    Use @th:induced-character-irreducibility.
  ]
] <exc:normal-subgroup-irreducible-induction>

#exercise[
  Apply the preceding exercise to give an alternative construction of $Irr_K G$,
  for $G$ the dihedral group of order $2m$ (see @exm:dihedral-group-characters).
  Apply the same method to determine $Irr_K G$ for the generalized quaternion
  group $Q_m$ of order $4m$.
] <exc:dihedral-quaternion-induction>

#exercise[
  Apply the Tensor Product Theorem @th:mackey-tensor-product to decompose
  products of irreducible characters of the dihedral group $D_m$ (as in
  @exm:dihedral-group-characters) into their irreducible constituents. (See also
  @bib:CurtisReiner1962[CR §~48].)
] <exc:dihedral-character-products>

#exercise[
  Find the character tables of the symmetric and alternating groups $S_4$ and
  $A_4$.
  #hint([@exc:symmetric-alternating-four-characters])[
    Find proper normal subgroups, and study the induced characters from these
    normal subgroups, and the characters having the normal subgroup contained in
    their kernels.
  ]
] <exc:symmetric-alternating-four-characters>

#exercise[
  Let $H <= G$. Prove that if $M$ is a simple $K G$-module, then $M|L^G$ for
  some simple $K H$-module $L$. (Here, as usual, $M|L^G$ means that $M$ is
  isomorphic to a direct summand of $L^G$.) Apply this result to show that for
  every $zeta in Irr_K G$, $deg zeta <= |G:A|$, where $A$ is an arbitrary
  abelian subgroup of $G$.
] <exc:character-degree-abelian-index>

#exercise[
  Let $H <= G$, and let $L$ be the $K H$-module $K$, on which $H$ acts in some
  way (in other words $L$ affords a _linear representation_#idx(
    "linear representation",
  ) of $H$). Call $L^G$ a _monomial representation_#idx(
    "monomial representation",
  )
  #source(279)
  of $G$. Prove that for each subgroup $S$ of $G$, $(L^G)_S$ is a direct sum of
  monomial representations of $S$.
] <exc:monomial-restriction>

From this point on, $R$ denotes a commutative ring, and $H$ a subgroup of $G$.

#exercise[
  For an $R G$-module $M$, show that the $G$-trivial submodule of $M$ is
  $R$-isomorphic to $Hom_(R G) lr((R,M))$, where $G$ acts trivially on $R$.
] <exc:invariants-hom-trivial>

#exercise[
  (D. G. Higman @bib:Higman1955a). Let $H <= G$, and let $L$ be a left
  $R H$-module. Consider a left $R G$-module $i(L)$ with the following
  properties:
  #enum(
    numbering: "(i)",
    [There exists an $R H$-homomorphism $lambda: L -> i(L)$ such that $i(L)$ is
      generated over $R G$ by $lambda(L)$;],
    [For each $R H$-homomorphism $mu: L -> M_H$ from $L$ into $M_H$, where $M$
      is any $R G$-module, there exists a homomorphism of $R G$-modules
      $hat(mu): i(L) -> M$ such that $hat(mu)lambda=mu$.],
  )
  Prove that $lambda$ is a monomorphism, and that $i(L) tilde.equiv L^G$ as
  $R G$-modules.
  #hint([@exc:induction-universal-property])[
    Prove that any two modules $i(L)$ and $i'(L)$ satisfying conditions (i) and
    (ii) are $R G$-isomorphic. Then show that $L^G$ satisfies these conditions,
    where $lambda: L -> L^G$ is the homomorphism $L -> 1 times.o L$.
  ]
] <exc:induction-universal-property>

#exercise[
  (Mackey @bib:Mackey1951). Keep the notation of the preceding exercise. Show
  that $Hom_(R H) lr((R G,L))$ becomes a left $R G$-module if we define
  $ (x f)(y)=f(y x), x,y in G, f in Hom_(R H) lr((R G,L)). $
  Define a map $lambda: L -> Hom_(R H) lr((R G,L))$ by setting $lambda(l)=f_l$,
  $l in L$, where $f_l$ is the element of $Hom_(R H) lr((R G,L))$ such that
  $f_l lr((1))=l$ and $f_l lr((g))=0$ for $g in.not H$. Prove that $lambda$
  satisfies conditions (i) and (ii) of Exercise
  @exc:induction-universal-property, and hence that
  $Hom_(R H) lr((R G,L)) tilde.equiv L^G$ as $R G$-modules.
] <exc:coinduction-induction>

#exercise[
  Let $M$ be a left $R G$-module which is $R$-free on $r$ generators. Then the
  inner tensor product $R G times.o_R M$ is $R G$-free on $r$ generators.
  #hint([@exc:regular-inner-tensor-free])[
    Apply @cor:induction-tensor-identity, with $L=1_H$, $H={1}$, $L^G=R G$ (see
    Exercise @exc:regular-induced-trivial). Then we have
    $
      R G times.o M tilde.equiv 1_H^G times.o M tilde.equiv (1_H times.o M_H)^G
    $
    by @cor:induction-tensor-identity, since the inner tensor product is a
    commutative operation. Then $1_H times.o M_H$ is a direct sum of $r$ copies
    of $1_H$, and the result follows from @eq:tensor-direct-sums.
  ]
] <exc:regular-inner-tensor-free>

#exercise[
  Let $M$ be a left $R G$-lattice. Prove that the inner tensor product
  $R G times.o_R M$ is $R G$-projective.
  #hint([@exc:regular-inner-tensor-projective])[
    Let $M'$ be a $G$-trivial $R$-module such that $M product.co M'$ is
    $R$-free. Then use the preceding exercise to show that
    $R G times.o (M product.co M')$ is $R G$-free.
  ]
] <exc:regular-inner-tensor-projective>

#exercise[
  Given an exact sequence $L -> M -> N$ of $R H$-modules, show that the sequence
  of $R G$-modules $L^G -> M^G -> N^G$ is also exact.
  #source(280)
  #hint([@exc:induction-exact])[
    $R G$ is $R H$-free, hence flat as $R H$-module.
  ]
] <exc:induction-exact>

#exercise[
  Let $L,M$ be left $R G$-lattices. Prove that
  $ (L times.o_R M)^* tilde.equiv L^* times.o_R M^* $
  as $R G$-modules, where $L^*$ is the contragredient of $L$, and $M^*$ that of
  $M$.
] <exc:contragredient-tensor-product>

#exercise[
  Let $L,M$ and $N$ be left $R G$-lattices, and let $L^*$, $M^*$ and $N^*$ be
  their contragredients.
  #enum(
    numbering: "(i)",
    [Show that if
      $ (xi) quad 0 -> L -> M -> N -> 0 $
      is an exact sequence of left $R G$-lattices, then so is
      $ (xi^*) quad 0 -> N^* -> M^* -> L^* -> 0. $],
    [Deduce from the above that the sequence $(xi)$ is exact if and only if the
      sequence $(xi^*)$ is exact.],
    [Show that $(xi)$ is split if and only if $(xi^*)$ is split.],
  )
  #hint([@exc:contragredient-exact-split])[
    Use the fact that $Hom_R lr((-,R))$ preserves exactness of exact sequences
    of $R$-lattices, and that $L^(**) tilde.equiv L$ as $R G$-lattices.
  ]
] <exc:contragredient-exact-split>

#exercise[
  Show that the group algebra $E G$ of a finite group $G$ over an arbitrary
  field $E$ is injective (as left $E G$-module). #hint(
    [@exc:group-algebra-injective],
  )[
    By @prop:finitely-generated-injective-criterion, $E G$ is injective if and
    only if each exact sequence
    $ 0 -> E G -> X -> Y -> 0, $
    with $X,Y$ f.g. $E G$-modules, is split. But $X$ and $Y$ are $E G$-lattices,
    since $E$ is a field. Then $0 -> Y^* -> X^* -> (E G)^* -> 0$ is exact, and
    $(E G)^* tilde.equiv E G$, by @cor:group-ring-self-contragredient.
  ] (See §@ss:frobenius-symmetric-algebras and §@ss:relative-projectivity for
  other proofs.)
] <exc:group-algebra-injective>

#exercise[
  Deduce from the preceding exercise that if $E$ is a field, then every f.g.
  projective $E G$-module is injective.
] <exc:group-algebra-projective-injective>

#exercise[
  Returning to modules over a commutative ring $R$, show that any exact sequence
  $ 0 -> R G -> X -> Y -> 0, $
  in which $X$ and $Y$ are $R G$-lattices, is $R G$-split. Hence
  $op("Ext")_(R G)^1 lr((Y,R G))=0$ for each $R G$-lattice $Y$. Deduce that each
  sequence of $R G$-lattices
  $ 0 -> M -> X -> Y -> 0 $
  in which $M$ is $R G$-projective, necessarily splits.
  #hint([@exc:lattice-extension-projective-splits])[
    Imitate the proof of Exercise @exc:group-algebra-injective. Further
    $M|(R G)^((n))$ for some $n$, so $op("Ext")_(R G)^1 lr((Y,M))$ is a summand
    of $op("Ext")_(R G)^1 lr((Y,R G^((n))))$.
  ]
] <exc:lattice-extension-projective-splits>

#source(281)
#exercise[
  Show that every $R G$-lattice can be embedded in a free $R G$-module on a
  finite number of generators.
  #hint([@exc:lattice-embeds-free])[
    For a left $R G$-lattice $L$, let $L^*$ be its contragredient. Then
    $(R G)^((n))$ maps onto $L^*$, for some $n$. Now use Exercise
    @exc:contragredient-exact-split and @cor:group-ring-self-contragredient.
  ]
] <exc:lattice-embeds-free>

#exercise[
  Show that every injective $R G$-lattice $M$ is $R G$-projective.
  #hint([@exc:injective-lattice-projective])[
    By Exercise @exc:lattice-embeds-free, $M$ can be embedded in $(R G)^((n))$
    for some $n$, so $M|(R G)^((n))$.
  ]
] <exc:injective-lattice-projective>
