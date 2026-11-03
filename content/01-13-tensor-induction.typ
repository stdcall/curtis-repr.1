#import "main-defs.typ": *
#import "statements.typ": *

== Tensor Induction and Transfer <sec:tensor-induction-transfer>

#source(353)
Let $H$ be a subgroup of a finite group $G$, and let $R$ be an arbitrary
commutative ring. For each left $R H$-module $L$, we have defined an _induced_
$R G$-module
$
  op("ind")_H^G lr((L))=R G times.o_(R H) L
  =plus.o.big_(i=1)^n (g_i times.o L),
$
where $G=union.big_(i=1)^n g_i H$, $|G:H|=n$. Let $G slash H$ denote the set of
left cosets ${g_i H}$ of $H$ in $G$, so the elements ${g_i}$ are a set of coset
representatives. The action of an element $x in G$ on $op("ind")_H^G lr((L))$
involves a permutation action of $x$ on the summands ${g_i times.o L}$, as well
as the action of $H$ on $L$. It turns out (see
@eq:elementary-tensor-induced-modules) that there is a family of $R G$-modules
which can be constructed from the $R$-modules ${g_i times.o L}$ by using this
permutation action of $G$ on the summands. These $R G$-modules correspond to the
elementary symmetric functions of ${g_i times.o L}$, with
$op("ind")_H^G lr((L))$ corresponding to the elementary symmetric function
$sum X_i$ (see §@ss:adams-operators-virtual-characters). The $R G$-module
associated with the elementary symmetric function $product X_i$ has been studied
extensively (Dress~@bib:Dress1971, Berger~@bib:Berger1977,
Evens~@bib:Evens1963), and is called the _tensor induced module_. We shall
denote it by $times.o op("ind")_H^G lr((L))$, or briefly by $L^(times.o G)$ when
there is no danger of confusion. This section contains an introduction to tensor
induction, and its connections with the group-theoretical transfer map.
Relations between this transfer map and character theory are presented in
§@ss:transfer-determinant-map.

=== Tensor Induction <ss:tensor-induction>

Let us begin with a close study of the permutation action of $G$ on the set
$G slash H$ of left cosets of $H$ in $G$. Let $H$ be any multiplicative group,
and let $H^n=H times dots.c times H$ be the direct product of $n$ copies of $H$.
Let $S_n$ be the symmetric group acting on ${1,dots,n}$. Then $S_n$ acts on
$H^n$ as a group of automorphisms, by means of the formula
$
  pi:(h_1,dots,h_n) -> (h_(pi^(-1)(1)),dots,h_(pi^(-1)(n))),
  h_i in H,pi in S_n.
$
Thus, $pi$ moves the element $h_i$ from the $i$-th place to the $pi(i)$-th
place, for each $i$. We may therefore view $pi$ as a permutation of the places
${①,dots,ⓝ}$ occurring in these $n$-tuples from $H$. Let us now form the
semidirect product $H^n times.r S_n$, in which each $pi in S_n$ acts by
conjugation on $H^n$:
$ pi(h_1, dots, h_n)pi^(-1)=(h_(pi^(-1)(1)),dots,h_(pi^(-1)(n))). $
<eq:wreath-product-conjugation>
The group $H^n times.r S_n$ is often called the _wreath product_
$H wreath S_n$.#idx("wreath product")

#source(354)
Now let $H$ be a subgroup of $G$, $|G:H|=n$, and let $G=union_(i=1)^n g_i H$.
For $x in G$, we have
$ x g_i=g_(pi(i)) h_i,quad h_i in H,1 <= i <= n. $
<eq:coset-permutation-components>
The permutation $pi in S_n$ and the elements $h_i in H$ are uniquely determined
by $x$.

#lemma[
  Define a map $phi:G -> H^n times.r S_n$ by setting
  $ phi(x)=pi(h_1, dots, h_n),x in G, $
  the product of $pi$ and the element $(h_1,dots,h_n)$ in $H^n times.r S_n$,
  where $pi$ and the elements $h_i in H$ are given by
  @eq:coset-permutation-components. Then $phi$ is a monomorphism of groups, and
  $phi$ depends on the choice of the coset representatives ${g_i}$. If ${g'_i}$
  is another set of representatives of $G slash H$, then we have
  $ g'_i=g_(lambda(i)) h'_i,quad h'_i in H,1 <= i <= n, $
  for some $lambda in S_n$. The corresponding map $phi':G -> H^n times.r S_n$
  satisfies
  $ phi'(x)=s^(-1)phi(x)s,x in G, $
  where $s=lambda(h'_1, dots, h'_n)$ in $H^n times.r S_n$.
] <lem:coset-wreath-embedding>
#proof[
  Given $x in G$, let $phi(x)$ be defined as above. Let $y in G$, and set
  $y g_i=g_(sigma(i)) k_i$ for $1 <= i <= n$, with $sigma in S_n$ and
  $k_i in H$, according to @eq:coset-permutation-components. Then
  $
    (x y)g_i=x g_(sigma(i)) k_i
    =g_(pi sigma(i)) h_(sigma(i)) k_i,1 <= i <= n,
  $
  so
  $
    phi(x y) & =pi sigma(h_(sigma(1)) k_1, dots, h_(sigma(n)) k_n) \
             & =pi sigma(h_(sigma(1)), dots, h_(sigma(n)))
               sigma^(-1)sigma(k_1, dots, k_n) \
             & =pi(h_1, dots, h_n)sigma(k_1, dots, k_n)=phi(x)phi(y),
  $
  using @eq:wreath-product-conjugation. The map $phi$ is injective because,
  given only $pi(1)$ and $h_1$, $x$ is determined uniquely by
  @eq:coset-permutation-components.

  The proof of the second part of the lemma, on the conjugacy of $phi(G)$ and
  $phi'(G)$ in $H^n times.r S_n$, is left as an exercise.
]

We now apply these considerations to the construction of tensor induced modules.
Keeping the preceding notation, let $L$ be a left $R H$-module for some
#source(355)
commutative ring $R$. Let
$ times.o^n L=L times.o dots.c times.o L quad (n "factors"), $
where $times.o$ means $times.o_R$, as in §@sec:tensor-algebras. Then
$times.o^n L$ is a left $R(H^n)$-module, with the action of
$(h_1,dots,h_n) in H^n$ on $l_1 times.o dots.c times.o l_n in times.o^n L$ given
by
$
  (h_1,dots,h_n)(l_1 times.o dots.c times.o l_n)
  =h_1 l_1 times.o dots.c times.o h_n l_n.
$
(For $n=2$, this module is simply $L \# L$, the outer tensor product defined in
@def:outer-inner-tensor-products.) The symmetric group $S_n$ acts on
$times.o^n L$ as a group of symmetry operators (see
§@ss:tensor-symmetric-exterior-algebras), with the action of $pi in S_n$ on
$l_1 times.o dots.c times.o l_n in times.o^n L$ given by
$
  pi(l_1 times.o dots.c times.o l_n)
  =l_(pi^(-1)(1)) times.o dots.c times.o l_(pi^(-1)(n)).
$
We now show that the combined actions of $S_n$ and $H^n$ on $times.o^n L$ give
$times.o^n L$ the structure of a left $R(H^n times.r S_n)$-module. For this, it
is sufficient to check that both sides of @eq:wreath-product-conjugation act in
the same way on each $l_1 times.o dots.c times.o l_n in times.o^n L$. We have
$
  pi(h_1, dots, h_n)pi^(-1)(l_1 times.o dots.c times.o l_n)
  &=pi(h_1, dots, h_n){l_(pi(1)) times.o dots.c times.o l_(pi(n))} \
  &=pi(h_1 l_(pi(1)) times.o dots.c times.o h_n l_(pi(n))) \
  &=h_(pi^(-1)(1)) l_1 times.o dots.c times.o h_(pi^(-1)(n)) l_n,
$
as required.

Now let $phi:G -> H^n times.r S_n$ be a monomorphism of groups, defined as in
Lemma~@lem:coset-wreath-embedding relative to some set of coset representatives
${g_i}$ of $G slash H$. We may use $phi$ to give $times.o^n L$ the structure of
a left $R G$-module. The action of $x in G$ on $l_1 times.o dots.c times.o l_n$
is then given by
$
  x(l_1 times.o dots.c times.o l_n)
  &=pi(h_1, dots, h_n)(l_1 times.o dots.c times.o l_n) \
  &=h_(pi^(-1)(1)) l_(pi^(-1)(1)) times.o dots.c times.o
  h_(pi^(-1)(n)) l_(pi^(-1)(n)),
$ <eq:tensor-induced-action>
where $phi(x)=pi(h_1, dots, h_n)$ as in @lem:coset-wreath-embedding. It follows
from the second part of Lemma~@lem:coset-wreath-embedding that any two actions
of $G$ on $times.o^n L$, defined by use of two different sets of representatives
of $G slash H$, give rise to isomorphic $R G$-modules. The isomorphism is given
by the action of an element $s in H^n times.r S_n$ constructed as in
@lem:coset-wreath-embedding.

#definition[
  Let $H$ be a subgroup of $G$ of index $n$, and let $L$ be a left $R H$-module.
  The operation which assigns to $L$ the $R G$-module $times.o^n L$, with the
  action of $G$ given by @eq:tensor-induced-action, is called _tensor
  induction_,#idx("tensor induction")#idx("induction") and will be denoted by
  $ L -> times.o op("ind")_H^G lr((L)), $
  or simply by
  $ L -> L^(times.o G). $
] <def:tensor-induction>

#source(356)
It is possible to give a somewhat more conceptual description of
$times.o op("ind")_H^G lr((L))$, using the theory of additive induced modules
from §@sec:induced-modules. For a set of representatives ${g_i}$ of $G slash H$,
we have a corresponding set of $R$-submodules ${g_i times.o L}_(1 <= i <= n)$ of
$op("ind")_H^G lr((L))=R G times.o_(R H) L$, and $op("ind")_H^G lr((L))$ is
their direct sum. We may instead form the tensor product
$times.o.big_(i=1)^n (g_i times.o L)$ over $R$, and let $G$ act diagonally on
this $R$-module by the formula
$
  x((g_1 times.o l_1) times.o dots.c times.o (g_n times.o l_n))
  =(x g_1 times.o l_1) times.o dots.c times.o (x g_n times.o l_n),
  x in G,l_i in L.
$ <eq:diagonal-tensor-induced-action>
In order to view the right hand side as an element of
$times.o.big_(i=1)^n (g_i times.o L)$, it is necessary to identify
$
  times.o.big_(i=1)^n g_(pi(i)) times.o L quad "with" quad
  times.o.big_(i=1)^n g_i times.o L,
$
for all $pi in S_n$, using the $R$-isomorphism
$
  times.o.big_(i=1)^n (g_(pi(i)) times.o l_i) ->
  times.o.big_(i=1)^n g_i times.o l_(pi^(-1)(i)).
$
We then use @eq:coset-permutation-components to calculate the right hand side of
@eq:diagonal-tensor-induced-action, and obtain
$
  (x g_1 times.o l_1) times.o dots.c times.o (x g_n times.o l_n)
  &=(g_(pi(1)) h_1 times.o l_1) times.o dots.c times.o
  (g_(pi(n)) h_n times.o l_n) \
  &=(g_(pi(1)) times.o h_1 l_1) times.o dots.c times.o
  (g_(pi(n)) times.o h_n l_n) \
  &=(g_1 times.o h_(pi^(-1)(1)) l_(pi^(-1)(1))) times.o dots.c times.o
  (g_n times.o h_(pi^(-1)(n)) l_(pi^(-1)(n))).
$
Comparing this result with @eq:tensor-induced-action, we have

#proposition[
  Let $L$ be an $R H$-module, and ${g_i}_(1 <= i <= n)$ a set of representatives
  of $G slash H$. Then the tensor product of $R$-modules
  $times.o.big_(i=1)^n (g_i times.o L)$, with diagonal action of $G$ defined by
  @eq:diagonal-tensor-induced-action, is an $R G$-module. There is an
  isomorphism of $R G$-modules
  $
    times.o.big_(i=1)^n (g_i times.o L)
    tilde.equiv times.o op("ind")_H^G lr((L)),
  $
  given by
  $
    times.o.big_(i=1)^n (g_i times.o l_i) in
    times.o.big_(i=1)^n (g_i times.o L) -> times.o.big_(i=1)^n l_i
    in times.o^n L.
  $
] <prop:tensor-induction-diagonal-model>

#source(357)
The previous discussion of $times.o^n L$ as an $R(H^n times.r S_n)$-module shows
that $times.o.big_(i=1)^n (g_i times.o L)$ is independent (up to
$R G$-isomorphism) of the choice of coset representatives ${g_i}_(1 <= i <= n)$.

#remark(numbered: false)[
  The preceding discussion can be generalized to yield a family of $R G$-modules
  $s_k lr((L))$, $1 <= k <= n$. By definition,
  $
    s_k lr((L))=product.co_(1 <= i_1 < i_2 < dots.c < i_k <= n)
    (g_(i_1) times.o L) times.o_R dots.c times.o_R (g_(i_k) times.o L),
  $
  <eq:elementary-tensor-induced-modules>
  with diagonal action of $g$ as in @eq:diagonal-tensor-induced-action. Thus
  $
    s_1 lr((L)) tilde.equiv op("ind")_H^G lr((L)),quad
    s_n lr((L)) tilde.equiv times.o op("ind")_H^G lr((L)).
  $
  This collection of $R G$-modules ${s_k lr((L)):1 <= k <= n}$ has properties
  analogous to those of the elementary symmetric functions.
]

We return to the consideration of $times.o op("ind")_H^G lr((L))$, which we
abbreviate as $L^(times.o G)$ as in @def:tensor-induction. The next result shows
that $L -> L^(times.o G)$ is multiplicative, in the same sense that $L -> L^G$
is additive (see @prop:induction-transitive).

#proposition[
  Let $L$ and $M$ be left $R H$-modules. Then
  $
    (L times.o M)^(times.o G) tilde.equiv
    L^(times.o G) times.o M^(times.o G),
  $
  where $L times.o M$ denotes the inner tensor product of $R H$-modules, and
  $L^(times.o G) times.o M^(times.o G)$ denotes the inner tensor product of
  $R G$-modules.
] <prop:tensor-induction-multiplicative>
#proof[
  Letting $n=|G:H|$ as usual, it is sufficient to verify that the inner tensor
  product $(times.o^n L) times.o (times.o^n M)$ of $R(H^n times.r S_n)$-modules
  is isomorphic to the $R(H^n times.r S_n)$-module
  $times.o^n lr((L times.o M))$, where $L times.o M$ is the inner tensor product
  of $R H$-modules. We leave it to the reader to check that the $R$-isomorphism
  from $times.o^n lr((L times.o M))$ to $(times.o^n L) times.o (times.o^n M)$,
  given by
  $
    (l_1 times.o m_1) times.o dots.c times.o (l_n times.o m_n)
    ->(l_1 times.o dots.c times.o l_n) times.o
    (m_1 times.o dots.c times.o m_n),quad l_i in L,m_i in M,
  $
  is the required $R(H^n times.r S_n)$-isomorphism.
]

We conclude this section with the computation of the representation afforded by
the tensor induced module $L^(times.o G)$ in the simplest case, that in which
$L$ affords a linear representation $lambda:H -> R^dot$. In order to obtain the
result, we shall need the group-theoretic _transfer map_
$ V_H^G:G slash G' -> H slash H', $ <eq:transfer-domain>
#idx("transfer")
where $G slash G'$ is the commutator factor group of $G$, and $H slash H'$ that
of $H$.

#source(358)
Let $H <= G$, $|G:H|=n$, $G=union g_i H$ as above. For $x in G$, write
$ x g_i=g_(pi(i)) h_i,quad h_i in H,1 <= i <= n, $
as in @eq:coset-permutation-components. We now define
$
  v(x)="image of" product_(i=1)^n h_i quad "in" H slash H',
  "for" x in G.
$
For $y in G$, let us write $y g_i=g_(sigma(i)) k_i$, $k_i in H$, as in the proof
of @lem:coset-wreath-embedding. Then since $H slash H'$ is abelian, we obtain
$
  v(x y)={product_(i=1)^n h_(sigma(i)) k_i}H'
  ={product h_i}{product k_i}H'=v(x)v(y).
$
Thus $v$ is a homomorphism from $G$ into $H slash H'$. If the set of coset
representatives ${g_i}$ is replaced by another set ${g'_i}$, where
$ g'_i=g_(tau(i)) z_i,quad z_i in H,1 <= i <= n, $
for some $tau in S_n$, then it is easily checked that for $x in G$,
$
  x g'_i=g'_(tau^(-1)pi tau(i)) h'_i,
  "where" h'_i=z_(tau^(-1)pi tau(i))^(-1) h_(tau(i)) z_i,1 <= i <= n.
$
It follows at once that $product_1^n h_i$ and $product_1^n h'_i$ have the same
image in $H slash H'$, so the map $v$ is independent of the choice of coset
representatives of $G slash H$. Because $H slash H'$ is abelian, we thus obtain
a well defined homomorphism @eq:transfer-domain, given by
$ V_H^G lr((x G'))={product_(i=1)^n h_i}H',x in G, $
<eq:transfer-coset-formula>
where the ${h_i}$ are determined from $x$ by @eq:coset-permutation-components.
The homomorphism $V_H^G$ is called the _transfer map_ (or _Verlagerung_) from
$G slash G'$ to $H slash H'$.#idx("transfer")

(The transfer map can also be defined by using the Tate cohomology groups
$hat(H)^i lr((G,ZZ))$ introduced in §@ss:tate-cohomology. The inclusion $H <= G$
induces a homomorphism
$ hat(H)^(-2) lr((G,ZZ)) -> hat(H)^(-2) lr((H,ZZ)). $
On the other hand,
$
  hat(H)^(-2) lr((G,ZZ)) tilde.equiv G slash G',quad
  hat(H)^(-2) lr((H,ZZ)) tilde.equiv H slash H',
$
by @eq:tate-abelianization. It can be shown that the resulting homomorphism from
$G slash G'$ to
#source(359)
$H slash H'$ coincides with the transfer $V_H^G$ defined above. See
Weiss~@bib:Weiss1969, p.~116 for details.)

For applications of transfer to group theory, see
Gorenstein~@bib:Gorenstein1968, Chapter~7 or Huppert~@bib:Huppert1967,
Chapter~IV. In §@ss:transfer-determinant-map, we shall follow Gallagher's
approach @bib:Gallagher1965 to the connection between transfer and induction and
restriction of characters. Here, we shall content ourselves with using the
transfer map to compute the character of a tensor induced module $L^(times.o G)$
in the case where the original $R H$-module $L$ affords a linear representation
$lambda:H -> R^dot$. (As usual, $R^dot="units of" R$.) Thus, we start with an
$R H$-module $L$ having an $R$-basis consisting of a single element $l$, with
the action of $H$ on $L$ given by
$ h l=lambda(h)l,h in H. $
Then $L^(times.o G)$ is also a free $R$-module with a single basis element $m$,
where
$ m=times.o.big_(i=1)^n (g_i times.o l), $
and $G=union g_i H$. Let $x in G$, and use @eq:coset-permutation-components and
@eq:diagonal-tensor-induced-action to obtain
$
  x m & =times.o.big_(i=1)^n (x g_i times.o l)
        =times.o.big_(i=1)^n g_(pi(i)) times.o h_i l \
      & =times.o.big_(i=1)^n g_i times.o h_(pi^(-1)(i)) l
        ={lambda(product_(i=1)^n h_i)}m.
$
(We have used the commutativity of the ring $R$.) But $H' <= ker lambda$, so
$lambda$ is well defined on $H slash H'$. Since $V_H^G lr((x))=(product h_i)H'$
by @eq:transfer-coset-formula, we obtain

#proposition[
  Let $lambda:H -> R^dot$ be a linear $R$-representation of $H$, afforded by an
  $R H$-module $L$ which is $R$-free on one generator. Then $L^(times.o G)$ is
  an $R G$-module which is $R$-free on one generator, and $L^(times.o G)$
  affords the linear representation $lambda^(times.o G)$ of $G$ given by
  $ lambda^(times.o G)(x)=lambda(V_H^G lr((x))),x in G. $
] <prop:linear-tensor-induction-transfer>

=== Transfer and the Determinant Map <ss:transfer-determinant-map>

We continue to study the permutation action of $G$ on $G slash H$, and its
connection with character theory. Here we prove some results of
Gallagher~@bib:Gallagher1965 which relate the transfer map @eq:transfer-domain
to the determinants of representations of finite groups. Another application of
the determinant map, also due to Gallagher, appears in
§@ss:extensions-invariant-characters.

In this subsection, all representations and character are taken in the complex
field $CC$.

#source(360)
Let $G$ be a finite group, and $M$ a left $CC G$-module, affording a matrix
representation $upright(bold(M))$ with character $mu$. The multiplication
theorem for determinants shows that the map $x -> det upright(bold(M))(x)$,
$x in G$, is a linear representation of $G$, which depends only on the
isomorphism class of $M$. We denote the character of the representation
$x -> det upright(bold(M))(x)$ by $det mu$, since $mu$ determines $M$ up to
isomorphism. Then by definition,
$ (det mu)(x)=det upright(bold(M))(x),x in G. $
#idx("determinant map")
If $mu$ and $nu$ are $CC$-characters of $G$, then we have:
$
  cases(
    det(mu+nu)=(det mu)(det nu),
    det(mu nu)=(det mu)^(nu(1))(det nu)^(mu(1)).
  )
$ <eq:character-determinant-identities>
The proofs of these formulas are left as exercises for the reader; they depend
on the fact that the determinant of a matrix is the product of its eigenvalues.

Now let $H$ be a subgroup of $G$, $n=|G:H|$, and let $G=union_(i=1)^n g_i H$ as
in §@ss:tensor-induction. Set
$ x g_i=g_(pi(i)) h_i,pi in S_n,h_i in H,1 <= i <= n, $
as in @eq:coset-permutation-components, and note that this formula can be
rewritten as
$ g_(pi(i))^(-1) x g_i=h_i,1 <= i <= n. $
<eq:coset-component-conjugation>
Let $epsilon_(G -> H) lr((x))$ denote the sign of the permutation $pi$. The map
$x -> pi$ is the permutation representation of $G$ on the left cosets
$G slash H$, and if $upright(bold(P))(x)$ is the permutation matrix
corresponding to $pi$, then $epsilon_(G -> H) lr((x))=det upright(bold(P))(x)$,
$x in G$.

#proposition[
  Let $H <= G$, and let $V_H^G$ be the transfer map.
  #enum(
    numbering: "(i)",
    [If $lambda$ is a $CC$-character of $H$, then
      $
        det lambda^G={epsilon_(G -> H)^(lambda(1))}
        {(det lambda) compose V_H^G},
      $
      that is,
      $
        (det lambda^G)(x)={epsilon_(G -> H)^(lambda(1)) lr((x))}
        {(det lambda)(V_H^G x)} quad "for all" x in G.
      $],
    [If $zeta$ is a $CC$-character of $G$, then
      $ (det zeta)^(|G:H|)=(det zeta_H) compose V_H^G. $],
  )
] <prop:induced-character-determinant-transfer>
#proof[
  Let $upright(bold(L))$ be a matrix representation of $H$ affording $lambda$,
  and let $d=deg lambda$. Changing the notation of @eq:induced-matrix slightly
  in order to conform to @eq:coset-component-conjugation, we can
  #source(361)
  express $upright(bold(L))^G lr((x))$ as a matrix of $d times d$ blocks:
  $
    upright(bold(L))^G lr((x))=(dot(upright(bold(L))) lr(
        (g_j^(-1) x
          g_i)
      )),x in G,
  $
  where the $j$-th row of blocks of the matrix $upright(bold(L))^G lr((x))$ is
  $
    (dot(upright(bold(L))) lr((g_j^(-1) x g_1)),dots,
      dot(upright(bold(L))) lr((g_j^(-1) x g_n))).
  $
  Using this fact and @eq:coset-component-conjugation, it is easily checked that
  we have a factorization
  $
    upright(bold(L))^G lr((x))=(dot(upright(bold(I)))_d lr(
        (g_j^(-1)
          x g_i)
      )) dot
    "diag"(upright(bold(L))(h_1),dots,upright(bold(L))(h_n)),
  $
  <eq:induced-matrix-determinant-factorization>
  where for $h in H$, $upright(bold(I))_d lr((h))=upright(bold(I))_d=d times d$
  identity matrix, and where $dot(upright(bold(I)))_d$ denotes the extension of
  $upright(bold(I))_d$ from $H$ to $G$ as in §@ss:induction-frobenius. Taking
  determinants in @eq:induced-matrix-determinant-factorization, we obtain
  $
    det upright(bold(L))^G lr((x))=det(
      dot(upright(bold(I)))_d
      lr((g_j^(-1) x g_i))
    ) dot
    product_(i=1)^n det upright(bold(L))(h_i).
  $
  Now $det upright(bold(L))$ is a representation of $H slash H'$, so by
  @eq:transfer-coset-formula the second factor on the right becomes
  $
    product_(i=1)^n det upright(bold(L))(h_i)
    =(det upright(bold(L)))(product_(i=1)^n h_i)=(det
      upright(bold(L)))(V_H^G x).
  $
  In order to compute the first factor
  $det(dot(upright(bold(I)))_d lr((g_j^(-1) x g_i)))$, we note that if
  $upright(bold(I))_d^G$ denotes $op("ind")_H^G upright(bold(I))_d$, then
  $upright(bold(I))_d^G lr((x))=(dot(upright(bold(I)))_d lr((g_j^(-1) x g_i)))$
  for $x in G$. Letting $upright(bold(P))(x)$ be the permutation matrix
  corresponding to $pi$ in @eq:coset-component-conjugation, we have
  $
    upright(bold(I))_d^G lr((x))=upright(bold(P))(x) times.o
    upright(bold(I))_d,x in G,
  $
  where $upright(bold(I))_d$ is the $d$-rowed identity matrix. Then
  $
    det upright(bold(I))_d^G lr((x))={det upright(bold(P))(x)}^d
    =epsilon_(G -> H)^(lambda(1)) lr((x)),
  $
  by the definition of $epsilon_(G -> H)$. Combining our results, we have proved
  part (i) of the proposition.

  For the proof of (ii), we first observe that
  $ zeta_H^G=(1_H^G)zeta. $
  Using this fact and @eq:character-determinant-identities, we obtain, after
  substituting $zeta_H$ for $lambda$ in part (i),
  $
    (det 1_H^G)^(zeta(1)) dot (det zeta)^(|G:H|)
    ={epsilon_(G -> H)^(zeta(1))}{(det zeta_H) compose V_H^G}.
  $
  #source(362)
  Since $(det 1_H^G)^(zeta(1))=epsilon_(G -> H)^(zeta(1))$, we may cancel this
  factor, and obtain part (ii) of the proposition.
]

#corollary[
  Let $E <= H <= G$. Then
  $
    epsilon_(G -> E)={epsilon_(G -> H)^(|H:E|)}
    {epsilon_(H -> E) compose V_H^G}.
  $
] <cor:permutation-sign-transitivity>
#proof[
  We have $det(1_E^H)=epsilon_(H -> E)$, and
  $ det(1_E^H)^G=det 1_E^G=epsilon_(G -> E), $
  by transitivity of induction. Applying
  Proposition~@prop:induced-character-determinant-transfer(i) to $1_E^H$, we
  obtain
  $
    epsilon_(G -> E)={epsilon_(G -> H)^(|H:E|)}
    {epsilon_(H -> E) compose V_H^G},
  $
  as required.
]

We conclude this section with some remarks, without complete proofs, on
refinements of these results in case $H$ is a normal subgroup of $G$. For
details, see Gallagher~@bib:Gallagher1965.

Let $N$ be a normal subgroup of $G$, and let $x in G$ be such that the coset
$x N$ has order $d$ in the factor group $F=G slash N$. In the permutation action
of $G$ on the cosets $G slash N$, the element $x$ is therefore represented by a
product of disjoint cycles, each of length $d$. It follows that
$
  epsilon_(G -> N) lr((x))=(-1)^((d-1)(|F| slash d))
  =(-1)^(|F|-|F| slash d).
$
Consequently $epsilon_(G -> N) lr((x))=1$ unless $|F|$ is even and $|F| slash d$
is odd. The latter case can occur only if a Sylow $2$-subgroup $S$ of $F$ is
contained in the cyclic group $⟨ overline(x) ⟩$ generated by the image
$overline(x)$ of $x$ in $F$. Thus $epsilon_(G -> N)=1_G$ unless the Sylow
$2$-subgroups of $F$ are cyclic and non-trivial, and in that case
$epsilon_(G -> N) != 1$.

In the latter situation, in which a Sylow $2$-subgroup $S$ of $F$ is cyclic of
order $2^a$, where $a>0$, the automorphism group of $S$ has order
$phi(2^a)=2^(a-1)$. It follows that $N_F lr((S)) slash C_F lr((S))$ has odd
order dividing $2^(a-1)$, hence $N_F lr((S))=C_F lr((S))$. By a theorem of
Burnside (see §@ss:normal-p-complements-transfer), it follows that $F$ has a
normal $2$-complement. It is also possible to prove this directly, as follows.
Let $F_epsilon$ be the kernel of $epsilon_(G -> N)$ in $F$. Then
$F_epsilon < F$, and by induction $F_epsilon$ has a normal $2$-complement $H$,
which is#footnote[$O_(2') lr((F_epsilon))$ denotes the maximal normal
  $2'$-subgroup of $F_epsilon$.] $O_(2') lr((F_epsilon))$, and hence
characteristic in $F_epsilon$. Then $H$ is normal in $F$, and is the required
normal $2$-complement. From these considerations, we conclude that if
$epsilon_(G -> N) != 1$, then $epsilon_(G -> N)$ is the only nontrivial
homomorphism from $F=G slash N$ to ${plus.minus 1}$.

Returning to an arbitrary normal subgroup $N$, let $zeta in "Irr" G$,
$psi in "Irr" N$, and assume that $(zeta,psi^G)>0$. Let $T=G_psi$, the
stabilizer of $psi$ (see §@ss:clifford-character-theory); then by
#source(363)
@prop:clifford-character-restriction there exists $xi in "Irr" T$ such that
$ zeta=xi^G quad "and" quad xi|_N=a psi, $
for some positive integer $a$. The integer $a$ is the degree of an irreducible
projective representation of $T slash N$ by
@th:clifford-projective-factorization, so $a$ divides $|T:N|$ by
@prop:projective-character-degree. It follows that
$
  frac(psi^G lr((1)), zeta(1))
  =frac(|G:N|psi(1), a psi(1)|G:T|)=frac(|T:N|, a) in ZZ.
$
We can now state

#proposition[
  Let $N ⊴ G$, $zeta in "Irr" G$, $psi in "Irr" N$, and assume $(zeta,psi^G)>0$.
  Let $e$ be the integer $psi^G lr((1)) slash zeta(1)$. Then
  $
    (det zeta)^e={epsilon_(G -> N)^(e psi(1))}
    {(det psi) compose V_N^G}.
  $
] <prop:normal-constituent-determinant-transfer>

For finite groups, the Principal Ideal Theorem states that $V_(G')^G$ is trivial
(see Zassenhaus~@bib:Zassenhaus1949, Chapter~V, §4). Using this result and
@prop:normal-constituent-determinant-transfer, Gallagher proved:

#corollary[
  For each pair of irreducible characters $zeta$ of $G$ and $psi$ of $G'$ with
  $(zeta,psi^G)>0$, we have
  $ (det zeta)^f={epsilon_(G -> G')^(f psi(1))}, $
  where
  $ f=psi(1)|G:G'| slash zeta(1). $
] <cor:derived-subgroup-constituent-determinant>

=== Normal $p$-Complements and the Transfer <ss:normal-p-complements-transfer>

A finite group $G$ is said to have a _normal $p$-complement_,#idx(
  "normal p-complement",
) for some prime $p$, if $G$ has a normal subgroup $N$ whose order is the
$p'$-part of the order of $G$. In this situation, $N$ has order prime to $p$,
and index $|G:N|$ equal to a power of $p$. If $G$ has a normal $p$-complement,
then $G$ has a decomposition as a semidirect product, $G=N times.r S$, for any
Sylow $p$-subgroup $S$ of $G$ (compare with Theorem~@th:schur-zassenhaus). In
case $N$ is a normal $p$-complement in $G$, then $N$ coincides with
$O_(p') lr((G))$, the unique maximal normal subgroup of $G$ whose order is prime
to $p$. Therefore a normal $p$-complement is uniquely determined, if it exists.

Many theorems in finite group theory involve the existence of normal
$p$-complements. Following M. Hall~@bib:Hall1959, §14.3, we shall derive one of
the most important of these theorems, as an application of the transfer map
$V_H^G$ defined in §@ss:tensor-induction. Later, in
§@ss:normal-complement-criterion, we shall obtain a more general result, as an
application of the Brauer Induction Theorem (see
@th:hall-subgroup-normal-complement and @cor:burnside-normal-p-complement).

#source(364)
#theorem(name: "Burnside’s Transfer Theorem")[
  Let $S$ be a Sylow $p$-subgroup of a finite group $G$ such that $S$ is
  contained in the center of its normalizer. Then $G$ contains a normal
  $p$-complement.
] <th:burnside-normal-p-complement>
#idx("Burnside's Transfer Theorem", target: [@th:burnside-normal-p-complement])

We first require

#lemma[
  Let $X$ and $Y$ be subsets of a Sylow $p$-subgroup $S$ of $G$. If both $X$ and
  $Y$ are normalized by $S$ and are conjugate in $G$, then $X$ and $Y$ are
  conjugate in $N_G lr((S))$.
] <lem:sylow-normalizer-controls-fusion>
#proof[
  Let $X^u=Y$, for some $u in G$. Then $X^u$ is normalized by $S^u$, and both
  $S$ and $S^u$ are contained in the normalizer $N$ of $Y$. By Sylow's Theorem,
  $S$ and $S^u$ are conjugate in $N$, so $S^(u v)=S$ for some element $v$ such
  that $Y^v=Y$. Setting $z=u v$, we have $z in N_G lr((S))$, and
  $ X^z=X^(u v)=(X^u)^v=Y^v=Y, $
  as required.
]

#proof(head: emph[Proof of the Theorem.])[
  Since $S$ is in the center of $N_G lr((S))$, $S$ is abelian, and $S'=1$. We
  shall investigate the transfer map $V_S^G:G slash G' -> S$. By the discussion
  in §@ss:tensor-induction, formula @eq:transfer-coset-formula for $V_S^G$ is
  independent of the choice of coset representatives. Thus we may compute
  $V_S^G lr((u))$, for each $u in G$, by using coset representatives of
  $G slash S$ tailored to the element $u$. Given $u in G$, we may partition the
  cosets in $G slash S$ into orbits under the action of left multiplication by
  $⟨ u ⟩$. These orbits correspond to the decomposition of the permutation
  $ x S -> u x S,x in G, $
  as a product of disjoint cycles (see @bib:CurtisReiner1962[CR §1] for this
  approach to the cycle decomposition of a permutation). Letting
  ${x_i S}_(1 <= i <= m)$ be representatives of these orbits, we have as coset
  representatives of $G slash S$ the elements
  $ {u^j x_i:0 <= j <= d_i-1,1 <= i <= m}, $
  where $d_i$ is the length of the cycle corresponding to the orbit of $x_i S$
  under the action of $⟨ u ⟩$. The element $u$ acts on the coset representatives
  as follows:
  $ u dot u^j x_i=u^(j+1) x_i,quad 0 <= j <= d_i-1,1 <= i <= m, $
  and
  $ u dot u^(d_i-1) x_i=x_i s_i,quad "for some" s_i in S. $
  It follows (by @eq:transfer-coset-formula) that
  $
    V_S^G lr((u))=product_(i=1)^m s_i
    =product_(i=1)^m x_i^(-1) u^(d_i) x_i.
  $
  #source(365)
  In particular, for $u in S$, $u^(d_i)$ and $x_i^(-1) u^(d_i) x_i$ are both in
  $S$, and are normalized by $S$ and conjugate in $G$. By the preceding lemma,
  they are conjugate in $N_G lr((S))$. Since $S$ is contained in the center of
  $N_G lr((S))$, we have
  $ x_i^(-1) u^(d_i) x_i=u^(d_i),1 <= i <= m. $
  Consequently,
  $ V_S^G lr((u))=u^(|G:S|),u in S. $
  Since $|G:S|$ is prime to $p$, and $S$ is an abelian $p$-group, it follows
  that $V_S^G:G slash G' -> S$ is surjective, and the restriction of $V_S^G$ to
  $S G' slash G'$ is an isomorphism. The kernel $H$ of $V_S^G$ is therefore a
  subgroup of $G slash G'$ of index $|S|$. Therefore there exists a normal
  subgroup $N$ of $G$ of index $|S|$, and $N$ is the desired $p$-complement.
]

The above theorem provides a significant start towards the classification of
$2$-groups which can appear as Sylow $2$-subgroups of non-abelian simple group
(see §@ss:brauer-suzuki-generalized-quaternion for a continuation of this
project).

#corollary[
  A finite non-abelian group $G$ with a non-trivial cyclic Sylow $2$-subgroup
  must have a normal $2$-complement. Hence $G$ cannot be simple.
] <cor:cyclic-sylow-two-normal-complement>
#proof[
  Let $S$ be a Sylow $2$-subgroup of $G$, and assume $S$ is cyclic of order
  $2^a$, $a >= 1$. Then the automorphism group of $S$ has order
  $phi(2^a)=2^(a-1)$, where $phi$ is the Euler $phi$-function. Then
  $N_G lr((S)) slash C_G lr((S))$ has order dividing $2^(a-1)$. On the other
  hand, $N_G lr((S)) slash S$ has odd order, since $S$ is a Sylow $2$-subgroup
  by hypothesis, so its quotient $N_G lr((S)) slash C_G lr((S))$ has odd order
  as well. It follows that $N_G lr((S))$ acts trivially on $S$, and therefore
  $S$ is contained in the center of $N_G lr((S))$. But then $G$ has a normal
  $2$-complement by Burnside's Theorem, which completes the proof.
]

#exercise-heading

#exercise[
  Prove the analogue of the Mackey Subgroup Theorem for tensor induction. In
  other words, let $E$ and $H$ be subgroups of a finite group $G$, and let $M$
  be an $R H$-module. Then
  $
    (M^(times.o G))_E tilde.equiv
    times.o.big_g {(g times.o M)_(E_g)}^(times.o E),
  $
  where $G=union.dot E g H$, and $E_g=E inter attach(H, tl: g)$.
] <exc:tensor-induction-mackey-subgroup>
