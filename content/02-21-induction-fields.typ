#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/21-induction-fields.typ": *

== The Induction Theorem for Arbitrary Fields <sec:induction-arbitrary-fields>

Let $(K,R,k)$ be a $p$-modular system. The properties of the Cartan-Brauer
triangle
#induction-cartan-triangle()
were derived in §@sec:cartan-brauer-triangle under the assumption that $K$ is
sufficiently large relative to $G$. Several of these properties, for example,
the facts that the decomposition map $d$ is surjective, and that the determinant
of $c$ is a $p$-power, used the Brauer Induction Theorem and Brauer's criterion
for virtual characters. In this section we prove corresponding facts about the
triangle for an arbitrary $p$-modular system, without the hypothesis that $K$ be
large.

In order to accomplish this objective, we need an extension of the Brauer
Induction Theorem, due to Berman @bib:Berman1956a and Witt @bib:Witt1952 (see
@bib:CurtisReiner1962[CR §42] and Serre~@bib:Serre1977, §12.6). This result, of
importance in many other connections as well, is first proved for an arbitrary
field of characteristic zero, and then extended to fields of characteristic $p$
by using properties of the decomposition map (§@sec:decomposition-map).
#idx("Berman-Witt Theorem")
#idx("Witt-Berman Theorem")
#idx("Induction Theorems")
#idx("Induction Theorems", "Berman-Witt")

Our presentation in §@sec:induction-arbitrary-fields follows Serre
(@bib:Serre1977, Chapters~12 and~17) and @bib:CurtisReiner1962[CR §42].

=== The Witt-Berman Induction Theorem <ss:witt-berman-induction>

We recall from §@ss:modular-splitting-fields that a field $K$ of characteristic
zero is said to be _sufficiently large_ relative to $G$ provided that $K$
contains the $m$-th roots of~1, where $m$ is the exponent of $G$. The Brauer
Induction Theorem~@th:brauer-elementary-character-ideal asserts that
$ "ch" K G=sum_(H in cal(E)) ("ch" K H)^G, $
where $cal(E)$ is the set of elementary subgroups of $G$, and $K$ is
sufficiently large. For arbitrary fields $K$ of characteristic zero, the right
hand side is, in general, properly contained in $"ch" K G$ (see
Exercise~@exc:real-elementary-induction-proper). Equality can be restored by
enlarging the family of subgroups $cal(E)$. In
§@ss:induction-positive-characteristic, we shall obtain a similar result for
fields of characteristic $p>0$.

#source(514)
Until further notice, let $K$ denote an arbitrary field of characteristic zero,
$G$ a finite group, $m$ the exponent of $G$, and set $F=K(omega)$, where $omega$
is a primitive $m$-th root of~1. By
Corollary~@cor:exponent-cyclotomic-splitting-field, $F$ is a splitting field for
$G$ and all subgroups of $G$. Moreover, $F$ is a Galois extension of $K$, whose
Galois group we denote by $frak(G)$. Each automorphism $sigma in frak(G)$ is
uniquely determined by its action on $omega$, and is given by
$sigma(omega)=omega^t$, where $t$ is an integer uniquely determined modulo $m$.
Thus $t$ corresponds to a unit in $ZZ slash m ZZ$, and there is a monomorphism
$frak(G)->(ZZ slash m ZZ)'$, given by $sigma mapsto t$. We write $sigma_t$ for
the element of $frak(G)$ corresponding to $t+m ZZ$ in $(ZZ slash m ZZ)'$, and
denote the image of $frak(G)$ in $(ZZ slash m ZZ)'$ by $I_(m)(K)$.

For $t in I_(m)(K)$ and $x in G$, the element $x^t in G$ is well defined since
$x^m=1$. Hence $I_(m)(K)$ acts on $G$, with $t in I_(m)(K)$ sending $x$ to
$x^t$.

We also have an action of $frak(G)$ on $cf_F G$, the vector space of $F$-valued
class functions on $G$, given by
$ (sigma f)(x)=sigma(f(x)),f in cf_F G,sigma in frak(G),x in G. $
If $zeta$ is an $F$-character of $G$, afforded by an $F G$-module $Z$, then for
each $t in I_(m)(K)$ we have
$ sigma_(t)(zeta)(x)=zeta(x^t),x in G. $ <eq:galois-character-power-values>
Indeed, as we have shown before, $zeta(x)$ is the sum of the eigenvalues of $x$
acting on $Z$, while $zeta(x^t)$ is the sum of the $t$-th powers of the
eigenvalues, and is therefore the same as $sigma_(t)(zeta)(x)$.

We recall that for $x$ and $y$ in $G$, we write $x=_G y$ if $x$ and $y$ are
conjugate in $G$. We now define $x$ and $y$ to be _K-conjugate_ provided that
$ x=_G y^t quad "for some" t in I_(m)(K). $
The relation of $K$-conjugacy is an equivalence relation on $G$, and the
equivalence classes are called _K-conjugacy classes_.
#idx("K-conjugacy class")
#idx("conjugacy class")

A subgroup $H<=G$ is called a _K-elementary subgroup for a prime p_ provided
that $H$ is a semidirect product
$ H=chevron.l x chevron.r times.r D $
of a cyclic $p'$-group $chevron.l x chevron.r$ and a $p$-group $D$ acting on
$chevron.l x chevron.r$, such that for each $u in D$, $u x u^(-1)=x^t$ for some
$t in I_(m)(K)$. Evidently, two elements of $chevron.l x chevron.r$ are
conjugate in $H$ only if they are $K$-conjugate in $H$.
#idx("K-elementary subgroup")
#idx("elementary subgroup")

If $K$ contains $omega$, then $I_(m)(K)=1$, and $K$-conjugacy becomes ordinary
conjugacy in $G$. In this case, the $K$-elementary subgroups are the elementary
subgroups considered in §@sec:artin-brauer-induction (see
@def:elementary-subgroup). At the other extreme, if $K=QQ$, the $K$-elementary
groups are the hyperelementary groups, used in the Goldschmidt-Isaacs proof of
the Brauer Induction Theorem in §@sec:artin-brauer-induction.

#source(515)
We now introduce some additional notation which will be used throughout the rest
of this subsection:

$cal(E)_K=cal(E)_(K)(G)$: the set of all $K$-elementary subgroups of $G$.

$R=ZZ[omega]$: a ring of algebraic integers in $F$, where $F=K(omega)$.

$"ch" K G,"ch" F G$: the rings of virtual $K$-characters and $F$-characters of
$G$, respectively.
#idx("virtual characters")
#idx("virtual characters", "ring of")

$
  Irr_F G={zeta^1=1_G,zeta^2,dots,zeta^s}. \
  v(cal(E)_K,G)=sum_(H in cal(E)_K) ("ch" K H)^G. \
  "ch"_R K G=R times.o_ZZ "ch" K G,
  "ch"_K K G=K times.o_ZZ "ch" K G. \
  "ch"_F K G=F times.o_ZZ "ch" K G,
  "ch"_F F G=F times.o_ZZ "ch" F G. \
  v_(R)(cal(E)_K,G)=R times.o_ZZ v(cal(E)_K,G).
$

Since $"ch" K G$ is a free $ZZ$-module with finite basis, the ring $"ch"_R K G$
consists simply of all $R$-linear combinations of the elements of $"ch" K G$,
and can be viewed as a subring of $cf_F G$. Similar remarks apply to the rings
$"ch"_K K G,"ch"_R F G$, etc. The Galois group $frak(G)$ acts on $cf_F G$ as
shown above, and hence acts also on each of these subrings.

#proposition[
  A class function $psi in cf_F G$ belongs to $"ch"_K F G$ if and only if
  $ sigma_(t)(psi(x))=psi(x^t) quad "for all" t in I_(m)(K) "and all" x in G. $
] <prop:galois-equivariant-character-span>
#proof[
  The formula holds for $F$-characters of $G$, by
  @eq:galois-character-power-values, and hence for class functions
  $psi in "ch"_K F G$, since $sigma_t$ fixes elements of $K$, for all
  $t in I_(m)(K)$. Conversely, suppose the condition holds for some
  $psi in cf_F G$, and write
  $ psi=sum a_i zeta^i,a_i in F, $
  where $a_i=(psi,zeta^i)$. We have to show that each $a_i in K$, that is,
  $sigma_(t)(a_i)=a_i$ for all $t in I_(m)(K)$. By definition of the inner
  product, we have
  $ (psi,zeta^i)=|G|^(-1)sum_(x in G) psi(x)zeta^(i)(x^(-1)). $
  #source(516)
  For each $t in I_(m)(K)$, it follows from the assumption on $psi$ that
  $
    sigma_(t)(psi,zeta^i)
    &=|G|^(-1)sum_(x in G) sigma_(t)(psi(x))sigma_(t)(zeta^(i)(x^(-1))) \
    &=|G|^(-1)sum_(x in G) psi(x^t)zeta^(i)(x^(-t))=(psi,zeta^i),
  $
  as required.
]

#corollary[
  A class function $psi in cf_K G$ belongs to $"ch"_K K G$ if and only if $psi$
  is constant on the $K$-conjugacy classes of $G$.
] <cor:field-character-span-conjugacy>
#proof[
  Each $psi in "ch"_K K G$ takes values in $K$, so is fixed by $sigma_t$ for all
  $t in I_(m)(K)$. Therefore
  $ psi(x)=psi(x^t) quad "for all" x in G "and all" t in I_(m)(K) $
  <eq:field-character-power-invariance>
  by @prop:galois-equivariant-character-span, since
  $"ch"_K K G subset.eq "ch"_K F G$. Thus $psi$ is constant on the $K$-conjugacy
  classes.

  Conversely, let $psi in cf_K G$ be constant on the $K$-conjugacy classes. Then
  @eq:field-character-power-invariance holds, so
  @prop:galois-equivariant-character-span gives an expansion
  $ psi=sum_(i=1)^s a_i zeta^i,a_i in K. $
  Further, $sigma_t psi=psi$ for all $t in I_(m)(K)$. Since the coefficients
  $a_i$ lie in $K$, and are thus fixed under the action of $frak(G)$, it follows
  that the coefficients are constant on the $frak(G)$-orbits in $Irr_F G$. The
  sum of characters in such an orbit is a rational multiple of a $K$-character
  of $G$, by Exercise~@exc:galois-conjugate-characters. Hence
  $psi in "ch"_K K G$, completing the proof.
]

From these results we obtain easily:

#theorem[
  The characters ${theta^1,dots,theta^n}$ of a basic set of simple $K G$-modules
  form a basis of the $K$-space consisting of all functions in $cf_K G$ which
  are constant on the $K$-conjugacy classes. In particular, the number of
  distinct simple $K G$-modules is equal to the number of $K$-conjugacy classes.
] <th:field-character-conjugacy-classes>
#proof[
  Each character $theta^i$ is a multiple of a sum of characters
  ${zeta^j} subset.eq Irr_F G$ corresponding to a $frak(G)$-orbit in $Irr_F G$,
  by Exercise~@exc:galois-conjugate-characters. Therefore the ${theta^i}$ are
  linearly independent because of the linear independence of the ${zeta^j}$ and
  the fact that the orbits corresponding to $theta^i$ and $theta^j$ are disjoint
  if $i!=j$. By Corollary~@cor:field-character-span-conjugacy, every class
  function in $cf_K G$ which is constant on the $K$-conjugacy classes is a
  $K$-linear combination of the ${theta^j}$, and the result follows. The Theorem
  is due to Witt @bib:Witt1952 and Berman @bib:Berman1956b.
]

#source(517)
The main result of the section is as follows:

#theorem(name: "Witt-Berman Theorem")[
  Let $K$ be an arbitrary field of characteristic zero. Then
  $ "ch" K G=v(cal(E)_K,G), $
  that is, every $K$-character $zeta$ of $G$ can be expressed as a $ZZ$-linear
  combination of induced characters of the form $mu^G$, where $mu$ is a
  $K$-character of a $K$-elementary subgroup of $G$.
] <th:witt-berman-induction>
#idx("Berman-Witt Theorem", target: [@th:witt-berman-induction])
#idx("Witt-Berman Theorem", target: [@th:witt-berman-induction])
#idx("Induction Theorems", "Berman-Witt", target: [@th:witt-berman-induction])

We have remarked that in case $K$ is sufficiently large, the $K$-elementary
subgroups coincide with the elementary subgroups defined in
§@sec:artin-brauer-induction. Thus the Witt-Berman Theorem, in this case,
includes the Brauer Induction Theorem~@th:brauer-elementary-character-ideal. The
proof of the Witt-Berman Theorem, when specialized to the case of a sufficiently
large field $K$, offers a quite different approach to the proof of the Brauer
Induction Theorem from that given in §@sec:artin-brauer-induction.

Now let $K$ be arbitrary. We note first that $v(cal(E)_K,G)$ is an ideal in
$"ch"(K G)$ by @lem:class-function-induction-product; hence the theorem will be
proved once we show that the trivial character $zeta^1$ belongs to
$v(cal(E)_K,G)$. As the first lemma shows, it is sufficient to prove the weaker
result that $zeta^1 in v_(R)(cal(E)_K,G)$, where $R=ZZ[omega]$.

#lemma[
  If $zeta^1 in v_(R)(cal(E)_K,G)$, then $zeta^1 in v(cal(E)_K,G)$.
] <lem:integral-character-ideal-descent>
#proof[
  We first observe that $R slash ZZ$ is a torsionfree $ZZ$-module, since if
  $q alpha in ZZ$ for $alpha in R$, $q in ZZ$, then $alpha in QQ inter R=ZZ$. It
  follows that $ZZ$ is a direct summand of $R$, so we may write
  $R=plus.o.big_1^d ZZ r_i$, with $r_1=1$. Now let $N=v(cal(E)_K,G)$,
  $M="ch" K G$. Then $N subset.eq M$, and we have $zeta^1 in M$ and by
  hypothesis $1 times.o zeta^1 in R times.o_ZZ N$. We must prove that
  $1 times.o zeta^1 in 1 times.o N$. Identify $N$ with $1 times.o N$, $M$ with
  $1 times.o M$. Then $R times.o N=plus.o.big_1^d r_i times.o N$,
  $R times.o M=plus.o.big_1^d r_i times.o M$, and
  $ zeta^1=1 times.o zeta^1=sum_(i=1)^d r_i times.o n_i,n_i in N, $
  so
  $
    1 times.o zeta^1-1 times.o n_1
    =sum_(i=2)^d r_i times.o n_i in plus.o.big_(i=2)^d r_i times.o M.
  $
  The left side is in $1 times.o M$, so we obtain $zeta^1=n_1 in N$, as
  required.
]

We next prove several interesting lemmas about $K$-characters of $K$-elementary
subgroups of $G$. As in §@ss:applications-brauer-induction, we shall write
$|G|_p$ and $|G|_(p')$ for the $p$-part and $p'$-part, respectively, of the
order of a group $G$.

#source(518)
#lemma[
  Let $H=chevron.l x chevron.r D$ be a $K$-elementary subgroup of $G$, with
  $chevron.l x chevron.r$ a $p'$-group and $D$ a $p$-group, for some prime $p$.
  Then the restriction map
  $"res"_(chevron.l x chevron.r)^H:"ch" K H->"ch" K chevron.l x chevron.r$
  is surjective. In fact, every $K$-character of $chevron.l x chevron.r$ is the
  restriction to $chevron.l x chevron.r$ of some $K$-character of $H$.
] <lem:elementary-cyclic-character-extension>
#proof[
  If $x$ has order $c$, then
  $
    K chevron.l x chevron.r
    tilde.equiv K[X] slash (X^c-1)
    tilde.equiv product_(i=1)^q K[X] slash (f_(i)(X))
    tilde.equiv product_(i=1)^q K_i,
  $
  where $X$ is an indeterminate, and the ${K_i}$ are subfields of $F$ containing
  $K$ which correspond to the irreducible factors ${f_(i)(X)}$ of $X^c-1$. The
  fields ${K_i}$ are a basic set of simple $K chevron.l x chevron.r$-modules,
  with $x$ acting on $K_i$ as multiplication by a zero $theta_i$ of $f_(i)(X)$
  in $K_i$.

  We shall prove that for each fixed $i$, the action of $chevron.l x chevron.r$
  on $K_i$ can be extended to an action of $H$ on $K_i$. For $y in D$, we may
  write
  $ y x y^(-1)=x^t,quad "where" t in I_(m)(K). $
  Each $sigma_t in frak(G)$ carries $K_i=K(theta_i)$ onto itself, since the
  cyclotomic Galois group $frak(G)$ is abelian. The restriction $sigma_t|_(K_i)$
  sends $theta_i$ to $theta_i^t$ and is independent of the chosen admissible
  lift $t$: the action of $y$ on $x$ determines $t$ modulo $c$, and the order of
  $theta_i$ divides $c$. These restrictions therefore define a homomorphism
  $D->"Gal"(K_i slash K)$, by the multiplication law for the action of $D$ on
  $chevron.l x chevron.r$. Thus $D$ acts on $K_i$, with $y$ operating as
  $sigma_t|_(K_i)$.#ed-note[
    The action on $K_i$ need not lift to $I_(m)(K)$. For example, take
    $G=S_3 times C_5$ and let $K$ be the fixed field of $chevron.l sigma_17
    chevron.r$ in $QQ(zeta_30)$. Then $I_30(K)=chevron.l 17 chevron.r$ is cyclic
    of order~4; its image modulo~3 has order~2 but has no section. Thus the
    subgroup of order~2 in $S_3$ that inverts a 3-cycle has no such lift.
  ] We now have to prove that the separate actions of $chevron.l x chevron.r$
  and $D$ on $K_i$ define a $K$-representation of $H$.

  For each $t in I_(m)(K)$, the automorphism $sigma_t|_(K_i)$ carries $c$-th
  roots of~1 onto their $t$-th powers, since $c$ divides $m$. Hence
  $sigma_(t)(theta_i)=theta_i^t$. In order to prove that the separate actions of
  $D$ and $chevron.l x chevron.r$ on $K_i$ define a representation of $H$, it is
  sufficient to check that
  $ sigma_t theta_i sigma_t^(-1)=theta_i^t $
  as left operators on $K_i$. For this, it suffices to calculate their action on
  the powers ${theta_i^j}$, since $K_i=K(theta_i)$. But
  $
    (sigma_t theta_i sigma_t^(-1))theta_i^j
    =sigma_(t)(theta_i)sigma_(t)(sigma_t^(-1)theta_i^j)=theta_i^t theta_i^j,
  $
  as desired, and the proof is complete.
]

#lemma[
  Let $p$ be a prime, and let $x in G$ be a $p'$-element of order $c$. Set
  $
    N_((K))(x)={y in G:y x y^(-1)=x^t "for some" t in I_(m)(K)}.
  $
  Let $D$ be a Sylow $p$-subgroup of $N_((K))(x)$. Then
  $H=chevron.l x chevron.r D$ is a $K$-elementary
  #source(519)
  subgroup of $G$. Let $J$ be the image of $I_(m)(K)$ in $(ZZ slash c ZZ)'$,
  with each residue included once. Then there exists an element
  $xi in "ch"_R K H$ such that #named-equation(name: [$(ast)$])[$
    xi(x^j)=cases(c & "if" j in J, 0 & "otherwise".)
  $] <eq:elementary-cyclic-orbit-indicator>
] <lem:elementary-cyclic-orbit-indicator>
#proof[
  It is immediate from the definition that $N$ is a group, and that $H$ is a
  $K$-elementary subgroup. Let ${chi_1,dots,chi_c}$ be a basic set of
  irreducible $F$-characters of $chevron.l x chevron.r$; they are all linear
  characters since $omega in F$. Define $xi_1:chevron.l x chevron.r->ZZ$ by the
  formula @eq:elementary-cyclic-orbit-indicator above; then
  $xi_1 in cf_F chevron.l x chevron.r$. Hence
  $ xi_1=sum_(i=1)^c a_i chi_i,a_i in F, $ <eq:cyclic-orbit-character-expansion>
  where the coefficients $a_i$ are given by the orthogonality relations:
  $
    a_i=c^(-1)sum_(j=1)^c xi_1(x^j)chi_(i)(x^(-j))
    =sum_(j in J) chi_(i)(x^(-j)),1<=i<=c.
  $
  Thus each $a_i in R$, and since $a_i$ is a sum of $frak(G)$-conjugate elements
  of $F$, we have also $a_i in K$ for all $i$. Since $a_i$ is fixed by all
  automorphisms in $frak(G)$, it follows from the above formula that the
  coefficients $a_i$ in @eq:cyclic-orbit-character-expansion are constant on
  $frak(G)$-orbits of characters ${chi_i}$. It is easily shown, using the first
  part of the proof of Lemma~@lem:elementary-cyclic-character-extension (or
  Exercise~@exc:galois-conjugate-characters), that the sums of the
  $F$-characters ${chi_i}$ in different $frak(G)$-orbits coincide with the
  irreducible $K$-characters of $chevron.l x chevron.r$. Thus we have shown that
  $xi_1$ is an $R$-linear combination of $K$-characters of
  $chevron.l x chevron.r$. By Lemma~@lem:elementary-cyclic-character-extension,
  each $K$-character on $chevron.l x chevron.r$ can be lifted to a $K$-character
  of $H$, so we can define an $R$-linear combination $xi$ of $K$-characters of
  $H$ whose restriction to $chevron.l x chevron.r$ agrees with $xi_1$,
  completing the proof.
]

#lemma[
  Keep the notation of @lem:elementary-cyclic-orbit-indicator, and let
  $psi=xi^G$, where $xi in "ch"_R K H$ is the class function constructed in
  @lem:elementary-cyclic-orbit-indicator. Then $psi in v_(R)(cal(E)_K,G)$, and
  satisfies the conditions:
  $ psi(x)=|N_((K))(x)|_(p'), $
  and
  $ psi(s)=0 $
  for each $s in G_(p')$ such that $s$ is not $K$-conjugate to $x$.
] <lem:induced-cyclic-orbit-indicator>
#proof[
  It is clear from the definition of $psi$ that $psi in v_(R)(cal(E)_K,G)$. Let
  $s in G_(p')$, and suppose $psi(s)!=0$. By @eq:induced-character-average,
  $y s y^(-1) in H$ and $xi(y s y^(-1))!=0$, for some $y in G$. Then
  $y s y^(-1) in G_(p') inter H$, and so $y s y^(-1) in chevron.l x chevron.r$;
  since $xi(y s y^(-1))!=0$, we have $y s y^(-1)=x^t$ for some $t in I_(m)(K)$.
  Thus if $s in G_(p')$ is such that $psi(s)!=0$, then $s$ is $K$-conjugate to
  $x$.
  #source(520)
  Now let $S={x^t:t in I_(m)(K)}$. Then by @eq:induced-character-average,
  $
    psi(x)=|H|^(-1)sum_(y in G,y x y^(-1) in S) c
    =|H|^(-1)|N_((K))(x)|c=|N_((K))(x)|_(p'),
  $
  since $c=|chevron.l x chevron.r|$ and $|H|=c|N_((K))(x)|_p$. This completes
  the proof.
]

We require one more preliminary result.

#lemma[
  Let $p$ be a prime, and let $P$ be a prime ideal in $R$ containing $p$. Then
  for all $phi in "ch"_R K G$, we have $phi(x) equiv phi(y) ("mod" P)$, for any
  two elements $x,y in G$ whose $p'$-parts are $K$-conjugate to each other.
] <lem:character-congruence-regular-parts>
#proof[
  By Corollary~@cor:field-character-span-conjugacy, $phi$ is constant on
  $K$-conjugacy classes. Hence it suffices to show that
  $phi(x) equiv phi(y) ("mod" P)$ if $x$ is the $p'$-part of $y$. Both $x,y$ lie
  in $chevron.l y chevron.r$, and by restriction to $chevron.l y chevron.r$ and
  extension of the ground ring $R$, it is sufficient to prove the result for an
  irreducible, hence linear, $F$-character $mu$ of $chevron.l y chevron.r$. Let
  $y=x u$, where $u$ is the $p$-part of $y$. Then $mu(y)=mu(x)mu(u)$. Moreover,
  $mu(u)^(p^d)=1$ for some integer $d$, so $(mu(u)-1)^(p^d) equiv 0 ("mod" P)$.
  Since $P$ is a prime ideal, we obtain $mu(u) equiv 1 ("mod" P)$ and
  $mu(y) equiv mu(x) ("mod" P)$, as required.
]

#proof(head: emph[Proof of the Witt-Berman Theorem @th:witt-berman-induction.])[
  By Lemma~@lem:integral-character-ideal-descent, it is sufficient to prove that
  $zeta^1 in v_(R)(cal(E)_K,G)$. Since the integers
  ${|G|_(p'):p "prime",p divides |G|}$ are relatively prime, it suffices to
  prove, for a fixed prime $p$ dividing $|G|$, that
  $|G|_(p')zeta^1 in v_(R)(cal(E)_K,G)$. Let ${x_j}_(j in J)$ be a set of
  representatives of the $p$-regular $K$-conjugacy classes of $G$, and let
  ${P_i}_(i in I)$ be the set of prime ideals in $R$ containing the rational
  prime $p$. Now $R=ZZ[omega]$ is a Dedekind domain (see
  @bib:CurtisReiner1962[CR (21.13)]). From this result, or from the elementary
  fact that $R slash p R$ is an artinian ring, we know that the prime ideals
  ${P_i}$ are maximal ideals, finite in number. Further, since
  $inter.big_(i in I) P_i$ maps onto $rad(R slash p R)$, we obtain#footnote[From
    Theorem~@th:cyclotomic-prime-factorization, it follows readily that, in
    fact, $(product_(i in I) P_i)^h=p R$ for some $h$. However, this stronger
    result will not be needed in the present proof.]
  $
    (product_(i in I) P_i)^h
    subset.eq (inter.big_(i in I) P_i)^h subset.eq p R
  $
  for some positive integer $h$, by the results of §@sec:radicals. We shall keep
  the above notation throughout the remaining steps of the proof.

  _Step 1._ We shall show that there exists an $eta in v_(R)(cal(E)_K,G)$ such
  that
  $ eta(x) equiv 1 ("mod" P_i),x in G,i in I. $
  For each $p$-regular class representative $x_j$, $j in J$, let
  $psi_j in v_(R)(cal(E)_K,G)$ be the
  #source(521)
  function defined in Lemma~@lem:induced-cyclic-orbit-indicator; it satisfies
  the conditions
  $
    psi_(j)(x_j)=|N_((K))(x_j)|_(p'),quad
    psi_(j)(x_(j'))=0,j'!=j.
  $
  For each $j$, let $a_j$ be a rational integer such that
  $a_j|N_((K))(x_j)|_(p') equiv 1 ("mod" p)$, and define
  $ eta=sum_(j in J) a_j psi_j. $
  Now let $x in G$, and $i in I$. By
  Lemma~@lem:character-congruence-regular-parts, we have
  $eta(x) equiv eta(x_(j_0)) ("mod" P_i)$, for some $j_0 in J$; hence
  $
    eta(x) equiv eta(x_(j_0))
    equiv sum_j a_j psi_(j)(x_(j_0))
    equiv a_(j_0)psi_(j_0)(x_(j_0)) equiv 1 ("mod" P_i),
  $
  as required.

  _Step 2._ There exists a positive integer $q$ such that the function $eta$
  defined in Step~1 satisfies the condition:
  $ eta(x)^q equiv 1 ("mod" |G|_p R) quad "for all" x in G. $
  The proof of this assertion is an easy consequence of Step~1 and the remarks
  preceding Step~1, and is left to the reader as an exercise.

  Now consider the function
  $ phi=|G|_(p')(zeta^1-eta^q) in "ch"_R K G. $
  By Step~2,
  $
    phi(x)=|G|_(p')(1-eta(x)^q) equiv 0 ("mod" |G|R)
  $
  for all $x in G$. If we can prove that such a function $phi$ belongs to
  $v_(R)(cal(E)_K,G)$, then we will have the desired conclusion:
  $
    |G|_(p')zeta^1=phi+|G|_(p')eta^q in v_(R)(cal(E)_K,G),
  $
  since $eta^q in v_(R)(cal(E)_K,G)$ by Step~1. The last step is handled as
  follows:

  _Step 3._ For each $x in G$ (not necessarily a $p'$-element), let $J_x$ be the
  image of $I_(m)(K)$ in $(ZZ slash |x| ZZ)'$, with each residue included once.
  The proof of @lem:elementary-cyclic-orbit-indicator shows that we can find an
  element $xi in "ch"_R K chevron.l x chevron.r$ such that
  $
    xi(x^j)=cases(
      "order of" x & "if" j in J_x,
      0 & "otherwise".,
    )
  $
  #source(522)
  The proof of @lem:induced-cyclic-orbit-indicator shows that
  $
    xi^(G)(y)=cases(
      |N_((K))(x)| & "if" y "is" K"-conjugate to" x,
      0 & "otherwise".,
    )
  $
  Since $chevron.l x chevron.r$ is obviously a $K$-elementary subgroup of $G$,
  it follows that $xi^G in v_(R)(cal(E)_K,G)$.

  Now let ${x_1,dots,x_t}$ represent the $K$-conjugacy classes of $G$, and for
  each $x_i$ construct an element $xi_i$ as above. Then for the function $phi$
  defined in Step~2, we have
  $ phi=sum_(i=1)^t phi(x_i) / abs(N_((K))(x_i)) xi_i^G. $
  This follows at once from the fact that both sides are constant on
  $K$-conjugacy classes in $G$, and agree at each $x_i$, $1<=i<=t$. Finally,
  each coefficient $phi(x_i) / abs(N_((K))(x_i))$ lies in $R$, so
  $phi in v_(R)(cal(E)_K,G)$. This completes the proof of the Witt-Berman
  Theorem for fields of characteristic zero.
]

#heading(level: 3)[
  The Induction Theorem over Fields of Characteristic $p>0$
] <ss:induction-positive-characteristic>

Let $(K,R,k)$ be a $p$-modular system, with $K$ a field of characteristic zero.
We shall first reformulate the Witt-Berman Theorem so that it makes sense for
$k G$-modules. By Proposition~@prop:grothendieck-character-ring, there is an
isomorphism of rings: $"ch" K G tilde.equiv G_0(K G)$. Moreover, for each
subgroup $H$ of $G$, the induction map $"ind"_H^G:"ch" K H->"ch" K G$ is part of
a commutative diagram
#character-induction-square
where the vertical maps are defined as in
Proposition~@prop:grothendieck-character-ring. The map
$"ind"_H^G:G_0(K H)->G_0(K G)$, also called _induction_, is defined by the
formula $"ind"_H^G lr([L])=[L^G]$ for each isomorphism class $[L]$ of
$K H$-modules. The Witt-Berman Theorem~@th:witt-berman-induction thus becomes,
in the language of Grothendieck groups,
$ G_0(K G)=sum_(H in cal(E)_K) "ind"_H^G G_0(K H), $
<eq:witt-berman-grothendieck-induction>
where $cal(E)_K$ is the family of $K$-elementary subgroups of $G$. We shall
prove a result analogous to @eq:witt-berman-grothendieck-induction, with $K$
replaced by $k$.

#source(523)
When $K$ is sufficiently large, $cal(E)_K$ is the family of elementary subgroups
of $G$, and by Exercise~@exc:brauer-induction-brauer-characters we have
$ "Bch" k G=sum_(H in cal(E)) ("Bch" k H)^G, $
where $"Bch"$ denotes the ring of virtual Brauer characters. Since
$"Bch" k G tilde.equiv G_0(k G)$ by @prop:grothendieck-brauer-character-ring,
the above formula becomes
$ G_0(k G)=sum_(H in cal(E)) "ind"_H^G G_0(k H), $
which is the desired analogue of @eq:witt-berman-grothendieck-induction when $K$
is sufficiently large.

With these remarks as motivation, we consider an arbitrary $p$-modular system
$(K,R,k)$, with $char K=0$. For each subgroup $H<=G$, the restriction map
$M mapsto M_H$ carries any ses of $k G$-modules to a ses of $k H$-modules, and
hence defines a $ZZ$-homomorphism
$ "res"_H^G:G_0(k G)->G_0(k H) $
such that $"res"_H^G lr([M])=[M_H]$ for a $k G$-module $M$. It is easily checked
that the restriction map commutes with the decomposition map
$d:G_0(K G)->G_0(k G)$, defined in @prop:decomposition-homomorphism-existence,
in the sense that there exists a commutative diagram
#restriction-decomposition-square
Similar remarks apply to induction. If $L$ is a $k H$-module, then
$L^G=k G times.o_(k H) L$ is a $k G$-module. Moreover, $k G$ is a free right
$k H$-module, so each ses
$ 0->L'->L->L''->0 $
of $k H$-modules yields, by @prop:projective-is-flat, a ses of $k G$-modules:
$ 0->L'^G->L^G->L''^G->0. $
Therefore the map $"ind"_H^G:G_0(k H)->G_0(k G)$, defined by
$"ind"_H^G lr([L])=[L^G]$, is a $ZZ$-homomorphism.

#source(524)
We next show that, as in the case of restriction, the operation $"ind"_H^G$
commutes with the decomposition map. We have to prove that the diagram
#induction-decomposition-square
commutes. For this, it suffices to show that
$overline(M)^G tilde.equiv overline(M^G)$ for each $R H$-lattice $M$, where bars
denotes reduction mod $frak(p)$. To accomplish this objective, we note that
$overline(M)$ is defined by a ses of $R H$-modules:
$ 0->M arrow^(pi) M->overline(M)->0, $
where $pi$ denotes multiplication by a generator $pi$ of $frak(p)$. As we have
noted above, we then have a ses of $R G$-modules
$ 0->M^G arrow^(pi) M^G->overline(M)^G->0. $
Thus $overline(M^G)=M^G slash pi M^G tilde.equiv overline(M)^G$, as required.

We next require a version of Lemma~@lem:class-function-induction-product for
Grothendieck rings (see also Exercise~@exc:brauer-character-induction-product).
We recall that for an arbitrary field $E$, multiplication in $G_0(E G)$ is given
by the formula $[M][N]=[M times.o_E N]$ (see
@eq:grothendieck-tensor-multiplication).

#lemma[
  Let $E$ be an arbitrary field, and let $H$ be a subgroup of $G$. Then for all
  $u in G_0(E H)$, $v in G_0(E G)$, we have
  $ ("ind"_H^G u)dot v="ind"_H^(G)(u dot "res"_H^G v). $
] <lem:grothendieck-induction-product>
#proof[
  By our preceding remarks, it is sufficient to prove that if $L$ is a left
  $E H$-module, and $M$ a left $E G$-module, then there is an isomorphism of
  $E G$-modules
  $ L^G times.o_E M tilde.equiv (L times.o_E M_H)^G. $
  But this result was proved in @cor:induction-tensor-identity by using the
  Tensor Product Theorem.
]

Now we come to the main result of this subsection.

#theorem[
  Let $(K,R,k)$ be an arbitrary $p$-modular system, with $char K=0$. Then
  $ G_0(k G)=sum_(H in cal(E)_K) "ind"_H^(G)(G_0(k H)), $
  where $cal(E)_K$ is the family of $K$-elementary subgroups of $G$.
] <th:witt-berman-modular-grothendieck-induction>
#source(525)
#proof[
  Using Lemma~@lem:grothendieck-induction-product with $E=k$, it follows that
  the right hand side is an ideal in the ring $G_0(k G)$. Thus it is sufficient
  to prove that the identity element of $G_0(k G)$ belongs to the sum on the
  right hand side. The identity element of $G_0(K G)$ is $[1_G]$, where $1_G$
  affords the trivial character of $G$; also, $d[1_G]$ is the identity element
  of $G_0(k G)$, where $d:G_0(K G)->G_0(k G)$ is the decomposition map. By the
  Witt-Berman Theorem~@th:witt-berman-induction (or by
  @eq:witt-berman-grothendieck-induction) we have
  $
    [1_G]=sum_(H in cal(E)_K) a_H "ind"_H^(G)(u_H),
    quad "where" a_H in ZZ,u_H in G_0(K H)
    "for each" H in cal(E)_K,
  $
  and $cal(E)_K$ is the family of $K$-elementary subgroups of $G$. Applying the
  decomposition map $d$ to both sides of this formula, we obtain
  $
    d[1_G]=sum_H a_H d("ind"_H^G u_H)
    =sum_H a_H "ind"_H^(G)(d(u_H)),
  $
  using the fact that the decomposition map commutes with induction. Since
  $d(u_H) in G_0(k H)$ for each subgroup $H in cal(E)_K$, the proof is complete.
]

=== The Cartan-Brauer Triangle (General Case) <ss:cartan-brauer-general-case>

Throughout this subsection, $G$ denotes a finite group, and $(K,R,k)$ a
$p$-modular system such that $char K=0$, and $R$ is complete in the
$frak(p)$-adic topology. It is not assumed that either $K$ or $k$ are splitting
fields. In this setting, we shall establish most of the properties of the
Cartan-Brauer Triangle which were previously proved in
§@sec:cartan-brauer-triangle under the additional assumption that $K$ is
sufficiently large. This part of our discussion is based on the treatment in
Serre @bib:Serre1977. We also include a proof of a theorem, due to Witt and
Berman, on the number of simple $E G$-modules, for an arbitrary field $E$ of
characteristic $p>0$ (see @th:field-character-conjugacy-classes for fields of
characteristic zero).

As we have shown in §@sec:cartan-brauer-triangle, the hypothesis that $R$ is
complete implies that $R G$ is semiperfect, and that there is an isomorphism of
$ZZ$-modules, $K_0(R G) tilde.equiv K_0(k G)$, given by reduction mod $frak(p)$.
The first main result is that the decomposition map $d:G_0(K G)->G_0(k G)$ is
surjective. The simplest examples show that the decomposition map need not be
surjective, in case $R$ is not assumed to be complete. Thus, further
generalizations are not always possible (see
Exercise~@exc:incomplete-decomposition-map-not-surjective).
#idx("decomposition map")

#theorem[
  Let $(K,R,k)$ be a $p$-modular system such that $R$ is complete, and
  $char K=0$. Then the decomposition map $d:G_0(K G)->G_0(k G)$ is surjective.
] <th:complete-decomposition-map-surjective>
#proof[
  By @eq:witt-berman-grothendieck-induction and
  @th:witt-berman-modular-grothendieck-induction, we have #named-equation(
    name: [$(ast)$],
  )[$
    G_0(K G)=sum_(H in cal(E)_K) "ind"_H^G G_0(K H)
  $] <eq:complete-decomposition-elementary-reduction>
  #source(526)
  and
  $ G_0(k G)=sum_(H in cal(E)_K) "ind"_H^G G_0(k H). $
  Here, in both cases, $cal(E)_K$ is the family of $K$-elementary subgroups of
  $G$. Since $d$ commutes with the operation $"ind"_H^G$ (see
  §@ss:induction-positive-characteristic), we have
  $
    d(G_0(K G))=sum_(H in cal(E)_K) "ind"_H^G d(G_0(K H)).
  $
  By virtue of formula @eq:complete-decomposition-elementary-reduction above, it
  therefore suffices to prove that
  $ d(G_0(K H))=G_0(k H) $ <eq:elementary-decomposition-surjectivity>
  for each $K$-elementary subgroup $H$ of $G$. Thus the proof of
  @th:complete-decomposition-map-surjective will be complete once we establish
  the following more general version of
  @eq:elementary-decomposition-surjectivity:
]

#proposition[
  Let $(K,R,k)$ be a $p$-modular system with $char K=0$ and $R$ complete in the
  $frak(p)$-adic topology. Let $H$ be a group which is a semi-direct product
  $A times.r D$ of a cyclic $q'$-group $A=chevron.l a chevron.r$ and a $q$-group
  $D$, for some prime $q$. Then every simple $k H$-module $F$ can be lifted to a
  simple $K H$-module $Z$, that is, there exists a full $R H$-lattice $M$ in $Z$
  such that $M slash frak(p)M tilde.equiv F$.
] <prop:hyperelementary-simple-module-lifting>

Before beginning the proof, we remark that any group $H$ satisfying the above
hypotheses is an example of a $p$-solvable group (see
§@ss:background-group-theory). Thus, in case $K$ is sufficiently large, the
above proposition is a special case of the Fong-Swan-Rukolaine Theorem proved in
§@sec:p-solvable-groups. In the situation occurring in
@prop:hyperelementary-simple-module-lifting, the stronger hypotheses on $H$
allow us to lift simple $k H$-modules, without having to assume that $K$ is
sufficiently large.

#proof(head: emph[Proof of @prop:hyperelementary-simple-module-lifting.])[
  We shall use induction on $|H|$. First suppose that $q!=p$, and let $S$ be the
  Sylow $p$-subgroup of $A$. Then $S$ is a normal $p$-subgroup of $H$, and acts
  trivially on the given simple $k H$-module $F$, by
  @prop:normal-p-subgroup-brauer-kernel. If we set $overline(H)=H slash S$, then
  $overline(H)$ is a $p'$-group, and $F$ is a simple $k overline(H)$-module.
  Therefore $F in cal(P)(k overline(H))$, and since $R$ is complete, $F$ can be
  lifted to a projective $R overline(H)$-lattice by
  @prop:projective-cover-summary; this lattice is then an $R H$-lattice, whose
  reduction mod $frak(p)$ is $F$, and the result is proved in this case where
  $q!=p$.

  Now assume that $q=p$, and let $L$ be a simple $k A$-submodule of $F_A$. If
  the $k A$-module $L$ is not $H$-stable, then let $H_1="Stab"_H L$, a proper
  subgroup of $H$. By Theorem~@th:clifford-theorem, we have
  $F tilde.equiv (L_1)^H$ for some simple $k H_1$-module $L_1$. Since the group
  $H_1$ also satisfies the hypotheses of
  @prop:hyperelementary-simple-module-lifting, we can apply the induction
  hypothesis to lift $L_1$ to a simple $K H_1$-module. It is then easily checked
  that $(L_1)^H$ can be lifted to a $K H$-module, and the result is established
  in this case.

  #source(527)
  Thus we may now assume that $L$ is $H$-stable, and that $F_A$ is a direct sum
  of copies of $L$. Using the notation of
  Exercise~@exc:cyclic-prime-to-p-unramified-decomposition, we may decompose
  $k A$ and $K A$ into direct sums of fields: $k A=product_i k_i$,
  $K A=product_i K_i$. To fix the notation, suppose that
  $
    L tilde.equiv k_1=k[y] slash (f_1(y))=k[overline(omega)],
    quad R_1=R[y] slash (g_1(y))=R[omega],
  $
  where $overline(g_1)=f_1$, and where $g_1(omega)=0$, $f_1(overline(omega))=0$.
  We may assume that $a$ acts on $k_1$ as multiplication by $overline(omega)$,
  and on $R_1$ as multiplication by $omega$.

  Let us now consider the action of $D$ on $F$. Since $D$ is a $p$-group, and
  $char k=p$, it follows from @th:p-group-algebra-local that $D$ acts trivially
  on the socle of $F_D$. Therefore $F$ contains a nonzero element $u$ such that
  $x u=u$ for all $x in D$. Then $(k A)u$ is a $k H$-submodule of $F$, since
  $x(k A)x^(-1)=k A$ for all $x in D$, because $A ⊴ H$. Therefore $F=(k A)u$,
  and so $F_A$ is a cyclic $k A$-module. Since $k A$ has no repeated summands as
  $k A$-module, it follows that $F_A tilde.equiv L$, that is,
  $F tilde.equiv k_1$ as $k A$-modules.

  For each $x in D$, $a$ acts on the conjugate module $attach(L, tl: x^(-1))$ in
  the same way that $x a x^(-1)$ acts on $L$. Writing $x a x^(-1)=a^t$ for some
  integer $t$, it follows that $x a x^(-1)$ acts as $overline(omega)^t$ on
  $k_1$. But $L$ is $H$-stable, and therefore $overline(omega)^t$ must be a zero
  of the polynomial $f_1(y)$ used to define $k_1$. This shows that the map
  $overline(omega) mapsto overline(omega)^t$ gives an element
  $sigma_x in frak(G)$, where $frak(G)$ is the Galois group
  $ frak(G)="Gal"(k_1 slash k) tilde.equiv "Gal"(R_1 slash R). $
  <eq:unramified-cyclic-galois-reduction>
  The map $x mapsto sigma_x$, $x in D$, is a homomorphism of $D$ into $frak(G)$,
  and allows us to view $k_1$ as a $k H$-module on which $a$ acts as
  $overline(omega)$ and $x in D$ acts as $sigma_x$. Then $F tilde.equiv k_1$ as
  $k H$-modules.

  In view of the isomorphism, we can make $R_1$ into an $R H$-lattice by letting
  $a$ act as $omega$, and $x in D$ act as $sigma_x$ (that is,
  $x dot omega=omega^t$ in terms of the above notation). Clearly
  $overline(R_1) tilde.equiv k_1$ as $k H$-modules, so $F$ has now been lifted
  to an $R H$-lattice $R_1$, and this completes the proof of
  Proposition~@prop:hyperelementary-simple-module-lifting, as well as the proof
  of Theorem~@th:complete-decomposition-map-surjective.
]

We remark that the structure of the simple module $F$ in the stable case, as in
the preceding proof, was described by
Theorem~@th:graded-clifford-correspondence, but not in a sufficiently precise
way to accomplish the lifting, without the help of the Galois theory of local
fields.

We now consider the Cartan-Brauer Triangle
#induction-cartan-triangle(punctuation: ",")
#idx("Cartan-Brauer triangle")
defined in §@ss:cartan-map-triangle whether or not the field $K$ is sufficiently
large. The next two
#source(528)
theorems will use the facts established in §@ss:cartan-brauer-large-field for
the splitting field case, together with some results on ground field extensions
proved in §@ss:grothendieck-ground-field-extension.

#theorem[
  The map $e:K_0(k G)->G_0(K G)$ is a split injection, for any $p$-modular
  system $(K,R,k)$ with $char K=0$ and $R$ complete in the $frak(p)$-adic
  topology.
] <th:projective-character-map-split-injection>
#proof[
  The result holds if $K$ is sufficiently large, by
  @prop:cartan-triangle-injectivity-cokernel. For the general case, by
  §@ss:modular-splitting-fields there exists a finite extension $(K',R',k')$ of
  $(K,R,k)$ in which $K'$ is sufficiently large. Now consider the commutative
  diagram
  #projective-character-extension-square()
  where $e$ and $e'$ are defined by @eq:projective-character-map, and
  $alpha,beta$ arise from ground field extensions. Then $e'$ is a split
  injection by @prop:cartan-triangle-injectivity-cokernel, so $gamma e'=1$ for
  some $gamma$ as shown below:
  #projective-character-extension-square(split: true)
  By @prop:grothendieck-scalar-extension-injections, both $alpha$ and $beta$ are
  injections, and therefore so is $e$, because $e'$ is an injection. Further, by
  @prop:grothendieck-scalar-extension-injections there exists a map $delta$ such
  that $delta alpha=1$. It follows at once that
  $ delta gamma beta e=delta gamma e'alpha=delta alpha=1, $
  so $delta gamma beta$ is the desired splitting of $e$.
]

Keeping the hypotheses of @th:projective-character-map-split-injection, we
obtain the following extension of
@cor:projective-lattices-determined-by-character:

#corollary[
  Let $P$ and $P' in cal(P)(R G)$ be such that
  $K times.o_R P tilde.equiv K times.o_R P'$ as $K G$-modules. Then
  $P tilde.equiv P'$ as $R G$-modules.
] <cor:complete-projective-lattices-character-isomorphism>

The next result is a reformulation and generalization of
@th:cartan-determinant-p-power, and we shall prove it without the use of Brauer
characters.

#source(529)
#theorem[
  Let $(K,R,k)$ be a $p$-modular system, with $R$ complete and $char K=0$. The
  Cartan homomorphism
  $ c:K_0(k G)->G_0(k G) $
  is injective, $op("cok") c$ is finite, and $|G|_p dot op("cok") c=0$.
] <th:cartan-map-cokernel-p-primary>
#idx("Cartan homomorphism", target: [@th:cartan-map-cokernel-p-primary])
#proof[
  Since $K_0(k G)$ and $G_0(k G)$ are $ZZ$-free of the same rank, by
  §@ss:cartan-map-triangle, it follows that $c$ is injective if and only if
  $op("cok") c$ is a finite $ZZ$-module.

  We first give a new proof of the result in case $K$ is sufficiently large (see
  @th:cartan-determinant-p-power and
  @prop:cartan-triangle-injectivity-cokernel), this time using the induction
  theorem @th:witt-berman-modular-grothendieck-induction instead of the theory
  of Brauer characters.

  If $K$ is sufficiently large, the family of $K$-elementary subgroups of $G$
  coincides with the family $cal(E)$ of elementary subgroups, and in this case
  @th:witt-berman-modular-grothendieck-induction gives
  $ G_0(k G)=sum_(H in cal(E)) "ind"_H^G G_0(k H). $
  We must prove that $|G|_p u in im c$ for every $u in G_0(k G)$. Since
  $|G|_p>=|H|_p$ for all $H in cal(E)$, and since the Cartan map obviously
  commutes with induction (see
  Exercise~@exc:induction-cartan-commutative-diagram), it is clearly sufficient
  to prove that $|H|_p$ annihilates $G_0(k H) slash c{K_0(k H)}$. But for such a
  group, $im c=|H|_p dot G_0(k H)$ by
  Exercise~@exc:elementary-group-cartan-image, which completes the proof of the
  theorem in the case where $K$ is sufficiently large.

  Turning to the general case, let $(K',R',k')$ be a finite extension of
  $(K,R,k)$ with $K'$ sufficiently large. Then there is a commutative diagram
  #cartan-extension-snake-diagram
  where $alpha$ and $beta$ are the injections defined in
  @prop:grothendieck-scalar-extension-injections, $c$ and $c'$ are Cartan
  homomorphisms, $X=op("cok") alpha$, $Y=op("cok") beta$, and $f$ is the
  homomorphism induced on $X$ by $c'$. By the Snake Lemma, there is an exact
  sequence of abelian groups
  $
    0->ker c->ker c'->ker f->op("cok") c->op("cok") c'.
  $
  By the first part of the proof, $ker c'=0$ and $|G|_p dot op("cok") c'=0$.
  Therefore $ker c=0$, and so $op("cok") c$ is finite, by the remark at the
  beginning of the proof. On the other hand, $alpha$ is a split injection by
  @prop:grothendieck-scalar-extension-injections, so $X$ is $ZZ$-free. Therefore
  $ker f$ is
  #source(530)
  also $ZZ$-free. From the exact sequence
  $ 0->ker f->op("cok") c->op("cok") c', $
  and the fact that $op("cok") c$ is finite, we conclude that $ker f=0$.
  Therefore $op("cok") c$ is embedded in $op("cok") c'$, and so
  $|G|_p dot op("cok") c=0$, which finishes the proof of the theorem.
]

As an immediate consequence of Theorem~@th:cartan-map-cokernel-p-primary, we
obtain the following corollaries, valid for an arbitrary $p$-modular system
$(K,R,k)$ in which $char K=0$ and $R$ is complete:

#corollary[
  Two f.g. projective $k G$-modules are isomorphic if and only if they have the
  same composition factors (counted with multiplicity).
] <cor:projective-modules-composition-factors>

#corollary[
  The determinant of the Cartan matrix is a power of $p$.
] <cor:cartan-determinant-arbitrary-field>

It should be pointed out that for an arbitrary $p$-modular system $(K,R,k)$ as
above, we do not obtain the equation $bold(C)=attach(bold(D), tl: t)bold(D)$,
nor even that $bold(C)$ is symmetric. For further discussion, see
@bib:CurtisReiner1962[CR §83A].

In §@ss:projective-lattice-characters, we give a detailed study of the image of
the map $K_0(R G)->G_0(K G)$ in the global case, where $R$ is a Dedekind domain
with quotient field $K$ of characteristic~0.

For the rest of this subsection, $E$ denotes an arbitrary field of
characteristic $p>0$, and $G$ a finite group. We shall prove a result due to
Witt @bib:Witt1952 and Berman @bib:Berman1956a, on the number of simple
$E G$-modules. The corresponding result for a field of characteristic zero is
given in Theorem~@th:field-character-conjugacy-classes. The Witt-Berman result
has been extended to twisted group algebras by Reynolds @bib:Reynolds1971. Our
proof follows Reiner @bib:Reiner1964, and is based on the theory of Brauer
characters.

Let $m$ be the exponent of $G$, and write $m=p^a m'$, where $p divides.not m'$.
Then the polynomial $X^(m')-1$ is separable over $E$, and the field $F$
generated from $E$ by the zeros of $X^(m')-1$ is a Galois extension of $E$, and
is a splitting field for $G$, by
Theorem~@th:sufficiently-large-field-splits-group. We have $F=E(tilde(omega))$,
where $tilde(omega)$ is a primitive $m'$-th root of~1 over $E$.

As in §@ss:witt-berman-induction, let $frak(G)$ be the Galois group of $F$ over
$E$, and define a monomorphism $sigma mapsto t$ from $frak(G)$ into a subgroup
$I_(m')(E)$ of $(ZZ slash m'ZZ)'$. If $sigma_t in frak(G)$ corresponds to
$t in I_(m')(E)$, then $sigma_(t)(tilde(omega))=tilde(omega)^t$.

Two elements $x,y in G_(p')$ are called _E-conjugate_ if $x=_G y^t$ for some
$t in I_(m')(E)$. Then $E$-conjugacy is an equivalence relation on $G_(p')$, and
its equivalence classes are called _p-regular E-conjugacy classes_.

The Witt-Berman Theorem can now be stated as follows:

#theorem[
  Let $G$ be a finite group, and let $E$ be an arbitrary field of characteristic
  $p>0$. Then the number of isomorphism classes of simple $E G$-modules is equal
  to the number of $p$-regular $E$-conjugacy classes of $G$.
] <th:modular-field-character-conjugacy-classes>
#idx(
  "Berman-Witt Theorem",
  target: [@th:modular-field-character-conjugacy-classes],
)
#idx(
  "Witt-Berman Theorem",
  target: [@th:modular-field-character-conjugacy-classes],
)

#source(531)
We first have to extend some of the results on Brauer characters from
§@sec:brauer-characters, in order to handle $E G$-modules. In
§@sec:brauer-characters, Brauer characters were defined for $k G$-modules, when
$k$ is part of a $p$-modular system, and $k$ is sufficiently large. For the more
general case of $E G$-modules, we make the following definition:

#definition[
  Let $E$ be an arbitrary field of characteristic $p>0$, and let $G$ be a finite
  group of exponent $m=p^a m'$, where $(p,m')=1$. Let
  $
    k_0="prime field of" E,
    quad k=k_0(tilde(omega)) subset.eq E(tilde(omega))=F,
  $
  where $tilde(omega)$ is a primitive $m'$-th root of unity over $E$. Then $k$
  is sufficiently large relative to $G$, and is part of a $p$-modular system
  $(K,R,k)$ in which $K$ is sufficiently large relative to $G$, and where $R$
  contains a primitive $m'$-th root of unity $omega$ such that
  $overline(omega)=tilde(omega)$, where bars denote reduction mod $frak(p)$.

  Now let $L$ be a left $E G$-module. For each $x in G_(p')$, the eigenvalues of
  the left multiplication $x_l$ on $L$ are powers of $tilde(omega)$, and lie in
  $k$. We then define the _Brauer character_ $lambda$ of $G$ afforded by $L$
  exactly as in @def:brauer-character. The resulting function $lambda$ is a
  $K$-valued class function defined on $G_(p')$. It is easily checked that
  statements (i)–(iii) of @prop:brauer-character-properties hold true for Brauer
  characters afforded by $E G$-modules.
] <def:brauer-character-arbitrary-field>
#idx("Brauer characters", target: [@def:brauer-character-arbitrary-field])
#idx("character", target: [@def:brauer-character-arbitrary-field])
#idx("character", "Brauer", target: [@def:brauer-character-arbitrary-field])

The preceding definition of Brauer characters clearly generalizes that given in
@def:brauer-character. It will be useful to have another interpretation of
Brauer characters afforded by $E G$-modules. Let ${M_i:1<=i<=r}$ be a basic set
of simple $k G$-modules, and let $mu_i$ be the Brauer character of $G$ afforded
by $M_i$, $1<=i<=r$. Since $k$ is sufficiently large relative to $G$, the
$F G$-modules ${F times.o_k M_i}$ are a basic set of simple $F G$-modules, and
the Brauer character afforded by $F times.o_k M_i$ is precisely $mu_i$,
$1<=i<=r$. On the other hand, starting with the $E G$-module $L$ with Brauer
character $lambda$, we may form the $F G$-module $F times.o_E L$, whose Brauer
character is also equal to $lambda$. By @prop:brauer-character-properties(iii),
the Brauer character of the module $F times.o_E L$ depends only on the
composition factors of the module. If $F times.o_k M_i$ occurs with multiplicity
$a_i$ as a composition factor of $F times.o_E L$, for $1<=i<=r$, then clearly we
have
$ lambda=sum_(i=1)^r a_i mu_i $ <eq:arbitrary-field-brauer-composition>
as class functions on $G_(p')$. The key idea in this discussion is the fact that
Brauer characters, as defined in @def:brauer-character-arbitrary-field, are
unchanged by ground field extension.

We need in addition the following fact:

#lemma[
  Let $H<=G$, and let $L$ be an $E H$-module affording the Brauer character
  $lambda$ of $H$. Then the induced $E G$-module $L^G$ has Brauer character
  $lambda^G$, where $lambda^G$ is the class function defined on $G_(p')$, as in
  @eq:induced-character-average.
] <lem:arbitrary-field-induced-brauer-character>
#idx(
  "character",
  "induced",
  target: [@lem:arbitrary-field-induced-brauer-character],
)
#idx(
  "induced character",
  target: [@lem:arbitrary-field-induced-brauer-character],
)

#source(532)
#proof[
  The result is an extension of Exercise~@exc:induced-brauer-character. Let
  ${N_i}$ be a basic set of simple $k H$-modules, and let $N_i$ afford the
  Brauer character $nu_i$ of $H$. By @eq:arbitrary-field-brauer-composition we
  obtain
  $ lambda^G=sum_i a_i nu_i^G $
  as class functions on $G_(p')$. By Exercise~@exc:induced-brauer-character,
  $nu_i^G$ is the Brauer character of $G$ afforded by $N_i^G$, and hence also by
  $F times.o_k N_i^G$. However, $F times.o_E L^G$ is isomorphic to
  $(F times.o_E L)^G$, and therefore has the same $F G$-composition factors as
  $product.co_(i=1)^r (F times.o_k N_i^G)^((a_i))$. It follows at once that the
  Brauer character of $G$ afforded by $F times.o_E L^G$ is precisely
  $sum a_i nu_i^G$. This shows that $L^G$ affords the Brauer character
  $lambda^G$, and the proof is completed.
]

We are now ready to proceed with the proof of
@th:modular-field-character-conjugacy-classes.

_Step 1._ Let ${X_i:1<=i<=u}$ be a basic set of simple $E G$-modules, and let
$chi_i$ be the Brauer character of $G$ afforded by $X_i$, $1<=i<=u$. These
${chi_i}$ are $K$-valued class functions on $G_(p')$, and we shall prove that
they are linearly independent over $K$. As in
@eq:arbitrary-field-brauer-composition, let ${mu_j}$ be a basic set of
irreducible Brauer characters of $G$. Then the ${mu_j}$ are linearly independent
over $K$ by @th:brauer-characters-class-function-basis, since $k$ is
sufficiently large relative to $G$. Now each $chi_i$ is expressible as a
$ZZ$-linear combination of the ${mu_j}$ by
@eq:arbitrary-field-brauer-composition. Further, a given $mu_j$ cannot occur in
both $chi_i$ and $chi_(i')$, where $i!=i'$, since by
Exercise~@exc:base-extension-common-composition-factor the $F G$-modules
$F times.o_E X_i$ and $F times.o_E X_(i')$ have no common composition factor.
This shows that the Brauer characters ${chi_i:1<=i<=u}$ can be expressed as
non-overlapping sums of the ${mu_j}$. Since the ${mu_j}$ are linearly
independent over $K$, so are the ${chi_i}$, as claimed.

_Step 2._ We show next that Brauer characters afforded by $E G$-modules are
constant on $E$-conjugacy classes in $G_(p')$. Let $chi$ be the Brauer character
of $G$ afforded by an $E G$-module $X$, and suppose that $a,b in G_(p')$ are
$E$-conjugate. Then we may write $g a g^(-1)=b^t$ for some $g in G$ and
$t in I_(m')(E)$. If $bold(X):G->M_(d)(E)$ is a matrix representation afforded
by $X$, then $bold(X)(a)$ and $bold(X)(b)$ have the same sets of eigenvalues,
and the eigenvalues of $bold(X)(b^t)$ are the $t$-th powers of those of
$bold(X)(b)$. However, since $bold(X)(b)$ has entries in $E$, the map
$tilde(omega) mapsto tilde(omega)^t$ defines an automorphism of $F$ which leaves
$bold(X)(b)$ fixed. It follows that $bold(X)(b)$ and $bold(X)(b^t)$ have the
same sets of eigenvalues, and hence $chi(a)=chi(b^t)=chi(b)$, as required.

_Step 3._ Let $a in G_(p')$, and let $A$ be the cyclic $p'$-group generated by
$a$. Let $J_a$ be the image of $I_(m')(E)$ in $(ZZ slash |A| ZZ)'$, with each
residue included once. Define a class function $theta:A->K$ by setting
$
  theta(a^t)=cases(
    |A| & t in J_a,
    0 & "otherwise".,
  )
$
Let us show that $theta$ is expressible as a $K$-linear combination of Brauer
#source(533)
characters of $A$ afforded by $E A$-modules. Since $A$ is a $p'$-group and $F$
is sufficiently large, we have $"Bch" F A="ch" K A$ by
@cor:prime-to-p-brauer-ordinary-characters. Now the Galois group $frak(G)$ of
$F$ relative to $E$ permutes the set of simple $F A$-modules, and the direct sum
over each orbit is the extension $F times.o_E L$ of some simple $E A$-module
$L$; this follows from the proof of
Exercise~@exc:cyclic-prime-to-p-unramified-decomposition, and also from
@cor:group-algebra-multiplicity-free-extension and
@prop:galois-orbit-simple-module-extension. Consequently, the Brauer character
of $A$ afforded by $L$ is the sum over a $frak(G)$-orbit of the Brauer
characters afforded by simple $F A$-modules.

By the first part of the proof of @lem:elementary-cyclic-orbit-indicator, the
above function $theta$ is a $K$-linear combination of irreducible characters
afforded by simple $K A$-modules, or equivalently, of irreducible Brauer
characters afforded by simple $F A$-modules. Further, the coefficients are
constant on the $frak(G)$-orbits of such $F A$-modules. This implies at once
that $theta$ is a $K$-linear combination of Brauer characters afforded by
$E A$-modules, as claimed.

_Step 4._ We can now complete the proof of the Witt-Berman
Theorem~@th:modular-field-character-conjugacy-classes. Let ${a_j:1<=j<=v}$ be
representatives of the $p$-regular $E$-conjugacy classes of $G$, and let
${chi_i:1<=i<=u}$ be a basic set of irreducible Brauer characters of $G$, as in
Step~1. Then the ${chi_i}$ are linearly independent over $K$ by Step~1, and they
are constant on the $E$-conjugacy classes of $G$ by Step~2. It follows that
$u<=v$.

Conversely, for each $a_j$, $1<=j<=v$, let $theta_j$ be the function constructed
in Step~3 for the cyclic group $chevron.l a_j chevron.r$. Since $theta_j$ is a
$K$-linear combination of Brauer characters afforded by
$E chevron.l a_j chevron.r$-modules, it follows from
@lem:arbitrary-field-induced-brauer-character that the induced class function
$theta_j^G$ is a $K$-linear combination of Brauer characters of $E G$-modules.
Hence each $theta_j^G$ is a $K$-linear combination of the ${chi_i}$. Once we
show that the class functions ${theta_j^G:1<=j<=v}$ are linearly independent
over $K$, it will then follow immediately that $v<=u$. From Step~2, the
characters ${theta_j^G}$ are constant on the $E$-conjugacy classes of $G$. It is
easily checked that $theta_j^(G)(a_j)!=0$, while $theta_j^(G)(a_l)=0$ if $l!=j$.
This implies that the ${theta_j^G}$ are linearly independent over $K$, and so
$v<=u$. This completes the proof of the theorem.

#exercises-heading

#exercise[
  Let $G=chevron.l x:x^n=1 chevron.r$ be a cyclic group of order $n$. For each
  $d$ dividing $n$, let $Phi_(d)(X)$ be the cyclotomic polynomial of order $d$,
  and let $zeta_d$ be a primitive $d$-th root of~1 over the rational field $QQ$.
  Show that the Wedderburn decomposition of $QQ G$ into simple components is
  given by
  $
    QQ G tilde.equiv product_(d divides n) QQ[X] slash (Phi_(d)(X))
    tilde.equiv product_(d divides n) QQ(zeta_d).
  $
  #hint([@exc:rational-cyclic-group-wedderburn])[
    As in the proof of @lem:elementary-cyclic-character-extension, we have
    $
      QQ G tilde.equiv QQ[X] slash (X^n-1),
      quad X^n-1=product_(d divides n) Phi_(d)(X).
    $
    Now use the results in §@ss:cyclotomic-fields.
  ]
] <exc:rational-cyclic-group-wedderburn>

#source(534)
#exercise[
  Let $G$ be as above, and let $K$ be any field such that $char K$ does not
  divide $|G|$. Find the Wedderburn decomposition of $K G$, and relate this to
  the results in @th:field-character-conjugacy-classes and
  @def:brauer-character-arbitrary-field.
] <exc:cyclic-group-field-wedderburn>

#exercise[
  Generalize Exercises~@exc:rational-cyclic-group-wedderburn and
  @exc:cyclic-group-field-wedderburn to the case where $G$ is a finite abelian
  group.
] <exc:abelian-group-field-wedderburn>

#exercise[
  Prove that the decomposition map $d:G_0(K G)->G_0(k G)$ need not be
  surjective, if $(K,R,k)$ is a $p$-modular system in which $R$ is not complete.
  #hint([@exc:incomplete-decomposition-map-not-surjective])[
    Let $p=5$, $K=QQ$, $R$ the ring of $5$-adic integers in $QQ$, and
    $k=ZZ slash 5ZZ$. Take $G$ to be the cyclic group of order~4. For another
    example, see the hint for Exercise~@exc:prime-to-p-projective-lifts.
  ]
] <exc:incomplete-decomposition-map-not-surjective>

#exercise[
  Let $(K,R,k)$ be a $p$-modular system in which $char K=0$ and $R$ is complete.
  Let $A=chevron.l a:a^m=1 chevron.r$ be cyclic, where $p divides.not m$. Show
  that the Wedderburn decomposition of the semisimple ring
  $ k A=product_i k_i,k_i="field", $
  lifts to a decomposition of $R$-algebras
  $ R A=product_i R_i,quad "where" R_i slash frak(p)R_i tilde.equiv k_i. $
  Further, if $K_i$ is the quotient field of $R_i$, show that $K_i$ is a Galois
  unramified extension of $K$ with valuation ring $R_i$, and that
  $ "Gal"(K_i slash K) tilde.equiv "Gal"(k_i slash k) quad "for each" i. $
  #hint([@exc:cyclic-prime-to-p-unramified-decomposition])[
    We have (since $p divides.not m$)
    $
      k A tilde.equiv k[y] slash (y^m-1)
      tilde.equiv product_i k_i,
      quad "where" k_i=k[y] slash (f_(i)(y)),
    $
    and where
    $
      y^m-1=product_i f_(i)(y),quad
      f_(i)(y) in k[y],quad f_(i)(y) "irreducible".
    $
    By Hensel's Lemma, this factorization lifts to a factorization
    $
      y^m-1=product_i g_(i)(y),quad
      g_(i)(y) in R[y],quad g_(i)(y) "irreducible",
    $
    with $overline(g_i)=f_i$ for each $i$.

    Keep $i$ fixed, and let $omega$ range over those $m$-th roots of~1 (in an
    algebraic closure of $K$) which are zeros of $g_(i)(x)$. Then $K_i=K(omega)$
    is unramified over $K$, and $R_i=R[omega]$ is its valuation ring. Further,
    $R_i slash frak(p)R_i tilde.equiv overline(R)[overline(omega)]
    =k(overline(omega))=k_i$, and $overline(omega)$ ranges over the zeros of
    $f_(i)(y)$. The correspondence $omega arrow.l.r overline(omega)$ gives the
    desired isomorphism of Galois groups. (For more details, see Weiss
    @bib:Weiss1963, section 3-2).
  ]
] <exc:cyclic-prime-to-p-unramified-decomposition>

#exercise[
  (Serre @bib:Serre1977). Show that $sum_(H in cal(E)) ("ch" K H)^G$ is properly
  contained in $"ch" K G$, in case $G=S_3$, $K=RR$, and $cal(E)$ is the family
  of elementary subgroups of $G$.
] <exc:real-elementary-induction-proper>
