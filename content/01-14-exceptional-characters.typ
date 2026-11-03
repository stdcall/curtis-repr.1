#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/14-exceptional-characters.typ": *

#heading(level: 2)[
  Special Classes and Exceptional Characters
] <sec:special-classes-exceptional-characters>

The results in the present section, and their applications, form a vein in group
theory which has perhaps released most of its treasures by now. Nevertheless,
this approach retains an elusive and fresh aspect which suggests that it may
#source(366)
yet provide new insights. The method, due to Brauer and Suzuki, involves an
extension of the character theory used in the proof of Frobenius' Theorem (see
§@ss:frobenius-groups), and is of extraordinary flexibility and strength. In the
past, it has been one of the key steps in the proofs of some major
classification theorems for finite simple groups.

This part of character theory, together with Brauer's work on blocks of
characters, constitute the central contribution of representation theory to the
theory of finite simple groups developed during the past two decades. There is a
vast literature devoted to this topic alone. Our account begins with the proof
of a theorem of Frobenius, where some of the essential ideas originated. This
application of character theory to finite group theory motivates the later
discussion, especially since all known proofs of Frobenius' Theorem rely on
character-theoretic methods. We shall then give Suzuki's~@bib:Suzuki1959
technique of exceptional characters, which was historically the first attempt to
describe the general method involved. Finally, we shall illustrate the
application of these results to finite group theory. For other applications of
exceptional characters and extensions of the method, see Feit~@bib:Feit1967,
Isaacs~@bib:Isaacs1976, Feit-Thompson~@bib:Feit1963, and articles on character
theory in the proceedings of symposia volumes (Madison and Santa Cruz) listed on
the first page of the Bibliography.

#heading(level: 3)[
  Frobenius Groups
] <ss:frobenius-groups>

#definition[
  A _Frobenius group_#idx("Frobenius group") is a finite group $G$ with a
  nontrivial subgroup $H$ such that
  $ H inter H^x=1,AA x in G-H. $
  The subgroup $H$ is called the _Frobenius complement_.#idx(
    "Frobenius complement",
  ) We shall show below that $G$ contains a normal subgroup $N$ such that
  $G=N H$ and $N inter H=1$; such an $N$ is called a _Frobenius kernel_ of
  $G$.#idx("Frobenius kernel")
] <def:frobenius-group>

Frobenius groups occur abundantly, the simplest example being the dihedral group
of order $2(2m+1)$:
$ D_(2m+1)=⟨ a,b:a^(2m+1)=b^2=(a b)^2=1 ⟩, $
with Frobenius complement $H=⟨ b ⟩$ and Frobenius kernel $N=⟨ a ⟩$. This example
illustrates the general fact that $(|G:H|,|H|)=1$ for $H$ a Frobenius complement
in the Frobenius group $G$. This result is an easy consequence of the Sylow
theorems and the fact that the center of a Sylow group is nontrivial.

The main theorem of this subsection is that in every Frobenius group, the
Frobenius kernel exists and is uniquely determined. The proof is based on the
character theory developed in §@ss:finite-group-character-orthogonality.

#source(367)
#theorem(title: [Frobenius])[
  Let $G$ be a Frobenius group with Frobenius complement $H$. Then there exists
  a unique Frobenius kernel $N$ in $G$.
] <th:frobenius-kernel>
#idx("Frobenius' Theorem", target: [@th:frobenius-kernel])
#proof[
  _Step 1._ Throughout this proof let $K$ be the complex field, $"ch"(K G)$ the
  ring of virtual complex characters of $G$, $"cf"(G)$ the ring of
  complex-valued class functions on $G$, and $"Irr"(G)$ the set of irreducible
  complex characters of $G$. Let $H$ be a Frobenius complement in the Frobenius
  group $G$, and set
  $ S=(G-union.big_(x in G) H^x) union {1}. $
  We shall show that $S$ is the desired Frobenius kernel, and begin by proving
  that $|S|=|G:H|$. Indeed, from the definition of Frobenius complement it
  follows that $H=N_G lr((H))$, so there are exactly $|G:H|$ distinct subgroups
  $H^x$. These have only the identity element in common, so $union_x H^x$
  consists of $1+|G:H|(|H|-1)$ elements. Therefore
  $ |S|=|G|-|G:H|(|H|-1)=|G:H|, $
  as claimed.

  We remark that if $G$ contains a Frobenius kernel $N$, then necessarily $N=S$.
  Indeed, if $N$ exists then $|N|=|G:H|=|S|$, and furthermore $N inter H^x=1$
  for all $x in G$ (since $N inter H=1$ and $N ⊴ G$), whence $N subset.eq S$.
  This shows that if $N$ exists, then $N$ is unique; the crux of the difficulty
  lies in proving that $S$ is indeed a subgroup of $G$.

  _Step 2._ Now let $theta in "cf"(H)$ be such that $theta(1)=0$, and let us
  show that $theta^G|_H=theta$. Clearly $theta^G lr((1))=|G:H|theta(1)=0$. On
  the other hand, let $h in H$, $h != 1$; then
  $ theta^G lr((h))=|H|^(-1)sum_(x in G) dot(theta) lr((x^(-1) h x)) $
  by @eq:induced-character-average. If $dot(theta) lr((x^(-1) h x)) != 0$ then
  $h^x != 1$ and $h^x in H inter H^x$. It follows that $x in H$, so
  $theta(x^(-1) h x)=theta(h)$ since $theta in "cf"(H)$. Thus
  $ theta^G lr((h))=|H|^(-1)sum_(x in H) theta(x^(-1) h x)=theta(h), $
  which proves that $theta^G|_H=theta$.

  _Step 3._ We show next that the map $theta -> theta^G$ gives an isometry from
  ${theta in "cf"(H):theta(1)=0}$ into $"cf"(G)$, where the isometry is with
  respect to the scalar products $(,)_H$ and $(,)_G$. Indeed, let
  $theta,eta in "cf"(H)$ be such that
  #source(368)
  $theta(1)=eta(1)=0$. Then Step 2 and the Frobenius Reciprocity
  Theorem~@th:frobenius-class-functions yield
  $ (theta^G,eta^G)_G=(theta^G|_H,eta)_H=(theta,eta)_H, $
  as desired.

  _Step 4._ To complete the proof of the theorem, we shall exhibit the
  above-defined set $S$ as an intersection of kernels of certain irreducible
  characters of $G$. Given $phi in "Irr"(H)$, let $theta=phi-phi(1)1_H$; then
  $theta in "cf"(H)$ and $theta(1)=0$. Since $theta in "ch"(K H)$, it follows
  that $theta^G in "ch"(K G)$. Setting
  $ phi^*=theta^G+phi(1)1_G, $
  we have also $phi^* in "ch"(K G)$. By Frobenius Reciprocity and Step 3, we
  obtain
  $
    norm(phi^*)_G^2 & =(phi^*,phi^*)_G
                      =(theta^G,theta^G)_G+2phi(1)(theta^G,1_G)+phi(1)^2 \
                    & =(theta,theta)_H+2phi(1)(theta,1_H)+phi(1)^2 \
                    & =(theta+phi(1)1_H,theta+phi(1)1_H)_H=(phi,phi)_H=1.
  $
  But $phi^* in "ch"(K G)$, so from $norm(phi^*)_G^2=1$ it follows that
  $plus.minus phi^* in "Irr"(G)$. However,
  $ phi^* lr((1))=theta^G lr((1))+phi(1)=phi(1)>0, $
  whence $phi^* in "Irr"(G)$. This shows that $phi^* in "Irr"(G)$ for every
  $phi in "Irr"(H)$. Note that
  $ (phi^*)_H=theta^G|_H+phi(1)1_H=theta+phi(1)1_H=phi. $
  Now set
  $ M=inter.big_(phi in "Irr"(H)) ker phi^*, $
  so $M ⊴ G$. If $h in M inter H$, then for all $phi in "Irr"(H)$ we have
  $ phi^* lr((1))=phi^* lr((h))=phi(h). $
  Thus $phi(h)=phi(1)$ for all $phi in "Irr"(H)$, so $h=1$ by
  Exercise~@exc:irreducible-character-kernel-intersection. This shows that
  $M inter H=1$, whence also $M inter H^x=1$ for all $x in G$ since $M ⊴ G$.
  Therefore $M subset.eq S$, where $S$ is as defined in Step 1. Conversely, if
  $g in S$, $g != 1$, then $g in.not H^x$ for all $x in G$, whence
  $theta^G lr((g))=0$ for each $theta$, by definition of induced characters. But
  then $phi^* lr((g))=phi^* lr((1))$ for each $phi$, so $g in M$. Thus $M=S$,
  and the preceding discussion gives $S ⊴ G$, $S inter H=1$, $G=S H$, and $S$ is
  the unique Frobenius kernel. This completes the proof of the theorem.
]

#source(369)
#corollary[
  Let $G$ be a finite group acting transitively on a finite set $X$, and assume
  that each element $g != 1$ in $G$ fixes at most one element of $X$. Then the
  set of elements of $G$ having no fixed points, together with the identity,
  forms a transitive normal subgroup $N$ of $G$.
] <cor:fixed-point-free-permutation-kernel>
#remark(numbered: false)[
  Let $chi$ be the character of the permutation representation of $G$ on $X$. In
  terms of $chi$, the hypothesis asserts that
  $ chi(g) <= 1,AA g in G,g != 1. $
  Then the transitive normal subgroup $N$ is defined by
  $ N={g in G:chi(g)=0} union {1}. $
]
#proof[
  Since $X$ is a transitive $G$-set, $X tilde.equiv G slash H$ as $G$-sets,
  where $H="Stab"_G lr((x_0))$ for some $x_0 in X$. If $H=1$, the action is
  regular and the conclusion holds with $N=G$. If $H=G$, then $X$ has one
  element and the conclusion holds with $N=1$. We may therefore assume $1<H<G$.
  An element $g in G$ fixes a coset $t H$ if and only if $g in t H t^(-1)$. Thus
  the hypothesis implies that $H^t inter H=1$ for all $t in G-H$, so $G$ is a
  Frobenius group with Frobenius complement $H$. The preceding remarks, together
  with Step 1 of the proof of @th:frobenius-kernel, show that the Frobenius
  kernel coincides with the subgroup described in the statement of the
  corollary. Finally, $N$ acts transitively on $X$ because $N H=G$ and
  $X tilde.equiv G slash H$.
]

Now that we have established the existence of the Frobenius kernel $N$ of a
Frobenius group $G$, we may use the results of §@ss:clifford-character-theory to
describe the character theory of $G$:

#proposition[
  Let $G$ be a Frobenius group with Frobenius kernel $N$. Then
  #enum(
    numbering: "(i)",
    [$C_G lr((n)) <= N$ for all $n in N$, $n != 1$.],
    [If $psi in "Irr"(N)$ is such that $psi != 1_N$, then $psi^G in "Irr"(G)$
      and $N ⊈ ker psi^G$. Conversely, each $zeta in "Irr"(G)$ such that
      $N ⊈ ker zeta$ can be expressed as $zeta=psi^G$ for some
      $psi in "Irr"(N)$, $psi != 1_N$.],
  )
] <prop:frobenius-group-characters>
#proof[
  It suffices to prove (i), since the remaining statements then follow from
  Theorem~@th:normal-self-centralizing-induction. Let $n in N$, $n != 1$, and
  suppose that $C_G lr((n)) ⊈ N$. By the characterization of $N$ in the proof of
  Theorem~@th:frobenius-kernel, we then have $C_G lr((n)) inter H^x != 1$ for
  some $x in G$. After conjugating by $x^(-1)$ and changing notation, we now
  have $C_G lr((n)) inter H != 1$ with $n in N$, $n != 1$. Let
  $h in C_G lr((n)) inter H$, $h != 1$; then $h in H inter H^n$, which
  contradicts the fact that $H$ is a Frobenius complement, and completes the
  proof.
]

For further discussion of Frobenius groups, see Feit~@bib:Feit1967 and
Isaacs~@bib:Isaacs1976.

#source(370)
#heading(level: 3)[
  Special Classes
] <ss:special-classes>

We shall describe a general situation where part of the character table of a
group $G$ can be determined from a corresponding part of the character table of
a subgroup. The method is due to Suzuki~@bib:Suzuki1959; our account follows an
exposition of Suzuki's work by G. Higman~@bib:Higman1968.

Throughout this subsection, $H$ denotes a subgroup of a finite group $G$. For
$x,y in G$, we write $x =_G y$ if $x=y^g$ for some $g in G$, and $x =_H y$ if
$x=y^h$ for some $h in H$. As in §@ss:frobenius-groups, $K$ denotes the complex
field.

#definition[
  A set of distinct conjugacy classes ${frak(S)_1,dots,frak(S)_n}$ of $H$, with
  representatives $h_i in frak(S)_i$, $1 <= i <= n$, is called a set of _special
  classes_ in $H$ provided that the following conditions hold:
  #idx("special classes")
  #enum(
    numbering: "(i)",
    [$C_G lr((h_i)) <= H$ for $1 <= i <= n$,],
    [$h_i !=_G h_j$ for $i != j$,],
    [If $⟨ h ⟩=⟨ h_j ⟩$, where $h in H$ and $1 <= j <= n$, then $h in frak(S)_i$
      for some $i$, $1 <= i <= n$, that is, $h$ is $H$-conjugate to some
      $h_i$.],
  )
] <def:special-classes>

Condition (ii) above asserts that the elements ${h_1,dots,h_n}$ belong to
distinct conjugacy classes in $G$, as well as in $H$. Condition (iii) is a sort
of completeness condition whose importance will become clear in the proof of
Lemma~@lem:special-class-virtual-character-basis.

Some additional notation is needed:
$
  frak(S)=frak(S)_1 union dots.c union frak(S)_n,
  "the union of the special classes,"
$
$
  "Irr"(H)={psi^1=1_H,psi^2,dots,psi^r},quad
  "Irr"(G)={zeta^1=1_G,zeta^2,dots,zeta^s},
$
$
  "ch"(K H)=sum ZZ psi^i,quad "ch"(K G)=sum ZZ zeta^i,
  "the rings of virtual"
$
characters on $H$ and $G$, respectively,
$
  W(frak(S))={phi in "cf"(H):phi|_(H-frak(S))=0},
  "the class functions on" H
$
vanishing off the special classes.

#lemma[
  $W(frak(S))$ has a $K$-basis consisting of $n$ virtual characters
  ${lambda_1,dots,lambda_n}$ in $"ch"(K H)$.
] <lem:special-class-virtual-character-basis>
#proof[
  Let ${h_(n+1),dots,h_r}$ be representatives of the $H$-conjugacy classes in
  $H-frak(S)$. A class function $sum_(i=1)^r x_i psi^i$, $x_i in K$, belongs to
  $W(frak(S))$ if and only if
  $ sum_(i=1)^r x_i psi^i lr((h_j))=0 quad "for" n+1 <= j <= r. $
  <eq:special-class-vanishing-equations>
  #source(371)
  If $W$ denotes the set of $r$-tuples $(x_1,dots,x_r)$ for which
  @eq:special-class-vanishing-equations holds, then the map
  $(x_1,dots,x_r) -> sum x_i psi^i$ gives a $K$-isomorphism
  $W tilde.equiv W(frak(S))$, since the ${psi^i}$ are linearly independent over
  $K$. Clearly $dim_K W=n$, since the $n$ characteristic functions on the
  special classes ${frak(S)_i}$ form a $K$-basis for $W(frak(S))$. We must show
  that $W$ has a $K$-basis of $r$-tuples with entries in $ZZ$.

  Let $xi$ be a primitive $|H|$-th root of $1$, $E=QQ(xi)$, and $G_(E slash QQ)$
  the Galois group of the Galois extension $E$ of $QQ$. For each
  $sigma in G_(E slash QQ)$ we have $sigma(xi)=xi^j$ for some integer $j$ such
  that $(j,|H|)=1$. Let $h in H$; since $psi^i lr((h))$ is a sum of powers of
  $xi$, it follows that
  $ sigma(psi^i lr((h)))=psi^i lr((h^j)) quad "for all" h in H, $
  <eq:character-galois-power-values>
  where $sigma(xi)=xi^j$ as above. Finally, we note that if $(j,|H|)=1$ then
  $⟨ h^j ⟩=⟨ h ⟩$ for all $h in H$.

  We show next that if $(j,|H|)=1$, then $h in H-frak(S)$ implies that also
  $h^j in H-frak(S)$. Indeed, we have $⟨ h ⟩=⟨ h^j ⟩$, so if $h^j in frak(S)$
  then also $h in frak(S)$ by condition (iii) of
  Definition~@def:special-classes. By virtue of
  @eq:character-galois-power-values, it follows that if $w=(x_1,dots,x_r) in W$,
  with each $x_i in E$, then also $sigma(w)=(sigma(x_1),dots,sigma(x_r)) in W$.

  Now the coefficients ${psi^i lr((h_j))}$ occurring in
  @eq:special-class-vanishing-equations all belong to $E$, so $W$ has a
  $K$-basis $w_1,dots,w_n$, with each $w_i$ an $r$-tuple having entries in $E$.
  We may further assume that the $n times r$ matrix with rows $w_1,dots,w_n$, is
  in reduced row echelon form, and that the first nonzero entry of each $w_i$
  equals $1$. Let $sigma in G_(E slash QQ)$; since $sigma(w_i) in W$ for each
  $i$, we can express $sigma(w_i)$ as an $E$-linear combination of
  $w_1,dots,w_n$. But then $sigma(w_i)=w_i$, by virtue of the echelon form. Thus
  $sigma(w_i)=w_i$ for all $i$ and all $sigma in G_(E slash QQ)$, whence each
  $w_i$ has entries in $QQ$. Clearing denominators, we then obtain a $K$-basis
  of $W$ in which the entries of the vectors all lie in $ZZ$, completing the
  proof.
]

We show next that condition (i) in Definition~@def:special-classes leads to a
generalization of the isometry described in Step 3 of the proof of
Theorem~@th:frobenius-kernel.

#lemma[
  Let $frak(S)$ be the union $union frak(S)_i$ of the special classes. If
  $x in G$ is such that $x frak(S) x^(-1) inter frak(S) != emptyset$, then
  $x in H$ and $x frak(S) x^(-1)=frak(S)$. For class functions
  $lambda,mu in "cf"(H)$ which vanish off the special classes, we have
  $ lambda^G|_H=lambda,quad "and" quad (lambda^G,mu^G)_G=(lambda,mu)_H. $
] <lem:special-class-induction-isometry>
#proof[
  Let $x frak(S) x^(-1) inter frak(S) != emptyset$, where $x in G$. After
  multiplying $x$ on the left and right by elements of $H$, we may assume that
  $x h_i x^(-1)=h_j$, for some $i,j$, $1 <= i,j <= n$. By condition (ii) of
  Definition~@def:special-classes, we have $i=j$, and hence by (i) we have
  $x in H$. Therefore $x frak(S) x^(-1)=frak(S)$ because $frak(S)$ is a union of
  $H$-conjugacy classes. The rest of the proof is exactly the same as Steps 2
  and 3 in the proof of Theorem~@th:frobenius-kernel.
]

#source(372)
We now introduce some additional notation. Recalling that
$"Irr"(H)={psi^1,psi^2,dots,psi^r}$, we write the ${lambda_i}$ in
@lem:special-class-virtual-character-basis as
$ lambda_i=sum a_(i j) psi^j,a_(i j) in ZZ, $
for some uniquely determined $n times r$ matrix $upright(bold(A))=(a_(i j))$
over $ZZ$. Similarly, the induced virtual characters $lambda_i^G$ can be
expressed in terms of the characters ${zeta^1,dots,zeta^s}$ in $"Irr"(G)$, say
$ lambda_i^G=sum b_(i j) zeta^j,b_(i j) in ZZ, $
for an $n times s$ matrix $upright(bold(B))=(b_(i j))$ over $ZZ$.

#lemma[
  #enum(
    numbering: "(i)",
    [$b_(i 1)=a_(i 1)$, $1 <= i <= n$.],
    [$sum_(k=1)^s b_(i k)b_(j k)=sum_(k=1)^r a_(i k)a_(j k)$ for
      $1 <= i,j <= n$, that is,
      $upright(bold(B)) dot attach(upright(bold(B)), tl: t)
      =upright(bold(A)) dot attach(upright(bold(A)), tl: t)$.],
    [$sum_(i=1)^s zeta^i lr((h_j))zeta^i lr((h_k))
      =sum_(i=1)^r psi^i lr((h_j))psi^i lr((h_k))$, $1 <= j,k <= n$.],
    [$sum_(j=1)^s b_(i j) zeta^j lr((h_k))
      =sum_(j=1)^r a_(i j) psi^j lr((h_k))$, $1 <= k <= n$.],
  )
] <lem:special-class-character-coefficients>
#proof[
  (i) Recalling that $zeta^1=1_G$ and $psi^1=1_H$, we have
  $ (lambda_i,psi^1)=(lambda_i^G,zeta^1),1 <= i <= n, $
  by Frobenius Reciprocity, whence $a_(i 1)=b_(i 1)$.

  (ii) For $1 <= i,j <= n$, $lambda_i$ and $lambda_j$ vanish off the special
  classes, hence by Lemma~@lem:special-class-induction-isometry we have
  $ (lambda_i^G,lambda_j^G)=(lambda_i,lambda_j). $
  Statement (ii) now follows from the definitions of the matrices
  $upright(bold(A))$ and $upright(bold(B))$, and the orthogonality relations in
  $"cf"(H)$ and $"cf"(G)$.

  (iii) This result is immediate from the Second Orthogonality Relation
  @prop:first-second-character-orthogonality(ii), using conditions (i) and (ii)
  of Definition~@def:special-classes.

  (iv) We have $lambda_i^G=sum b_(i j) zeta^j$, and $lambda_i^G|_H=lambda_i$, by
  Lemma~@lem:special-class-induction-isometry. In particular,
  $lambda_i^G lr((h_k))=lambda_i lr((h_k))$ for $1 <= k <= n$, which implies
  (iv), and completes the proof of the lemma.
]

#source(373)
The main result of this subsection is that from the information in Lemma
@lem:special-class-character-coefficients, it is possible (in a certain sense)
to solve the equations
$
  sum zeta^i lr((h_j)) zeta^i lr((h_k))
  =sum psi^i lr((h_j)) psi^i lr((h_k))
$
for the character values $zeta^i lr((h_j))$, thus giving that part of the
character table of $G$ which involves the character values on the classes in $G$
arising from the special classes in $H$.

#theorem(title: [Suzuki])[
  There exist uniquely determined elements ${c_(j k)}$ of $K$, $1 <= j,k <= n$,
  such that
  $ psi^i lr((h_j))=sum_(k=1)^n c_(j k) a_(k i). $
  For these elements ${c_(j k)}$, we have
  $ zeta^i lr((h_j))=sum_(k=1)^n c_(j k) b_(k i). $
  In other words, there exists an $n times n$ matrix $upright(bold(C))$ such
  that
  $ attach(lr((psi^i lr((h_j)))), tl: t)=upright(bold(C)) upright(bold(A)), $
  and for this matrix we have
  $ attach(lr((zeta^i lr((h_j)))), tl: t)=upright(bold(C)) upright(bold(B)). $
] <th:suzuki-special-class-character-values>
#idx("Suzuki's Theorem", target: [@th:suzuki-special-class-character-values])
#proof[
  For each $j$, $sum_i psi^i lr((h_j)) psi^i$ vanishes off the special classes,
  by the Second Orthogonality Relation for $H$. Since ${lambda_1,dots,lambda_n}$
  are a basis for $W(frak(S))$, we therefore have
  $ sum_i psi^i lr((h_j)) psi^i=sum_k c_(j k) lambda_k, $
  for some uniquely determined elements $c_(j k) in K$. Moreover, expressing the
  ${lambda_k}$ in terms of the $psi^i$, we have
  $
    sum_k c_(j k) lr((sum_i a_(k i) psi^i))
    =sum_i lr((sum_k c_(j k) a_(k i))) psi^i.
  $
  Comparing coefficients of the ${psi^i}$ we obtain
  $ psi^i lr((h_j))=sum_(k=1)^n c_(j k) a_(k i), $
  which is the first assertion of the theorem.

  #source(374)
  For the second, we first verify that equations
  @lem:special-class-character-coefficients(iv) hold when the
  ${zeta^i lr((h_j))}$ are replaced by $sum_(k=1)^n c_(j k) b_(k i)$. We have
  $
    sum_(j=1)^s b_(i j) sum_(l=1)^n c_(k l) b_(l j)
    &=sum_(l=1)^n c_(k l) lr((sum_(j=1)^s b_(i j) b_(l j)))
    =sum_(l=1)^n c_(k l) lr((sum_(j=1)^r a_(i j) a_(l j)))
    \
    &=sum_(j=1)^r a_(i j) lr((sum_(l=1)^n c_(k l) a_(l j)))
    =sum_(j=1)^r a_(i j) psi^j lr((h_k)),
  $
  using Lemma @lem:special-class-character-coefficients(ii). This means that if
  we set
  $
    zeta^i lr((h_j))=sum_(k=1)^n c_(j k) b_(k i)+epsilon_(i j),
    quad 1 <= i <= s, 1 <= j <= n,
  $
  then we have
  $
    sum_(j=1)^s b_(i j) epsilon_(j k)=0
    quad "for" 1 <= i <= n, 1 <= k <= n.
  $
  <eq:special-class-error-orthogonality>
  Substituting in the left hand side of Lemma
  @lem:special-class-character-coefficients(iii) we obtain
  $
    sum_(i=1)^s zeta^i lr((h_j)) zeta^i lr((h_k))
    =sum_(i=1)^s lr({sum_(p=1)^n c_(j p) b_(p i)+epsilon_(i j)})
    lr({sum_(q=1)^n c_(k q) b_(q i)+epsilon_(i k)}).
  $
  For the “cross terms” we have
  $ sum_(i=1)^s epsilon_(i j) lr({sum_(q=1)^n c_(k q) b_(q i)})=0 $
  by @eq:special-class-error-orthogonality, and similarly
  $ sum_(i=1)^s sum_(p=1)^n c_(j p) b_(p i) epsilon_(i k)=0. $
  For the “leading terms” we have by
  @lem:special-class-character-coefficients(ii),
  $
    sum_i sum_p sum_q c_(j p) b_(p i) c_(k q) b_(q i)
    =sum_(p,q) c_(j p) c_(k q) sum_(i=1)^s b_(p i) b_(q i)
    =sum_(p,q) c_(j p) c_(k q) sum_(l=1)^r a_(p l) a_(q l)
    =sum_(i=1)^r psi^i lr((h_j)) psi^i lr((h_k)),
  $
  #source(375)
  which is the right hand side of
  @lem:special-class-character-coefficients(iii). Therefore
  $
    sum_(i=1)^s epsilon_(i j) epsilon_(i k)=0,
    quad "for" 1 <= j,k <= n.
  $
  Finally, if $h_k =_H h_j^(-1)$, then
  $
    psi^i lr((h_k))=sum_(p=1)^n c_(k p) a_(p i)
    =overline(psi^i lr((h_j)))
    =overline(sum_p c_(j p) a_(p i))
    =sum_p overline(c_(j p)) a_(p i),
  $
  and hence $c_(k p)=overline(c_(j p))$ for all $p$. It follows that
  $
    zeta^i lr((h_k))=sum_p c_(k p) b_(p i)+epsilon_(i k)
    =overline(zeta^i lr((h_j)))
    =overline(sum_p c_(j p) b_(p i)+epsilon_(i j)),
  $
  and hence $epsilon_(i k)=overline(epsilon_(i j))$. Therefore
  $ sum_i |epsilon_(i j)|^2=0 $
  for all $j$, $1 <= j <= n$, and hence $epsilon_(i j)=0$ for all $i$ and $j$.
  This completes the proof of Theorem @th:suzuki-special-class-character-values.
]

#heading(level: 3)[
  Exceptional Characters. Suzuki’s CA-Group Theorem
] <ss:exceptional-characters-ca-groups>

In applications to the classification of finite non-abelian simple groups, the
theory of special classes and exceptional characters (see @def:special-classes
and @def:exceptional-characters) has typically been used to investigate the
structure of simple groups in some minimal situation. In these cases, the
possibilities for a purely group-theoretic analysis are limited because of the
relatively small number of subgroups to interact with one another. In this
subsection, we shall prove a result of Suzuki~@bib:Suzuki1957 dealing with one
of these minimal situations.

#definition[
  A finite group $G$ is called a _CA-group_ (for “abelian centralizer”) if the
  centralizer of every element $x in G-{1}$ is abelian.
] <def:ca-group>
#idx("CA-group", target: [@def:ca-group])

#theorem(title: [Suzuki])[
  Every finite simple non-abelian CA-group has even order.
] <th:suzuki-ca-group-even-order>
#idx("Suzuki's Theorem", target: [@th:suzuki-ca-group-even-order])

The preceding theorem is of course a special case of the Feit-Thompson Theorem
(Feit-Thompson~@bib:Feit1963), which asserts that every non-abelian simple group
has even order. Historically, Suzuki’s Theorem @th:suzuki-ca-group-even-order
was followed by a theorem on the non-existence of simple CN-groups of odd order
(Feit-Hall-Thompson~@bib:Feit1960), where a CN-group is defined as in
@def:ca-group, with “abelian”
#source(376)
replaced by “nilpotent.” These theorems were a part of the chain of results
leading to the Feit-Thompson Theorem. The CA-groups also are interesting from
the standpoint of classifying the known simple groups.
Brauer-Suzuki-Wall~@bib:Brauer1958 proved that every non-abelian simple CA-group
of even order is isomorphic to a fractional linear group $op("PSL")_2 lr((2^a))$
over a finite field of characteristic $2$.

The proof of @th:suzuki-ca-group-even-order begins with the following
observation, whose proof is immediate from the definitions:

#lemma(name: none)[
  Every maximal abelian subgroup $A$ of a CA-group $G$ has the property:
  $ A=C_G lr((a)) quad forall a in A, a!=1. $
] <lem:ca-maximal-abelian-centralizers>

An abelian subgroup $A$ of a finite group $G$ satisfying the condition of
@lem:ca-maximal-abelian-centralizers is called a _special abelian subgroup_, or
an _SA-subgroup_.
#idx("SA-group")
Besides occurring in CA-groups, special abelian subgroups may be present in
other finite groups which are not CA-groups; for example, a Sylow $p$-subgroup
in $op("PSL")_2 lr((p))$ is an SA-subgroup, for $p$ odd.

As preparation for the proof of @th:suzuki-ca-group-even-order, and for its
intrinsic interest as well, we begin with a discussion of the character theory
of a group which contains an SA-subgroup.

#definition[
  A subset $S$ of a finite group $G$ is called a _T.I. set_ (_trivial
  intersection set_) if
  $
    S subset.eq N_G lr((S)) quad "and" quad S inter S^x subset.eq {1}
    quad "for all" x in G-N_G lr((S)).
  $
] <def:trivial-intersection-set>
#idx(
  "T. I. (trivial intersection) set",
  target: [@def:trivial-intersection-set],
)
#idx("trivial intersection set", target: [@def:trivial-intersection-set])

(For example, it follows from §@ss:frobenius-groups that a Frobenius complement
$H$ in a Frobenius group $G$ is a T.I. set in $G$. It follows from
@lem:special-class-induction-isometry that the union of a set of special classes
(see @def:special-classes) is always a T.I. set.)

#proposition[
  Let $A$ be an SA-subgroup of a finite group $G$. Let
  $ H=N_G lr((A)), A^*=A-{1}, $
  and set
  $ m=|A|, quad e=|H:A|, n=(m-1) slash e. $
  Then the following statements hold:

  (i) The subset $A^*$ is a T.I. set in $G$, with normalizer $H$. If $H>A$, then
  $H$ is a Frobenius group with Frobenius kernel $A$.

  (ii) The index $e=|H:A|$ divides $m-1$, and $A^*$ is the union of exactly $n$
  distinct conjugacy classes of $H$. These are a set of special classes in $H$
  (see Definition @def:special-classes).

  #source(377)
  (iii) As $xi$ ranges over the non-trivial linear characters of $A$, the
  induced characters $xi^H$ give irreducible characters of $H$ of degree $e$,
  which vanish on $H-A$. There are precisely $n$ distinct irreducible characters
  ${psi_1,dots,psi_n}$ in this collection ${xi^H}$.

  (iv) Assume $n >= 2$, and let
  $ lambda_i=psi_i-psi_n, 1 <= i <= n-1, $
  so each $lambda_i$ is a virtual character of $H$. These ${lambda_i}$, together
  with any one virtual character $1_A^H-psi_i$, where $1 <= i <= n$, form a
  $ZZ$-basis for the set of virtual characters of $H$ vanishing off $A^*$. There
  exists a sign $epsilon=plus.minus 1$, and distinct non-trivial irreducible
  characters of $G$:
  $ {zeta_1,dots,zeta_n; theta_1,dots,theta_f}, $
  satisfying the conditions:
  $
    cases(
      (psi_i-psi_j)^G=epsilon(zeta_i-zeta_j) comma 1 <= i comma j <= n,
      psi_i^G=epsilon zeta_i+Delta
      quad "for some virtual character" Delta comma 1 <= i <= n,
      (1_A^H-psi_i)^G=1_G-epsilon zeta_i+a sum_(l=1)^n zeta_l
      +sum_(j=1)^f c_j theta_j comma 1 <= i <= n,
    )
  $
  where the virtual character $Delta$ and the integers $a$ and ${c_j}$ are
  independent of $i$.
] <prop:sa-subgroup-special-classes>
#proof[
  To establish (i), let $a in A inter A^x$, $a!=1$, for some element $x in G$.
  Then $C_G lr((a))$ contains both $A$ and $A^x$. From the assumption that $A$
  is an SA-subgroup of $G$, it follows that $A=A^x$ and $x in H$. Therefore
  $A^*$ is a T.I. set in $G$, with normalizer $H$.

  If $H=A$, then $H$ is abelian and the character statement (iii) follows
  directly; the proof of (iv) below applies unchanged. We now prove the
  Frobenius assertion in (i) under the additional assumption $H>A$, and begin by
  showing that $|A|$ is relatively prime to $|H:A|$. Let $p$ be a prime dividing
  $|A|$, and let $S$ be a Sylow $p$-subgroup of $H$. Then $S inter A!=1$. Since
  the center $Z(S)$ of $S$ centralizes each element of $S inter A$, and $A$ is
  an SA-group, it follows that $Z(S) <= A$. But $Z(S)!=1$, and $S$ centralizes
  each element of $Z(S)$, so $S <= A$. It follows that $|A|$ and $|H:A|$ are
  relatively prime.

  By the Schur-Zassenhaus Theorem @th:schur-zassenhaus, we have $H=A times.r B$
  for some subgroup $B$, and it now suffices to show that $B$ is a Frobenius
  complement in $H$. Since $H=A B$, it is enough to prove that if
  $B inter B^a!=1$ for some $a in A$, then $a=1$. Suppose that
  $b in B inter B^(a^(-1))$, where $a in A$, $a!=1$. Then $b=a b_1 a^(-1)$ for
  some $b_1 in B$, and hence $a b_1=b a$. Then $b_1^(-1) a b_1=b_1^(-1) b a$, so
  $b_1^(-1) b in A inter B=1$. Thus $b=b_1$, and
  $b in C_H lr((a)) inter B=A inter B=1$, by the SA-hypothesis, completing the
  proof of (i).

  #source(378)
  (ii) From the proof of (i), it follows that if two elements of $A$ are
  conjugate in $G$, then they are conjugate in $H$. Since $A^*$ is a union of
  conjugacy classes of $H$, it is clear from what has been shown above that
  these $H$-conjugacy classes (whose union is $A^*$) form a set of special
  classes in $H$, according to @def:special-classes. (Note that
  @def:special-classes(iii) holds trivially, since if $h in H$ and $⟨h⟩=⟨a⟩$ for
  some $a in A^*$, then also $h in A^*$, so $h$ is contained in some special
  class.) Moreover, $C_G lr((a))=A$ for each $a in A^*$, and it follows that
  each $H$-conjugacy class in $A^*$ contains $e=|H:A|$ elements. Therefore $e$
  divides $m-1$, and there are exactly $(m-1) slash e$ special classes in $A^*$.

  (iii) The set of nontrivial linear characters of $A$ can be written as a
  disjoint union of $H$-orbits. By @cor:brauer-conjugacy-orbits the number of
  such $H$-orbits is the same as the number of $H$-conjugacy classes in $A^*$,
  which is $n$. The characters of $H$ induced from representatives of these
  orbits are irreducible by @prop:frobenius-group-characters, and distinct by
  the Intertwining Number Theorem @th:intertwining-number. This completes the
  proof of (iii).

  (iv) The first statement is clear from the properties of the characters
  ${psi_i:1 <= i <= n}$ established in (iii). Since $n >= 2$, there are $n-1>0$
  virtual characters of $H$,
  $ psi_1-psi_n,dots,psi_(n-1)-psi_n, $
  vanishing off $A^*$. By @lem:special-class-induction-isometry we
  have#footnote[
    As in @prop:character-scalar-products-multiplicities(ii), for each class
    function $mu$ we denote $(mu,mu)$ by $norm(mu)^2$.
  ]
  $ norm((psi_i-psi_n)^G)^2=norm(psi_i-psi_n)^2=2, 1 <= i <= n-1. $
  Thus $(psi_i-psi_n)^G$ contains two distinct irreducible characters of $G$,
  each with multiplicity $plus.minus 1$. It also follows from
  @lem:special-class-induction-isometry that
  $ (psi_i-psi_n)^G lr((1))=(psi_i-psi_n)(1)=0, $
  since the characters ${psi_i}$ all have the same degree, by part (iii).
  Therefore the multiplicities of the characters of $G$ appearing in
  $(psi_i-psi_n)^G$ have opposite signs. Since, by
  @lem:special-class-induction-isometry,
  $
    lr(((psi_i-psi_n)^G,(psi_j-psi_n)^G))
    =(psi_i-psi_n,psi_j-psi_n)=1
  $
  if $i<j<n$, it is easily checked that there exists a fixed sign
  $epsilon=plus.minus 1$, and exactly $n$ irreducible characters
  ${zeta_1,dots,zeta_n}$ of $G$, such that
  $ (psi_i-psi_j)^G=epsilon(zeta_i-zeta_j),1 <= i,j <= n. $

  #source(379)
  From these relations we obtain
  $ psi_i^G-epsilon zeta_i=psi_j^G-epsilon zeta_j,1 <= i,j <= n. $
  Hence
  $ psi_i^G=epsilon zeta_i+Delta, $
  where $Delta$ is a virtual character independent of $i$. In particular,
  $Delta$ contains the characters ${zeta_i}$ with equal multiplicities.
  Moreover, by @lem:special-class-induction-isometry we have
  $
    (1_A^G,zeta_i-zeta_j)
    =epsilon lr((1_A^G,(psi_i-psi_j)^G))
    =epsilon lr((1_A^H,psi_i-psi_j))=0,
  $
  so the characters ${zeta_i}$ also appear with equal multiplicities in $1_A^G$.
  Combining our results, we obtain the last statement of (iv), and the proof is
  completed.
]

From now on, we assume that $n >= 2$, as in (iv) of the preceding result.

#definition[
  The characters ${zeta_1,dots,zeta_n}$ appearing in
  @prop:sa-subgroup-special-classes(iv) are called the _exceptional characters_
  associated with the SA-subgroup $A$. The remaining non-trivial irreducible
  characters of $G$ are called _non-exceptional characters_ relative to $A$.
] <def:exceptional-characters>
#idx("character", "exceptional", target: [@def:exceptional-characters])
#idx("exceptional character", target: [@def:exceptional-characters])
#idx("character", "non-exceptional", target: [@def:exceptional-characters])
#idx("non-exceptional character", target: [@def:exceptional-characters])

The next result contains detailed information about the values of the
exceptional and non-exceptional characters; this information will be used in the
proof of Suzuki’s Theorem @th:suzuki-ca-group-even-order. Even more precise
information will be obtained later, in
§@ss:green-correspondence-character-applications, as an application of modular
representation theory.

#proposition[
  Let ${zeta_1,dots,zeta_n;theta_1,dots,theta_f}$, $n >= 2$, be the exceptional
  and non-exceptional characters associated with the subgroup $A$, as in
  @prop:sa-subgroup-special-classes. Then the following statements hold:

  (i) $zeta_i lr((x))=zeta_j lr((x))$, $1 <= i,j <= n$, for each $x in G$ not
  conjugate to an element of $A^*$. In particular, the exceptional characters
  all have the same degree.

  (ii) If $B$ is another SA-subgroup of $G$, not conjugate to $A$, then
  ${zeta_1,dots,zeta_n}$ are non-exceptional characters relative to $B$.

  (iii) The multiplicities $a$ and ${c_j}_(1 <= j <= f)$ in the expression
  $
    (1_A^H-psi_i)^G=1_G-epsilon zeta_i+a sum_(l=1)^n zeta_l
    +sum_(j=1)^f c_j theta_j
  $
  satisfy the condition:
  $ e=a^2(n-1)+(a-epsilon)^2+sum_(j=1)^f c_j^2. $

  #source(380)
  (iv) Each non-exceptional character $theta_j$, $1 <= j <= f$, takes constant
  rational integral values on the special classes in $A^*$. More precisely,
  $ theta_j lr((x))=c_j, quad forall x in A^*, $
  where $c_j$ is the multiplicity of $theta_j$ in $(1_A^H-psi_i)^G$. The
  multiplicity $c_j$ is characterized by the condition
  $
    c_j equiv theta_j lr((1)) quad ("mod" m),
    quad |c_j| <= 1/2 (m-1).
  $
  In particular, $theta_j$ vanishes on $A^*$ if and only if $m$ divides
  $theta_j lr((1))$.

  (v) If $theta_j$ and $theta_(j')$ are non-exceptional characters with the same
  degree, then they appear with equal multiplicities in $(1_A^H-psi_i)^G$ for
  each $i$, $1 <= i <= n$.

  (vi) We have $sum_(x in A^*) |zeta_i lr((x))|^2 >= e(m-e)$.
] <prop:exceptional-character-values>
#proof[
  (i) By @prop:sa-subgroup-special-classes(iv), we have
  $ zeta_i-zeta_j=epsilon(psi_i-psi_j)^G,1 <= i,j <= n. $
  By the definition of the characters ${psi_i}$, it follows that $zeta_i-zeta_j$
  vanishes on all $x in G$ not conjugate to some element of $A^*$.

  (ii) If $B$ is a special abelian group not conjugate to $A$, then
  $B inter A=1$. Therefore by (i), $zeta_i-zeta_j$ vanishes on $B^*$ for
  $1 <= i,j <= n$. Hence if one character $zeta_i$ is exceptional relative to
  $B$, all characters ${zeta_j}_(1 <= j <= n)$ have this property, by
  @prop:sa-subgroup-special-classes(iv). By (i), this implies that
  $zeta_i=zeta_j$ for all $i$ and $j$, contrary to the assumption $n >= 2$.

  (iii) By @prop:sa-subgroup-special-classes(iv), $1_A^H-psi_i$ vanishes off the
  special classes, so by @lem:special-class-induction-isometry we have
  $ norm((1_A^H-psi_i)^G)_G=norm(1_A^H-psi_i)_H,1 <= i <= n. $
  Moreover, $1_A^H$ is the regular character of $H slash A$, and does not
  contain $psi_i$. Therefore
  $ norm((1_A^H-psi_i)^G)^2=1+|H:A|=1+e. $
  Using the expression of $(1_A^H-psi_i)^G$ in terms of the exceptional and
  non-exceptional characters, we obtain
  $ norm((1_A^H-psi_i)^G)^2=1+(a-epsilon)^2+a^2(n-1)+sum_(j=1)^f c_j^2. $

  #source(381)
  Assertion (iii) follows at once from comparing these two formulas for
  $norm((1_A^H-psi_i)^G)^2$.

  (iv) and (v) Let $xi$ be a nontrivial linear character of $A$. Then $xi^G$
  coincides with $psi_i^G$ for some $i$. If $theta$ is a non-exceptional
  character of $G$ relative to $A$, then $theta$ is contained in all ${psi_i^G}$
  with the same multiplicity, say $alpha$. If the multiplicity of $theta$ in
  $1_A^G$ is $beta$, then $(1_A^H-psi_i)^G$ contains $theta$ with multiplicity
  $beta-alpha$. By Frobenius Reciprocity, we also have
  $ theta|_A=beta 1_A+alpha(sum xi), $
  where the sum is taken over the nontrivial linear characters $xi$ of the
  abelian group $A$. Comparing degrees, we obtain
  $ theta(1)=beta+alpha(m-1) equiv (beta-alpha) quad ("mod" m). $
  Moreover, the Second Orthogonality Relation gives
  $ (1_A+sum xi)(x)=0, forall x in A^*. $
  We conclude that
  $ theta(x)=beta-alpha in ZZ, forall x in A^*. $
  Finally,
  $ |c_j| <= |c_j|^2 <= e <= (m-1) slash 2, 1 <= j <= f, $
  since $n >= 2$. This completes the proof of (iv) and (v).

  (vi) We first apply an argument, similar to the preceding one, to the
  exceptional characters ${zeta_i}$. If $zeta_i$ is exceptional, then for
  $j!=i$, it follows from @prop:sa-subgroup-special-classes(iv) that $zeta_i$
  appears with constant multiplicity, say $alpha$, in $psi_j^G$. Again using
  @prop:sa-subgroup-special-classes(iv), we have
  $(zeta_i,psi_i^G)=alpha+epsilon$. Letting $beta=(zeta_i,1_A^G)$, it follows
  easily that
  $ zeta_i|_A=beta 1_A+alpha sum xi+epsilon sum xi', $
  where the first sum is taken over all nontrivial linear characters $xi$ of
  $A$, and the second over the linear characters $xi'$ appearing in $psi_i|_A$.
  By the Second Orthogonality Relation, $(1_A+sum xi)(x)=0$ for all $x in A^*$,
  and it follows that
  $
    zeta_i lr((x))=beta-alpha+epsilon psi_i lr((x)),
    forall x in A^*, 1 <= i <= n.
  $
  Thus $zeta_i lr((x))=epsilon psi_i lr((x))+z$, for some integer $z$, and all
  $x in A^*$. We then have
  $
    & sum_(x in A^*) |zeta_i lr((x))|^2 \
    & =sum_(x in A^*) (epsilon psi_i lr((x))+z)
      (epsilon psi_i lr((x^(-1)))+z) \
    & =sum_(x in A^*) |psi_i lr((x))|^2
      +epsilon z sum_(x in A^*)
      (psi_i lr((x))+psi_i lr((x^(-1))))+(m-1)z^2 \
    & =m e-e^2-2 epsilon z e+z^2(m-1).
  $
  #source(382)
  (We have used the fact that $sum_(x in A^*) psi_i lr((x))=-psi_i lr((1))=-e$,
  because the restriction of $psi_i$ to $A$ is a sum of nontrivial linear
  characters of $A$.) It follows that
  $ sum_(x in A^*) |zeta_i lr((x))|^2 >= e(m-e), $
  since $m-1=e n$, and $z^2 n-2 epsilon z >= 0$ for $n >= 2$ and any integer
  $z$. This completes the proof of the proposition.
]

#remark(numbered: false)[
  The proofs of parts (iv)–(vi) are especially interesting, in that they use
  information about multiplicities to derive character values.
]

#proof(head: [#emph[Proof of Suzuki’s CA-group Theorem]
  @th:suzuki-ca-group-even-order.])[
  We assume that $G$ is a non-abelian simple CA-group. Then each maximal abelian
  subgroup of $G$ is a special abelian subgroup, as we have remarked earlier. We
  have already used the fact that if $A$ and $B$ are two SA-subgroups such that
  $A inter B!=1$, then both $A$ and $B$ are contained in the centralizer of any
  non-identity element of their intersection, and hence coincide. Thus each
  non-identity element of $G$ lies in exactly one maximal abelian subgroup of
  $G$. These maximal abelian subgroups, in turn, may be partitioned into classes
  of conjugate SA-subgroups, with representatives ${A_1,dots,A_t}$. We set
  $H_i=N_G lr((A_i))$, and let
  $ |A_i|=m_i, |H_i:A_i|=e_i, 1 <= i <= t. $
  Then $n_i=(m_i-1) slash e_i$ is an integer, for each $i$.

  We wish to show that $|G|$ is even, so suppose instead that $|G|$ is odd. From
  this assumption, it follows that each $n_i$ is even, since $n_i e_i=m_i-1$ is
  even and $e_i$ is odd. Thus $n_i >= 2$ for each $i$, and the results of the
  preceding two propositions can be applied to each of the subgroups
  ${A_1,dots,A_t}$.

  By @prop:sa-subgroup-special-classes, there exist exactly $n_i$ exceptional
  characters associated with each subgroup $A_i$, and by
  @prop:exceptional-character-values(ii), exceptional characters for $A_i$ are
  non-exceptional for $A_j$ if $j!=i$. Hence we have $sum_(i=1)^t n_i$ distinct
  nontrivial irreducible characters of $G$ which are exceptional for the various
  subgroups ${A_i}$. On the other hand, the sets ${A_j}$ form a partition of the
  conjugacy classes of $G$; since each set $A_j^*$ is a disjoint union of $n_j$
  special classes, it follows that $G$ has $1+sum_(i=1)^t n_i$ distinct
  conjugacy classes. By @th:split-group-algebra-dimensions, it follows that
  _every_ nontrivial irreducible character of $G$ is exceptional for some
  subgroup $A_i$, $1 <= i <= t$.

  Now let us choose the notation so that $m_t$ is the smallest integer among the
  ${m_i}$, and set
  $ m_t=m, e_t=e, n_t=n. $
  By @prop:exceptional-character-values(i) and
  @prop:exceptional-character-values(iv), we may, after reordering only the
  indices $1,dots,t-1$, assume that the common degree $d$ of the exceptional
  characters for $A_t$ satisfies
  $ m_i divides d, 1 <= i <= u, quad m_i divides.not d, u<i<t. $

  #source(383)
  Finally let $Gamma_i=(1_A^H-psi_i)^G$, where the ${psi_i}$ are characters of
  $H_t$ of degree $e$, as in @prop:sa-subgroup-special-classes(iii); then we may
  write
  $
    Gamma_i=1-epsilon zeta_i+a sum_(k=1)^n zeta_k
    +sum_j c_j theta_j, quad 1 <= i <= n.
  $
  Now the non-exceptional characters ${theta_j}$ for $A_t$ fall into sets of
  exceptional characters ${zeta_j^h}_(1 <= j <= n_h)$ for the other subgroups
  $A_h$; the characters in each such set have the same degree by
  @prop:exceptional-character-values(i) and hence appear in $Gamma_i$ with the
  same multiplicity by @prop:exceptional-character-values(v). We may therefore
  rewrite each $Gamma_i$ in the form
  $
    Gamma_i=1-epsilon zeta_i+a sum_(k=1)^n zeta_k
    +sum_(h=1)^(t-1) c_h lr((sum_(j=1)^(n_h) zeta_j^h)).
  $
  Moreover, by @prop:sa-subgroup-special-classes(iv), each $Gamma_i$ will vanish
  on the set $A_1^* union dots union A_(t-1)^*$.

  Suppose now that for some $h_0 <= u$, the multiplicity $c_(h_0)$ equals zero.
  Then by @prop:exceptional-character-values(iv), for all $x in A_(h_0)^*$ we
  have
  $
    zeta_k lr((x))=0, 1 <= k <= n;
    quad zeta_j^h lr((x))=y_h in ZZ
    quad "for" 1 <= j <= n_h, "for all" h!=h_0.
  $
  The equation $Gamma_i lr((x))=0$ for $x in A_(h_0)^*$ then implies that
  $ 0=1+sum_(h!=h_0) c_h n_h y_h, $
  which is impossible since ${c_h}$, ${n_h}$ and ${y_h}$ are integers, and the
  ${n_h}$ are all even. Hence $c_h!=0$ for $1 <= h <= u$. On the other hand, by
  @prop:exceptional-character-values(iii) we have
  $
    e=a^2(n-1)+(a-epsilon)^2+sum_h c_h^2 n_h
    >= 1+sum_(h=1)^u c_h^2 n_h.
  $
  Hence we have proved
  $ e-1 >= sum_(h=1)^u c_h^2 n_h, quad "where each" c_h!=0. $
  <eq:ca-group-multiplicity-bound>

  We next obtain an inequality for the order $g$ of $G$. Setting $zeta=zeta_k$
  for some $k$, $1 <= k <= n$, we have
  $
    g=sum_(x in G) |zeta(x)|^2
    =d^2+sum_(i=1)^t (g slash (m_i e_i))
    sum_(x in A_i^*) |zeta(x)|^2,
  $
  since there are $|G:H_i|=g slash (m_i e_i)$ distinct conjugates of each
  subgroup $A_i$, $1 <= i <= t$. For each $i$ with $u<i<t$, $zeta(x)$ is a
  nonzero rational integer for all
  #source(384)
  $x in A_i^*$, by @prop:exceptional-character-values(iv). Hence
  $ sum_(x in A_i^*) |zeta(x)|^2 >= m_i-1, quad i=u+1,dots,t-1. $
  In case $i=t$, we have by @prop:exceptional-character-values(vi):
  $ sum_(x in A_t^*) |zeta(x)|^2 >= e(m-e). $
  Combining these results, we obtain
  $
    g >= d^2+lr({sum_(i=u+1)^(t-1) g/(m_i e_i) (m_i-1)})
    +g/m (m-e).
  $ <eq:ca-group-order-bound>

  On the other hand, every element of $G$ is conjugate to some element of
  $A_1 union dots union A_t$, so
  $ g=1+sum_(i=1)^t g/(m_i e_i) (m_i-1). $
  This formula and @eq:ca-group-order-bound imply
  $
    1+lr({sum_(i=1)^u g/(m_i e_i) (m_i-1)})+g/(m e) (m-1)
    >= d^2+g/m (m-e).
  $
  Since
  $ 1/(m e) (m-1)-1/m (m-e)=(m-1+e^2)/(m e)-1, $
  the above formula simplifies to #named-equation(name: [$(ast)$])[$
    lr({sum_(i=1)^u (m_i-1)/(m_i e_i)})
    +(m-1+e^2)/(m e) >= 1+(d^2-1)/g.
  $] <eq:ca-group-normalized-order-bound>
  Now $(m_i-1) slash e_i=n_i$, and $m_i >= m$ for $1 <= i <= t$, so we obtain
  $ lr((sum_(i=1)^u n_i)) slash m >= sum_(i=1)^u (m_i-1)/(m_i e_i). $
  By @eq:ca-group-multiplicity-bound, we have $e-1 >= sum_(i=1)^u n_i$, so the
  inequality @eq:ca-group-normalized-order-bound implies
  $ (e-1)/m+(m-1+e^2)/(m e) >= 1+(d^2-1)/g. $

  #source(385)
  Since we have assumed that $d$ is the degree of a nontrivial irreducible
  character of a non-abelian simple group, we have $d>1$. Therefore we obtain a
  strict inequality
  $ (e-1)/m+(m-1+e^2)/(m e)>1. $
  From this we deduce, since $m-1=n e$,
  $ e-1+n+e>n e+1, quad "so" 2(e-1)+n(1-e)>0, $
  and therefore
  $ (e-1)(2-n)>0. $
  The last inequality is impossible because $e >= 1$ and $n >= 2$, and the proof
  of the theorem is completed!
]

#heading(level: 3)[
  Characters of $A_5$. Examples of Exceptional Characters
] <ss:a5-exceptional-characters>

Let $G$ be the alternating group $A_5$.
#idx("alternating group")
#idx("group", "alternating")
Using the Sylow theorems, it can be shown that $G$ is the unique simple
non-abelian group of order $60$. From this result, or by a direct argument based
on Sylow’s theorems, it can also be verified that
$ G tilde.equiv SL_2 lr((4)) tilde.equiv op("PSL")_2 lr((5)). $
As an illustration of the methods of the preceding section, we shall determine
the characters of $G$ in the field $K$ of complex numbers, leaving a number of
details to be checked by the reader. The group $G$ is also an example of a
simple CA-group.

There are $5$ conjugacy classes in $G$, which we label by the orders of their
elements:
$ 1,2,3,5_1,5_2. $
The orders of the corresponding centralizers are
$ 60,4,3,5,5. $
Let $A$ be a Sylow $5$-subgroup of $G$. Then $A$ is a cyclic SA-subgroup
generated by a $5$-cycle, and $N_G lr((A))=H$ is easily shown to be dihedral of
order $10$. We apply @prop:sa-subgroup-special-classes to find the exceptional
characters associated with the subgroup $A$.
#idx("character", "exceptional")
#idx("exceptional character")
In this case we have, following the notation of
§@ss:exceptional-characters-ca-groups,
$ m=|A|=5,e=|H:A|=2,n=(m-1) slash e=2. $
Thus there are two exceptional characters having the same degree, by
@prop:exceptional-character-values(i).

#source(386)
The dihedral group $H=N_G lr((A))$ has exactly two non-linear irreducible
characters $psi_1,psi_2$ of degree $2$; these are induced characters
$ psi_1=lambda_1^H,psi_2=lambda_2^H, $
where $lambda_1,lambda_2$ are non-trivial linear characters of $A$ (see
@exm:dihedral-group-characters). For $i=1,2$, the values of $psi_i$ are given in
@exm:dihedral-group-characters, using the fact that
$psi_i|_A=lambda_i+overline(lambda_i)$. Part of the character table of $H$
involving $psi_1$ and $psi_2$ is as follows:

#d5-exceptional-table

where
$ alpha=epsilon+overline(epsilon),beta=epsilon^2+overline(epsilon)^2, $
and $epsilon$ is a primitive $5$-th root of $1$.

By @prop:sa-subgroup-special-classes(iv) we have
$ (psi_1-psi_2)^G=zeta_1-zeta_2, $
where $zeta_1$ and $zeta_2$ are the exceptional characters associated with the
subgroup $A$; in this case, the sign $epsilon$ in
@prop:sa-subgroup-special-classes can be chosen equal to $1$.

We shall apply Theorem @th:suzuki-special-class-character-values to determine
the values of $zeta_1,zeta_2$ on the special classes $5_1$ and $5_2$. Changing
the notation of §@ss:special-classes, we have
$ op("Irr") H={psi_0(=1_H),psi_1,psi_2,psi_3}, $
where $psi_3$ is the nontrivial linear character. Also
$ op("Irr") G={zeta_0(=1_G),zeta_1,zeta_2,zeta_3,zeta_4}, $
where $zeta_3$ and $zeta_4$ are the nontrivial non-exceptional characters of
$G$. For a basis of $W(frak(S))$ as in
@lem:special-class-virtual-character-basis, we may choose
$ lambda_1=psi_1-psi_2,lambda_2=1_A^H-psi_1=1_H+psi_3-psi_1. $
Then by @prop:sa-subgroup-special-classes(iv),
$
  lambda_1^G=zeta_1-zeta_2,
  lambda_2^G=1_G-zeta_1+a(zeta_1+zeta_2)+c_3 zeta_3+c_4 zeta_4.
$
The relation @prop:exceptional-character-values(iii) gives
$ e=a^2(n-1)+(a-epsilon)^2+sum c_j^2. $

#source(387)
Since $epsilon=plus.minus 1$, this yields as possibilities
$
  a=0,{c_3,c_4}={plus.minus 1,0},
  quad "or else" a=1,{c_3,c_4}={plus.minus 1,0}.
$
In the first case, it follows immediately from Theorem
@th:suzuki-special-class-character-values that the exceptional characters
$zeta_1$ and $zeta_2$ take the same values as $psi_1$ and $psi_2$ on the special
classes. In the second case, we interchange $zeta_1$ and $zeta_2$, making
$epsilon=-1$, and again obtain $a=0$; thus in this case the values of $zeta_1$
and $zeta_2$ differ in sign from those of $psi_1$ and $psi_2$. This ambiguity
will be removed later. Let $B$ denote a Sylow $2$-subgroup of $G$, of order $4$.

The permutation representations of $G$ on the cosets $G slash N_G lr((B))$ and
$G slash N_G lr((A))$ are both doubly transitive, of degrees $5$ and $6$,
respectively. If $theta_3$ and $theta_4$ are the permutation characters, then by
Exercise @exc:doubly-transitive-character, $zeta_3=theta_3-1$ and
$zeta_4=theta_4-1$ are irreducible, of degrees $4$ and $5$, respectively. Since
the sum of the squares of the degrees of all irreducible representations is
$60$, it follows that $zeta_3$ and $zeta_4$ are the non-exceptional characters,
and the exceptional characters $zeta_1$ and $zeta_2$ both have degree $3$. The
values of $zeta_3$ and $zeta_4$ are easily found from the values of $theta_3$
and $theta_4$. Note that the multiplicity of $zeta_4$ in $lambda_2^G$ is zero by
@prop:exceptional-character-values(iv), since $zeta_4 lr((1))=5=m$. We then
obtain for the character table of $G$:

#numbered-block(a5-character-table) <eq:a5-character-table>
#idx("character", "table", target: [@eq:a5-character-table])

By the Second Orthogonality Relation, we obtain $x=-1,y=0$. It then follows from
the second orthogonality relation that $alpha$ and $beta$ appear with the sign
$-1$ in all occurrences, since ${alpha,beta}={1/2 (-1 plus.minus sqrt(5))}$.

There are several noteworthy features of this example, for which we should be
alert in more general situations. The first is the remarkable fact that the part
of the table involving the irrational entries ${alpha,beta}$ is simply lifted
from the character table of a much easier group $H=D_5$, using the theory of
exceptional characters. The non-exceptional characters are formed in this case
from doubly transitive permutation representations. Later, in
§@ss:green-correspondence-character-applications, we shall indicate how to get
more information about non-exceptional characters by using the theory of modular
representations.

It is also possible to find the characters of $A_5$ from the method of
§@ss:character-table, by calculating the structure constants $c_(i j k)$ for the
center of the group algebra (see Frobenius~@bib:Frobenius1896 or
McKay~@bib:McKay1979). One may also use the method of induced characters (see
Isaacs~@bib:Isaacs1976, p.~84).

#source(388)
#heading(level: 3)[
  The Brauer-Suzuki Theorem on Generalized Quaternion Sylow $2$-Groups
] <ss:brauer-suzuki-generalized-quaternion>

In this subsection, we shall apply the theory of special classes to another
important minimal situation in the classification of finite simple groups. This
time, we shall focus on the possible structures for a Sylow $2$-subgroup of a
finite simple group. In §@ss:normal-p-complements-transfer we proved, using
Burnside’s Transfer Theorem, that a Sylow $2$-subgroup of a non-abelian simple
group cannot be cyclic of order greater than $1$. The Brauer-Suzuki theorem,
proved in this subsection, shows that there cannot be a simple finite group
whose Sylow $2$-subgroup is generalized quaternion of order $>=16$. Using the
theory of blocks, Brauer-Suzuki~@bib:Brauer1959 also showed that the quaternion
group of order $8$ cannot appear as the Sylow $2$-subgroup of a simple group.
Another proof of this result, independent of block theory, and based instead on
a delicate refinement of the discussion to follow, was found by
Glauberman~@bib:Glauberman1974.

On the other hand, dihedral groups may appear as Sylow $2$-subgroups of simple
groups, and the classification of such simple groups was historically an
important step towards the determinations of all simple groups whose structure
is minimal in some sense. In this connection,
Gorenstein-Walter~@bib:Gorenstein1965 proved that a simple group with dihedral
Sylow $2$-subgroup must be either $A_7$ or $op("PSL")_2 lr((q))$, $q$ odd.

We recall from §@ss:background-group-theory that a generalized quaternion
$2$-group $S$ has a presentation
$ S=⟨x,y:x^(2^n)=1,y^2=x^(2^(n-1)),x^y=x^(-1)⟩. $
We shall assume $|S| >= 16$, so $n >= 3$. It is easily shown that such a group
$S$ has a unique involution (=element of order $2$), namely $y^2(=x^(2^(n-1)))$.

#theorem[
  Let $G$ be a finite group whose Sylow $2$-subgroups are generalized quaternion
  of order $>=16$. Then $G slash O(G)$ contains a nontrivial cyclic normal
  $2$-subgroup (where $O(G)$ denotes the unique maximal normal subgroup of $G$
  of odd order).
] <th:brauer-suzuki-generalized-quaternion>
#idx(
  "Brauer-Suzuki Theorem",
  target: [@th:brauer-suzuki-generalized-quaternion],
)

The theorem is due to Brauer-Suzuki~@bib:Brauer1959. Our proof follows closely
the presentation by Gorenstein~@bib:Gorenstein1968, Chapter~12.

#proof[
  Let $S$ be a Sylow $2$-subgroup of $G$, with generators and relations as
  above. We set
  $ X=⟨x⟩,T=⟨x^2⟩,R=⟨x^4⟩,C=C_G lr((T)),N=N_G lr((T)). $

  _Step 1._ We claim that there exists a subgroup $H ⊴ N$ such that
  $ N=H times.r S, |H| "is odd, and" C=H times.r X. $

  #source(389)
  To prove this, we note first that $T$ is the derived group $S'$ of $S$, so $S$
  normalizes $T$ and is contained in $N$. Also, since $n >= 3$, $S$ does not
  centralize $T$, so $S inter C=X$. Since $C ⊴ N$, $X$ is a Sylow $2$-subgroup
  of $C$, and is cyclic, so $C$ has a normal $2$-complement $H$, by Corollary
  @cor:cyclic-sylow-two-normal-complement. Then $H=O(C)$, the largest normal
  subgroup of $C$ of odd order, and $H$ is characteristic in $C$. Since $C ⊴ N$,
  we have $H ⊴ N$. By the proof of @cor:cyclic-sylow-two-normal-complement, the
  automorphism group of the cyclic $2$-group $T$ is a $2$-group, so each element
  of odd order in $N$ acts trivially on $T$. Hence the elements in $N$ of odd
  order lie in $C$, and thus clearly belong to $H$. Therefore $N slash H$ is a
  $2$-group, and we have $N=H times.r S,C=H times.r X$, proving the claim made
  above.

  _Step 2._ Let $A=C-R H$. We assert that $A$ is a T.I. set in $G$ (see
  @def:trivial-intersection-set) with normalizer $N$, and hence defines a set of
  special classes in $N$, by the proof of @prop:sa-subgroup-special-classes(ii).
  We first note that since $C=X H$ by Step 1, we have
  $ ⟨a^2⟩H=T H quad "or" quad ⟨a⟩H=T H $
  for each $a in A$. Moreover, $T H tilde.equiv T times H$ by Step 1, so for
  each $a in A$, $T=⟨a^m⟩$ for some integer $m$. Therefore if $a in A inter A^z$
  for some $z in G$, we have $⟨a^m⟩=T=T^z$, so $z in N$. On the other hand, $N$
  normalizes both $C=X H$ and $R H$, since $R$ is a characteristic subgroup of
  the cyclic group $X$. Then $N$ normalizes $A$. Finally, if $⟨a'⟩=⟨a⟩$ for some
  $a' in C$ and $a in A$, then clearly $a' in A$, completing the proof that $A$
  is a T.I. set with normalizer $N$, and that $A$ defines a set of special
  classes in $N$.

  _Step 3._ There exists a linear character $lambda$ of $C$ such that
  $ker lambda=R H$, $lambda^N in op("Irr") N$, and $lambda^N lr((1))=2$. Set
  $theta=1_C^N-lambda^N$. Then the following statements hold:

  (i) $(theta,theta)_N=3$;

  (ii) $theta(1)=0$, and $theta$ vanishes on $N-A$.

  Since $C slash R H tilde.equiv X slash R$ is cyclic of order $4$, there does
  exist a linear character $lambda$ of $C$ whose kernel is $R H$. For any such
  $lambda$, $attach(lambda, tl: y)!=lambda$ for all $y$ such that $N=⟨C,y⟩$, by
  Step 1. By @th:induced-character-irreducibility, $lambda^N$ is irreducible, of
  degree two. Now $1_C^N$ is the character of the regular representation of
  $N slash C$, by Exercise @exc:normal-induced-trivial. Since $|N slash C|=2$,
  $1_C^N=1_N+mu$ where $mu$ is a non-trivial linear character of $N$ with kernel
  $C$. Then clearly $1_N$, $mu$ and $lambda^N$ are the three distinct
  irreducible characters appearing with nonzero multiplicity in $theta$, and we
  have $(theta,theta)=3$ by the orthogonality relations, proving (i). It is also
  clear that $theta(1)=0$ and that $theta$ vanishes on $N-A$, by the definition
  of induced characters.

  _Step 4._ Let $theta=1_C^N-lambda^N$, as in Step 3. We claim there exist
  distinct nontrivial irreducible characters $zeta_1$ and $zeta_2$ of $G$ such
  that
  $
    theta^G=1_G+zeta_1-zeta_2,
    quad "and" zeta_2 lr((1))=zeta_1 lr((1))+1.
  $

  #source(390)
  By Steps 2 and 3 and @lem:special-class-induction-isometry, we have
  $ (theta^G,theta^G)=(theta,theta)_N=3. $
  Moreover, $(1_G,theta^G)=(1_N,theta)=1$ by Frobenius Reciprocity. Then
  $ theta^G=1_G plus.minus zeta_1 plus.minus zeta_2 $
  for some nontrivial irreducible characters $zeta_1$ and $zeta_2$. Since
  $theta^G lr((1))=0$, we may assume the signs chosen so that
  $theta^G=1_G+zeta_1-zeta_2$; then
  $ 0=theta^G lr((1))=1+zeta_1 lr((1))-zeta_2 lr((1)), $
  as required.

  _Step 5._ If $u$ is an involution or an element of odd order in $G$, then
  $theta^G lr((u))=0$ and $zeta_2 lr((u))=1+zeta_1 lr((u))$. These assertions
  hold because, by Step 2, $A$ contains no involutions or elements of odd order.
  Thus $u$ is conjugate to no element of $A$, so $theta(u)=0$ by Step 3, part
  (ii). By @lem:special-class-induction-isometry, $theta^G lr((u))=theta(u)=0$,
  hence $zeta_2 lr((u))=1+zeta_1 lr((u))$ by Step 4.

  _Step 6._ We assert that $G$ contains a single conjugacy class of involutions,
  with a representative which we denote by $u$. [This is clear by Sylow’s
  Theorem, since every involution must be conjugate to the unique involution in
  $S$.] Next, if $c_(u u w)$ is the number of ordered pairs of involutions whose
  product is $w$, for $w in G$, we claim that $c_(u u w)=0$ if $w$ has even
  order. For suppose that $u$ and $v$ are involutions such that $u v=w$, with
  $w$ of even order $2s$. By an easy computation, both $u$ and $v$ invert $w$,
  so $⟨u,v⟩$ is a dihedral group of order $4s$. Then $w^s$ is a central
  involution in $⟨u,v⟩$, and $⟨u,w^s⟩ tilde.equiv ZZ_2 times ZZ_2$. This
  contradicts Sylow’s theorem, since $S$ has no subgroup isomorphic to
  $ZZ_2 times ZZ_2$, and the assertion on $c_(u u w)$ is now proved.

  _Step 7._ By @eq:class-sum-structure-constants, the integer $c_(u u w)$ in
  Step 6 is a structure constant of the center of the group algebra of $G$. We
  have, by @prop:class-sum-constants-character-table,
  $
    c_(u u w^(-1))=|G| |C_G lr((u))|^(-2)
    sum_(m=1)^s z_m^(-1)(zeta^m lr((u)))^2 zeta^m lr((w)),
  $
  where $op("Irr") G={zeta^1,dots,zeta^s}$ and $z_m=zeta^m lr((1))$,
  $1 <= m <= s$. Keeping the involution $u$ fixed, we set
  $gamma(w)=c_(u u w^(-1))$, for $w in G$; then $gamma$ is an integer-valued
  class function on $G$, which vanishes on elements of even order by Step 6.

  _Step 8._ We now show that for each involution $u in G$,
  $
    1+(zeta_1 lr((u))^2)/(zeta_1 lr((1)))
    -(zeta_2 lr((u))^2)/(zeta_2 lr((1)))=0,
  $

  #source(391)
  where $zeta_1$ and $zeta_2$ are defined as in Step 4. To prove this, let
  $gamma$ be the class function defined in Step 7; then $(gamma,theta^G)=0$,
  since $gamma$ vanishes on elements of even order, and $theta^G$ vanishes on
  elements of odd order by Step 5. Since $theta^G=1_G+zeta_1-zeta_2$ by Step 4,
  and
  $
    gamma=|G| |C_G lr((u))|^(-2)
    sum_(m=1)^s z_m^(-1)(zeta^m lr((u)))^2 zeta^m
  $
  by Step 7, the Orthogonality Relations imply
  $
    1+(zeta_1 lr((u))^2)/(zeta_1 lr((1))) (zeta_1,zeta_1)
    -(zeta_2 lr((u))^2)/(zeta_2 lr((1))) (zeta_2,zeta_2)=0,
  $
  as required.

  _Step 9._ We show next that the kernel of $zeta_2$ contains every involution
  of $G$, and is consequently a normal subgroup of $G$ of even order. By Steps
  4, 5 and 8, we have
  $
    1+((zeta_2 lr((u))-1)^2)/(zeta_2 lr((1))-1)
    -(zeta_2 lr((u))^2)/(zeta_2 lr((1)))=0.
  $
  This readily implies that
  $ (zeta_2 lr((u))-zeta_2 lr((1)))^2=0. $
  Then $u in ker zeta_2$ by @prop:character-bound-kernel-scalar-subgroup, which
  proves the assertion above, since by Step 6, there is only one class of
  involutions in $G$.

  _Step 10._ We are now in position to complete the proof. Let $U$ be the
  subgroup of $G$ generated by the involutions. Then $U ⊴ G$, and the subgroup
  $V=S inter U$ is a Sylow $2$-subgroup of $U$. We prove that $V$ is cyclic.
  Suppose this is not the case; then $V$ is also generalized quaternion, and
  contains $y x^i$ for some $i$. Since $V ⊴ S$, $V$ contains also
  $ (y x^i)^x=x^(-1) y x^(i+1)=y x^(i+2), $
  using the fact that $x^(-1) y=y x$ by the defining relations for $S$. Thus $V$
  contains $x^2$, and so $S slash V$ is abelian. We now set $G_1=S U$. Applying
  Steps 1–9 to $G_1$, we conclude that $G_1$ has a non-linear irreducible
  character $zeta$ whose kernel contains $U$. Then $G_1 slash ker zeta$ is a
  homomorphic image of
  $
    G_1 slash U tilde.equiv S U slash U tilde.equiv S slash U inter S
    =S slash V,
  $
  which is abelian. This is contrary to the existence of a non-linear
  irreducible character of $G_1 slash ker zeta$. Therefore $V$ must be cyclic,
  as we wished to prove.

  #source(392)
  Finally, since $U$ has a cyclic Sylow $2$-subgroup of order greater than $1$,
  $U$ has a normal $2$-complement $L$ by Corollary
  @cor:cyclic-sylow-two-normal-complement. Then $L$ is a characteristic subgroup
  of $U$, and since $U ⊴ G$, we have $L ⊴ G$, and so $L ⊴ O(G)$. Then
  $U slash L ⊴ G slash L$, and $U slash L$ is a cyclic $2$-group. Hence
  $G slash O(G)$ contains a nontrivial cyclic normal $2$-subgroup, completing
  the proof.
]

#remarks(numbered: false)[
  (i) If $G$ has a generalized quaternion Sylow $2$-subgroup $S$ as above, then
  it follows from the preceding theorem that $G slash O(G)$ has a central
  subgroup of order $2$. The inverse image $Z$ of this subgroup is a normal
  subgroup of $G$ whose order is twice an odd number. It follows that a Sylow
  subgroup of $G slash Z$ is isomorphic to
  $S Z slash Z tilde.equiv S slash Z inter S$, which is a dihedral group. From
  the Gorenstein-Walter~@bib:Gorenstein1965 classification of groups with
  dihedral Sylow $2$-subgroups, it can be proved that $G slash Z$ is either a
  $2$-group, or is isomorphic to $A_7$, or else contains a normal subgroup
  isomorphic to $op("PSL")_2 lr((q))$, for $q$ odd.#ed-note[
    The classification applies to $G slash Z$, whose Sylow $2$-subgroups are
    dihedral and whose odd core is trivial. The printed claim about
    $G slash O(G)$ fails for $SL_2 lr((7))$. See Gorenstein~@bib:Gorenstein1980,
    Chapter~16, §3.
  ]

  (ii) The following result can be viewed as a far-reaching extension of the
  Brauer-Suzuki Theorem.

  #theorem(name: [Glauberman’s $Z^*$-Theorem], numbered: false)[
    Let $G$ be a finite group with Sylow $2$-subgroup $S$, and let $u$ be an
    involution in $S$. Suppose the only conjugate of $u$ lying in $S$ is $u$
    itself. Then
    $ u O(G) in "center of" lr((G slash O(G))). $
  ] <th:glauberman-z-star>
  #idx("Glauberman's $Z^*$-Theorem", target: [@th:glauberman-z-star])

  Indeed a generalized quaternion group contains a unique involution; we see
  thus that the Brauer-Suzuki Theorem is a special case of Glauberman’s Theorem.
  The $Z^*$-theorem can be proved using the theory of blocks (see Chapter~9 of
  Volume~II).
]

#heading(level: 3)[
  Centralizers of Involutions and Special Classes
] <ss:involution-centralizers-special-classes>

Our final application of special classes (in
§@sec:special-classes-exceptional-characters) is to the problem of determining
the structure of a finite group $G$ containing an involution $u$ whose
centralizer $C_G lr((u))$ in $G$ has some known structure.

This problem arises in the following way. Consider a known finite simple group
$G_0$, and let $u_0 in G_0$ be an involution whose centralizer
$H_0=C_(G_0) lr((u_0))$ can be determined from our knowledge of the structure of
$G_0$. We then consider an arbitrary finite simple group $G$ containing an
involution $u$ such that $H=C_G lr((u))$ is isomorphic to $H_0$, and ask whether
$G$ is isomorphic to $G_0$, and if not, what other possibilities are there for
$G$? This method is of basic importance for the general classification theory of
simple groups, because it yields workable characterizations of most of the known
simple groups, and has led (in exactly the way indicated above) to the discovery
of several of the sporadic simple groups. The underlying principle is a result
of Brauer (see
#source(393)
Brauer-Fowler~@bib:Brauer1955), which asserts that there exist at most finitely
many non-isomorphic simple groups containing an involution whose centralizer has
a given structure.

Our presentation follows G. Higman~@bib:Higman1968, whose choice of an example
and explanation of the method seem particularly illuminating.

We begin with the consideration of the finite simple group $G_0=SL_3 lr((3))$,
of order $5616$. The group $G_0$ is a finite group of Lie type, of rank $2$ as a
BN-pair. The structure of such groups will be considered in greater detail in
Chapter~7 of Volume~II. It is easily checked that the centralizer in $G_0$ of
the involution
$ mat(delim: "[", -1, 0, 0; 0, -1, 0; 0, 0, 1) $
is isomorphic to the group $GL_2 lr((3))$ of order $48$.

#theorem[
  Let $G$ be a finite simple group containing an involution $t$ whose
  centralizer is isomorphic to $GL_2 lr((3))$. Then the order of $G$ is $5616$
  or $7920$.
] <th:gl23-involution-centralizer>

We remark that the second possibility in @th:gl23-involution-centralizer also
corresponds to a finite simple group, the Mathieu group $M_11$. This provides an
illustration of how multiple solutions of classification problems, in terms of
centralizers of involutions, may yield sporadic simple groups.

We shall present a sketch of the proof of the above theorem, concentrating on
how the theory of special classes is used, and omitting a number of details.

We first require the character table of $H=GL_2 lr((3))$. It is given below with
$op("Irr")(H)={phi^1,dots,phi^8}$. The conjugacy classes
${frak(C)_1,dots,frak(C)_8}$ of $H$ are represented by matrices in
$GL_2 lr((3))$, which may be chosen as follows:
$
  1_H=mat(1, 0; 0, 1), quad t=mat(-1, 0; 0, -1),
  quad u=mat(0, 1; -1, 0),quad u'=mat(1, 0; 1, 1),
$
$
  v=mat(-1, 0; -1, -1),quad v'=mat(1, 0; 0, -1),
  quad w_1=mat(1, -1; 1, 1),quad w_2=mat(-1, 1; -1, -1).
$
Note that $t$ is the unique central involution in $H$. It will be seen later
that the representatives
$ {t,u,v,w_1,w_2} $
correspond to special classes in $H$, where we view $H$ as the centralizer (in
$G$) of some involution in an unknown simple group $G$. In addition to the
character table of $H$ given below, we also need the orders of the centralizers
in $H$ of the $8$ conjugacy class representatives listed above. These orders are
(respectively):
$ 48,48,8,6,6,4,8,8. $

#source(394)
The character table of $H$ is as follows:
#idx("character", "table")

#gl23-character-table

We now view $H$ as a subgroup of $G$, and identify $H$ with the centralizer of
the involution $t$. We first note that the elements ${t,u,v,w_1,w_2}$ are indeed
representatives of a set of special classes in $H$. These are representatives of
all classes in $H$ containing elements $h$ such that $t in ⟨h⟩$. With this
observation, it is easy to check that the axioms @def:special-classes are
satisfied. For example, let $h_1$ and $h_2$ be representatives of two of the
above classes, and assume $x h_1 x^(-1)=h_2$ for $x in G$. Then
$x ⟨h_1⟩ x^(-1)=⟨h_2⟩$, and hence $x t x^(-1)=t$, since $t$ is the unique
involution contained in both $⟨h_1⟩$ and $⟨h_2⟩$. Thus $x in H$, and we have
proved @def:special-classes(ii).

A $ZZ$-basis for the set of virtual characters of $H$ vanishing off the special
classes consists of the virtual characters
$ lambda_1=phi^1+phi^3-phi^4,lambda_2=phi^2+phi^3-phi^5, $
$
  lambda_3=phi^3-phi^6,lambda_4=phi^3-phi^7,
  lambda_5=phi^1+phi^2+phi^3-phi^8.
$
We thus have determined the matrix $upright(bold(A))=(a_(i j))$ in Lemma
@lem:special-class-character-coefficients, and now attempt to determine the
possibilities for a matrix $upright(bold(B))=(b_(i j))$ as in
@lem:special-class-character-coefficients, using the fact that
$
  upright(bold(B)) dot attach(upright(bold(B)), tl: t)
  =upright(bold(A)) dot attach(upright(bold(A)), tl: t),
$
by @lem:special-class-character-coefficients(ii). In this effort, we are
reassured by the fact that $sum_k b_(i k)^2=sum_k a_(i k)^2$ for each $i$, so
there are only finitely many choices for $upright(bold(B))$.

The matrix $upright(bold(A))$ expressing the ${lambda_i}$ in terms of the
${phi^j}$ is

#numbered-block(gl23-virtual-character-matrix)
<eq:gl23-virtual-character-matrix>

#source(395)
with zeros except as indicated. Then we have
$
  upright(bold(A)) dot attach(upright(bold(A)), tl: t)
  =mat(
    delim: "[",
    3, 1, 1, 1, 2; 1, 3, 1, 1, 2; 1, 1, 2, 1, 1;
    1, 1, 1, 2, 1; 2, 2, 1, 1, 4
  ).
$
<eq:gl23-virtual-character-gram-matrix>

Now let $upright(bold(B))=(b_(i j))$ be the matrix such that
$ lambda_i^G=sum_(j=1)^s b_(i j) zeta^j,1 <= i <= 5, $
where $op("Irr") G={zeta^1,zeta^2,dots,zeta^s}$. Then $upright(bold(B))$ is a
$5 times s$ matrix, whose rows we shall denote by
${upright(bold(r))_1,upright(bold(r))_2,dots,upright(bold(r))_5}$. Letting
$upright(bold(r))_i dot upright(bold(r))_j$ denote the usual dot product of
$s$-tuples, we see at once that the condition
$upright(bold(B)) dot attach(upright(bold(B)), tl: t)
=upright(bold(A)) dot attach(upright(bold(A)), tl: t)$ is equivalent to the
condition that
$
  upright(bold(r))_i dot upright(bold(r))_j
  =(i,j)"-entry of" upright(bold(A)) dot attach(upright(bold(A)), tl: t).
$

We are going to show that, up to sign and rearrangement of the nontrivial
characters ${zeta^2,dots,zeta^s}$, the values of ${zeta^2,dots,zeta^s}$ on the
special classes agree with the values of ${phi^1,dots,phi^8}$ on these classes
in $H$. By Theorem @th:suzuki-special-class-character-values, it is sufficient
to prove that up to a rearrangement of the columns after the first, and up to
changes of sign in the columns, the matrix $upright(bold(B))$ coincides with the
matrix $upright(bold(A))$ given in @eq:gl23-virtual-character-matrix (with
additional columns of zeros added as necessary). This procedure is valid because
the values of the characters ${zeta^i}$ will be used only in the class number
equation @prop:class-sum-constants-character-table, where an ambiguity of sign
has no effect.

By @eq:gl23-virtual-character-gram-matrix, we have
$upright(bold(r))_1 dot upright(bold(r))_1=3$, so for the first row of
$upright(bold(B))$ we may take
$ upright(bold(r))_1=⟨1,0,1,-1,0,0,dots⟩, $
taking into account the remarks in the preceding paragraph. Now
$b_21=(lambda_2^G,1_G)=a_21=0$ by @lem:special-class-character-coefficients, and
$upright(bold(r))_2 dot upright(bold(r))_1=1$,
$upright(bold(r))_2 dot upright(bold(r))_2=3$, so we may choose
$ upright(bold(r))_2=⟨0,1,1,0,-1,0,dots⟩, $
because the other possibilities
$
  ⟨0,1,plus.minus 1,plus.minus 1,0,dots⟩
  quad "or" quad ⟨0,1,-1,0,-1,0,dots⟩
$
are easily ruled out. Next
$
  upright(bold(r))_3 dot upright(bold(r))_3=2,
  upright(bold(r))_3 dot upright(bold(r))_1
  =upright(bold(r))_3 dot upright(bold(r))_2=1
  quad "and" b_31=0.
$
Thus $upright(bold(r))_3$ has exactly one $plus.minus 1$ in positions
corresponding to the nonzero entries
#source(396)
of $upright(bold(r))_1$ and $upright(bold(r))_2$. Then for $upright(bold(r))_3$
we obtain
$ upright(bold(r))_3=⟨0,0,1,0,0,-1,0,dots⟩, $
since all other possibilities can be ruled out by using the additional relations
$
  upright(bold(r))_4 dot upright(bold(r))_4=2,
  upright(bold(r))_4 dot upright(bold(r))_3
  =upright(bold(r))_4 dot upright(bold(r))_2
  =upright(bold(r))_4 dot upright(bold(r))_1=1.
$
Continuing in this way, we obtain
$ upright(bold(r))_4=⟨0,0,1,0,0,0,-1,0,dots⟩ $
and
$ upright(bold(r))_5=⟨1,1,1,0,0,0,0,-1,0,dots⟩, $
as required.

Now consider the characters ${zeta^1,dots,zeta^8}$ in $op("Irr") G$, whose
values on the special classes are determined up to sign by the matrix
$upright(bold(B))$ calculated above. Let $x_i=zeta^i lr((1))$, $1 <= i <= 8$.
Then these “virtual degrees” are also determined only up to sign. With these
ambiguities, we obtain the following fragment of the character table of $G$:

#numbered-block(involution-special-character-table)
<eq:involution-special-character-table>

By Theorem @th:suzuki-special-class-character-values, the characters
$zeta^i in op("Irr") G$, such that $i in.not [1,8]$, vanish on the special
classes. Thus we may apply the Second Orthogonality Relation to the above
fragment to obtain information about the “virtual degrees” ${x_i}$:
$ x_1=1 $
$ 1+x_2+2x_3+3x_4+3x_5-2x_6-2x_7-4x_8=0 $
$ 1+x_2+2x_3-x_4-x_5=0 $
#source(397)
$ 1+x_2-x_3+x_6+x_7-x_8=0 $
$ 1-x_2-x_4+x_5+sqrt(2)i x_6-sqrt(2)i x_7=0 $
$ 1-x_2-x_4+x_5-sqrt(2)i x_6+sqrt(2)i x_7=0. $
From these relations, we obtain easily
$ x_6=x_7,x_4+x_5=x_6+x_8=1+x_2+2x_3, $
$ x_6=x_3,x_4=1+x_3,x_4-x_5=1-x_2. $
Therefore, putting $x_2=x$ and $x_3=y$, the virtual degrees ${x_1,x_2,dots,x_8}$
are given by
$ {1,x,y,y+1,x+y,y,y,x+y+1}. $ <eq:involution-virtual-degrees>

We now proceed to apply to @eq:involution-special-character-table and
@eq:involution-virtual-degrees the class number formula
@prop:class-sum-constants-character-table, which asserts that
$
  c_(a b d)=|G| |C_G lr((a))|^(-1)|C_G lr((b))|^(-1)
  sum_(m=1)^s zeta^m lr((1))^(-1) zeta^m lr((a)) zeta^m lr((b))
  zeta^m lr((d^(-1))),
$
where $a,b,d$ are class representatives. We note that the other irreducible
characters vanish on the special classes, and that the right hand side of the
formula is independent of the sign ambiguities discussed previously. In order to
compute the numbers $c_(a b d)$ for representatives of the special classes, we
may use the character table of $H$. To see this, suppose that
$ t^x t^y=h in H,x,y in G, $
where $h$ is a representative of one of the special classes; then
$ (t^x)^(-1) h t^x=t^y t^x=h^(-1), $
and hence $(t^x)^(-1)⟨h⟩t^x=⟨h⟩$, so $t^x in C_G lr((t))=H$. There are two
possibilities for the class intersection number $c_(t t d)$ below, depending on
whether we have:
$ "Case I:" quad t =_G mat(1, 0; 0, -1) $
or
$ "Case II:" quad t !=_G mat(1, 0; 0, -1). $

#source(398)
With these preparations, we obtain the following table.

#involution-class-number-table

In Case II, it follows that $y=2$. In that case $t in ker zeta^3$, contrary to
the assumption that $G$ is a simple group. Thus we have only Case I to consider.
It is then easy to check that the following formula holds:
$ |G|=(2(48)^2 y(y+1))/((y-2)^2). $
We then obtain $(y-2) divides 48$, and
$ x=-(y(y+1))/(y-8). $
Continuing in this manner (see Higman~@bib:Higman1968 or
Dornhoff~@bib:Dornhoff1971, I, §28), we find that the possible solutions are:
$ y=26,x=-39,|G|=5616, $
or
$ y=10,x=-55,|G|=7920, $
completing the proof.

#exercise-heading

#exercise[
  Let $F$ be a finite field with $|F|>2$, and let $G$ be the set of all maps
  $theta:F arrow F$, given by
  $ theta(x)=a x+b,x in F, $
  where $a,b in F$, and $a!=0$. Prove that $G$ is a group under composition of
  maps. Then prove that $G$ is a Frobenius group, and find the Frobenius kernel
  and a Frobenius complement. Then find $op("Irr")_CC G$, using
  @prop:frobenius-group-characters.
] <exc:affine-finite-field-frobenius>
