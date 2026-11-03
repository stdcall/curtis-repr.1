#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/11-clifford-hecke.typ": *

#heading(level: 2)[
  Decomposition of Induced Modules. Clifford Theory and Hecke Algebras
] <sec:clifford-theory-hecke-algebras>

The decomposition of induced modules and characters is one of the most powerful
methods for constructing irreducible representations of finite groups. For
modules induced from normal subgroups, the main results are due to Frobenius,
Clifford and Gallagher, and are presented in §@ss:clifford-theorem,
@ss:clifford-character-theory[B]. In some cases (see
§@ss:clifford-character-theory), one can use these methods to construct all
irreducible characters for certain families of groups. In §@ss:clifford-systems,
one of Clifford’s theorems is presented in a generalized form due to Tucker,
Conlon and Ward. This result leads to the theory of projective representations,
and in §@ss:central-extensions we discuss some of Schur’s results relating
projective representations to central extensions of finite groups. The
decomposition of induced modules from arbitrary subgroups is discussed in
§@ss:hecke-algebras, following Curtis–Fossum, Ree and D. Higman. These methods
will play an important role in the representation theory of finite groups of Lie
type, to come in Volume II.

=== Clifford’s Theorem <ss:clifford-theorem>

The analysis of representations of a finite group $G$ over a field $K$, in terms
of induced representations, is simplified in case $G$ has a normal subgroup.

#theorem(name: "Clifford’s Theorem", title: [Clifford @bib:Clifford1937])[
  Let $K$ be an arbitrary field, $H$ a normal subgroup of a finite group $G$,
  $M$ a simple $K G$-module, and $L$ a simple $K H$-submodule of
  $op("res")_H^G lr((M))$. Then the following statements hold:

  #enum(
    numbering: "(i)",
    [$op("res")_H^G lr((M))$ is a semisimple $K H$-module, and is isomorphic to
      a direct sum of conjugates of $L$.],
    [The $K H$-homogeneous components of $op("res")_H^G lr((M))$ are permuted
      transitively by $G$.],
    [Let $tilde(L)$ be the $K H$-homogeneous component of
      $op("res")_H^G lr((M))$ containing $L$, and let
      $tilde(H)={x in G: x tilde(L)=tilde(L)}$, the stabilizer of $tilde(L)$.
      Write $G$ as a disjoint union $G=union.dot.big_(i=1)^n g_i tilde(H)$. Then
      ${attach(L, tl: g_i):1 <= i <= n}$ is a complete set of non-isomorphic
      #source(282)
      conjugates of $L$, and each appears with the same multiplicity $e$ in
      $op("res")_H^G lr((M))$:
      $
        op("res")_H^G lr((M)) tilde.equiv (plus.o.big_(i=1)^n attach(
            L, tl: g_i
          ))^((e)).
      $],
    [Let $tilde(L)$ and $tilde(H)$ be as in (iii). Then $tilde(L)$ is a
      $K tilde(H)$-module, and
      $ M tilde.equiv op("ind")_(tilde(H))^G lr((tilde(L))). $],
  )
]<th:clifford-theorem>
#idx("Clifford's Theorem", target: [@th:clifford-theorem])#idx(
  "homogeneous components",
  target: [@th:clifford-theorem],
)#idx("stabilizer", target: [@th:clifford-theorem])

#proof[
  (i) Let $L$ be a simple submodule of $op("res")_H^G lr((M))$, as above. For
  each $x in G$, $x L tilde.equiv attach(L, tl: x)$ as $K H$-modules, by Lemma
  @lem:conjugate-modules and the fact that $attach(H, tl: x)=H$ because $H ⊴ G$.
  We observe next that $sum_(x in G) x L$ is a $K G$-submodule of $M$, and hence
  coincides with $M$ because $M$ is simple. Thus $M_H$ is a sum of conjugates
  ${x L}$ of $L$, and the conjugates ${x L}$ are clearly simple $K H$-modules.
  By @prop:semisimple-module-criteria, $M_H$ is semisimple, and the proof of
  @prop:semisimple-module-criteria shows that $M$ is a direct sum of conjugates
  ${x L}$ of $L$, completing the proof of (i).

  (ii) Let us prove that the $K H$-homogeneous components of
  $op("res")_H^G lr((M))$ are permuted by $G$. Let $L'$ and $L''$ be simple
  $K H$-submodules of $op("res")_H^G lr((M))$. It suffices to prove that if
  $phi:L' -> L''$ is a $K H$-isomorphism, then $x L' tilde.equiv x L''$ as
  $K H$-modules for each $x in G$. But clearly $x phi x^(-1):x L' -> x L''$ is a
  $K$-isomorphism. It is also an $H$-isomorphism, since for $h in H$,
  $l' in L'$, we have
  $ (x phi x^(-1)) h x l'=x(x^(-1)h x)phi l'=h[(x phi x^(-1))x l'], $
  as required.

  Now let $tilde(L)$ denote the homogeneous component of $op("res")_H^G lr((M))$
  containing $L$, so $tilde(L)$ is the direct sum of those summands $x L$ of $M$
  which are $K H$-isomorphic to $L$. Then $x tilde(L)$ is also a homogeneous
  component for each $x in G$, and $sum_(x in G)x tilde(L)$ is a $K G$-submodule
  of $M$. Therefore $sum_(x in G)x tilde(L)=M$, and it follows from
  @prop:homogeneous-decomposition that every homogeneous component of
  $op("res")_H^G lr((M))$ is a translate $x tilde(L)$ of $tilde(L)$ by some
  element $x in G$. We have shown that $G$ acts transitively on the homogeneous
  components of $op("res")_H^G lr((M))$, completing the proof of (ii).

  (iii) From part (ii), the homogeneous components of $op("res")_H^G lr((M))$
  form a single orbit under the action of $G$. Let $tilde(L)$ be a fixed
  homogeneous component, and $tilde(H)$ its stabilizer as defined in (iii). Then
  the elements of the $G$-orbit of $tilde(L)$ are in bijective correspondence
  with any set of left coset representatives ${g_1,dots,g_n}$ of
  $G slash tilde(H)$, and we have
  $ op("res")_H^G lr((M))=plus.o.big_(i=1)^n g_i tilde(L). $
  From the proof of (ii), it follows that every conjugate of $L$ is isomorphic
  to
  #source(283)
  some $g_i L$, where $1 <= i <= n$. Finally, since $M=g_i M$, the multiplicity
  of $g_i L$ in $g_i tilde(L)$ is the same as the multiplicity $e$ of $L$ in
  $tilde(L)$, and the proof of (iii) is completed.

  (iv) From (iii), $M$, $tilde(L)$ and $tilde(H)$ satisfy the conditions of
  Proposition @prop:induced-module-criterion, so
  $M tilde.equiv op("ind")_(tilde(H))^G lr((tilde(L)))$ as required.
]

The preceding result expresses every simple $K G$-module $M$ as an induced
module $op("ind")_(tilde(H))^G lr((tilde(L)))$ for some subgroup $tilde(H)$ such
that $H <= tilde(H) <= G$. The problem of determining all simple $K G$-modules
is thus reduced to the corresponding problem for proper subgroups of $G$, except
when $tilde(H)=G$. We are then led to two problems. First, to find in what
circumstances the group $tilde(H)$ can be taken to be a proper subgroup of $G$.
Second, to investigate what can be done in case the situation $tilde(H)=G$
cannot be avoided. When $K$ is algebraically closed, the second problem leads to
a factorization of the representation afforded by $M$ as a tensor product of
projective representations (@bib:CurtisReiner1962[CR §~51]). An improved version
of this construction will be given later, first for characters (in
§@ss:clifford-character-theory), and then for modules (in
§@ss:clifford-systems). We conclude this section with some important cases where
a favorable solution of the first problem is possible.

#proposition(title: [Blichfeldt])[
  Let $K$ be an algebraically closed field, and $M$ a f.d. vector space over
  $K$. Let $G$ be a finite subgroup of $GL(M)$ which acts irreducibly on $M$ (so
  that $M$ is a simple $K G$-module), and let $A$ be an abelian normal subgroup
  of $G$ not contained in the center of $G$. Let $L$ be a simple submodule of
  $op("res")_A^G lr((M))$, $tilde(L)$ a $K A$-homogeneous component of
  $op("res")_A^G lr((M))$, and $tilde(A)$ the stabilizer of $tilde(L)$ as in
  Theorem @th:clifford-theorem. Then $tilde(A)<G$, and
  $M tilde.equiv op("ind")_(tilde(A))^G lr((tilde(L)))$.
]<prop:blichfeldt-imprimitivity>
#proof[
  Because of Theorem @th:clifford-theorem, it is sufficient to prove that
  $tilde(L)!=M$. Since $K$ is algebraically closed and $A$ is abelian, we have
  $dim_K L=1$. By @th:clifford-theorem(i), $op("res")_A^G lr((M))$ is a direct
  sum of conjugates of $L$. If $tilde(L)=M$, the conjugates of $L$ are mutually
  isomorphic as $K A$-modules, whence each $a in A$ has the form
  $a=alpha dot 1_M$ for some $alpha in K$. But this contradicts the assumption
  that $A$ is not contained in the center of $G$, and the result is proved.
]

A $K G$-module $M$ is called _imprimitive_#idx("imprimitive") if
$M tilde.equiv op("ind")_H^G lr((L))$ for some $K H$-module $L$, with $H$ a
proper subgroup of $G$; call $M$ _primitive_#idx("primitive module") if it
cannot be expressed in this way. We may thus refer to the preceding result as
_Blichfeldt’s Criterion for Imprimitivity_.#idx(
  "Blichfeldt's Criterion for Imprimitivity",
) We use this criterion to prove that if $G$ is nilpotent, then every simple
$K G$-module is induced from a one-dimensional module.

#theorem[
  Let $G$ be a finite nilpotent group, and let $K$ be an algebraically closed
  field. Every simple $K G$-module $M$ can be expressed in the form
  $M tilde.equiv op("ind")_H^G lr((L))$ for some subgroup $H <= G$ and some
  one-dimensional $K H$-module $L$.
]<th:nilpotent-group-monomial>
#source(284)
#proof[
  We require two facts from elementary group theory (see
  §@sec:background-algebras-groups):

  (i) Subgroups and homomorphic images of nilpotent groups are nilpotent.

  (ii) If $G$ is nilpotent and not abelian, then there exists an abelian normal
  subgroup $A$ not contained in the center $Z(G)$.

  Let $M$ be a simple $K G$-module, and let $G_l$ be the homomorphic image of
  $G$ consisting of all left multiplications ${x_l:x in G}$ on $M$. Then
  $G_l <= GL(M)$, and is either abelian, in which case $dim_K M=1$, or else
  $G_l$ has a proper abelian normal subgroup not contained in the center. In the
  latter case, Blichfeldt’s criterion @prop:blichfeldt-imprimitivity implies
  that $M tilde.equiv op("ind")_(H_l)^(G_l) lr((L))$ for some subgroup
  $H_l<G_l$, and some $K H_l$-module $L$. But $H_l$ comes from some subgroup
  $H<G$ by the homomorphism theorem, and $L$ is then a $K H$-module. By
  @prop:induced-module-criterion we have $M tilde.equiv op("ind")_H^G lr((L))$.
  Using induction on $|G|$, we may assume that
  $L tilde.equiv op("ind")_(H_1)^H lr((L_1))$ for a subgroup $H_1<=H$, and a
  one-dimensional $K H_1$-module $L_1$. By transitivity of induction
  @prop:induction-transitive, we have
  $
    M tilde.equiv op("ind")_H^G lr((L))
    =op("ind")_H^G lr((op("ind")_(H_1)^H lr((L_1))))
    tilde.equiv op("ind")_(H_1)^G lr((L_1)),
  $
  completing the proof of the theorem.
]

The preceding theorem shows the importance of studying representations of $G$
induced from one-dimensional representations of subgroups of $G$. Such induced
representations are called _monomial representations_ #idx(
  "monomial representation",
) (see Exercise @exc:monomial-restriction). Finite groups with the property that
every simple module is induced from a one-dimensional module, as in Theorem
@th:nilpotent-group-monomial, are called _$M$-groups_#idx("M-group") (for
monomial groups). $M$-groups are always solvable (@bib:CurtisReiner1962[CR
  §~53]), but not every solvable group is an $M$-group. For further discussion
of $M$-groups, see Exercises @exc:supersolvable-monomial and
@exc:solvable-nonmonomial, as well as Huppert @bib:Huppert1967, Chapter V, §18.

#heading(level: 3)[
  Applications of Clifford’s Theorem to Character Theory
] <ss:clifford-character-theory>

We shall investigate the character-theoretic implications of Clifford’s Theorem,
particularly in the more difficult case in which the submodule $L$ (in
@th:clifford-theorem) is isomorphic to all its conjugates.

In this section, we assume that $K$ is a splitting field for a finite group $G$
and all its subgroups, and that $K$ is contained in the complex field; thus
scalar products of characters can be related to multiplicities (see
@prop:character-scalar-products-multiplicities). As in
§@ss:finite-group-character-orthogonality, we use the notation
$op("Irr")_K lr((G))$ to denote the set of irreducible $K$-characters of $G$.
The discussion to follow is based on a paper of Gallagher @bib:Gallagher1962b.

Let $H ⊴ G$, and let $psi$ be a $K$-character of $H$. Then for $x in G$, the
_conjugate_#idx("conjugate character")#idx("character", "conjugate")
$attach(psi, tl: x)$ is also a $K$-character of $H$. We denote by $G_psi$ the
_stabilizer_#idx("stabilizer") of $psi$, defined by
$ G_psi={x in G:attach(psi, tl: x)=psi}. $

#source(285)
Note that $G_psi$ is a subgroup containing $H$. Further, from
@th:clifford-theorem(iii) it follows that if $L$ is a $K H$-module affording
$psi$, then $G_psi$ can also be characterized as
$ G_psi={x in G:attach(L, tl: x) tilde.equiv L "as" K H "-modules"}. $

#proposition[
  #enum(
    numbering: "(i)",
    [Let $zeta in op("Irr")_K lr((G))$, and let $H ⊴ G$. Then
      $ zeta|_H=e sum_x attach(psi, tl: x), $
      where $e$ is a positive integer, $psi in op("Irr")_K lr((H))$, and the sum
      is taken over the distinct $G$-conjugates of $psi$.],
    [Let $psi in op("Irr")_K lr((H))$, and let $G_psi$ be the stabilizer of
      $psi$ in $G$. For each $zeta in op("Irr")_K lr((G))$ such that
      $(zeta,psi^G)>0$, there exists an $eta in op("Irr")_K lr((G_psi))$ with
      the properties $eta|_H=r psi$ for some positive integer $r$, and
      $zeta=eta^G$.],
  )
]<prop:clifford-character-restriction>
#remark(numbered: false)[
  By Exercise @exc:clifford-character-uniqueness, the above character $eta$ is
  the unique character $eta in op("Irr")_K lr((G_psi))$ satisfying the
  conditions that $(eta^G,zeta)>0$ and $(eta,psi^(G_psi))>0$.
]
#proof[
  Part (i) is just the translation of @th:clifford-theorem(iii) into the
  language of character theory.

  (ii) By Frobenius Reciprocity @th:frobenius-class-functions, $(zeta,psi^G)>0$
  implies $(zeta|_H,psi)>0$. Let $zeta$ be afforded by the simple $K G$-module
  $M$; then $psi$ is afforded by a simple $K H$-submodule $L$ of
  $op("res")_H^G lr((M))$. Keeping the notation of @th:clifford-theorem, let
  $tilde(L)$ be the $K H$-homogeneous component of $op("res")_H^G lr((M))$
  containing $L$. Then $tilde(L)$ is a $K G_psi$-module; let $eta$ be the
  $K$-character of $G_psi$ afforded by $tilde(L)$. Then $eta|_H=r psi$ for some
  positive integer $r$ because all the simple components of $tilde(L)$ are
  isomorphic to $L$; further, $zeta=eta^G$ by @th:clifford-theorem(iv). Finally,
  $zeta in op("Irr")_K lr((G))$ implies $eta in op("Irr")_K lr((G_psi))$, by
  @prop:induction-transitive and the fact that $zeta=eta^G$. This completes the
  proof.
]

#theorem[
  Let $psi in op("Irr")_K lr((H))$ where $H ⊴ G$, and let $S=G_psi$, the
  stabilizer of $psi$ in $G$. Suppose that $psi=psi_1|_H$ for some $K$-character
  $psi_1$ of $S$, that is, suppose that $psi$ can be extended to a character
  $psi_1$ of $S$. Then

  #enum(
    numbering: "(i)",
    [$psi_1 in op("Irr")_K lr((S))$.],
    [Each $omega in op("Irr")_K lr((S slash H))$ can be viewed as an irreducible
      $K$-character of $S$, and we have $(omega psi_1)^G in op("Irr")_K lr((G))$
      for each $omega$.],
    [The formula $psi^G=sum omega(1)(omega psi_1)^G$, where the sum extends over
      all $omega in op("Irr")_K lr((S slash H))$, gives $psi^G$ as a linear
      combination of distinct irreducible characters $(omega psi_1)^G$.],
  )
]<th:gallagher-character-extension>
#source(286)
#proof[
  Assertion (i) is obvious. Next, $psi^S$ vanishes on $S-H$ by
  @eq:induced-character-cosets, and equals $|S:H|psi$ on $H$. On the other hand,
  $ sum_omega omega(1)(omega psi_1)=lr({sum_omega omega(1)omega})psi_1, $
  and $sum omega(1)omega$ is the regular character of $S slash H$ (see Exercise
  @exc:quotient-character-lift). This character vanishes on $S-H$ when viewed as
  a character of $S$, and takes the value $|S:H|$ on $H$. It follows that
  $ psi^S=sum_omega omega(1)(omega psi_1), $
  which gives the formula for $psi^G$ in (iii), by transitivity of induction.

  From the Intertwining Number Theorem @th:intertwining-number we have
  $ (psi^G,psi^G)=sum_(x H in G slash H) lr((psi,attach(psi, tl: x)))_H=|S:H|. $
  On the other hand,
  $
    (psi^G,psi^G)=sum_(omega,omega')omega(1)omega'(1)
    ((omega psi_1)^G,(omega' psi_1)^G),
  $ <eq:gallagher-character-norm>
  and the terms where $omega=omega'$ already contribute at least
  $sum_omega omega(1)^2$. This sum equals $|S:H|$, and since all terms on the
  right in @eq:gallagher-character-norm are non-negative, it follows that
  $((omega psi_1)^G,(omega psi_1)^G)=1$ for each $omega$. Hence the characters
  ${(omega psi_1)^G:omega in op("Irr")_K lr((S slash H))}$ are irreducible and
  distinct, which completes the proof of the theorem.
]

It is worthwhile to state, as a corollary, the above result for the special case
where $G_psi=G$ and where $psi$ can be extended to a character of $G$. (Criteria
for the existence of such an extension are given later in this section, as well
as in Exercises @exc:wreath-product-characters and @exc:metacyclic-characters,
and in §@sec:artin-brauer-induction.)

#corollary[
  Let $H ⊴ G$, and let $psi in op("Irr")_K lr((H))$ be a character such that
  $G_psi=G$. If $psi$ can be extended to a character $psi_1$ of $G$, then every
  irreducible component $zeta$ of $psi^G$ can be expressed in the form
  $zeta=omega psi_1$, for a uniquely determined irreducible character $omega$ of
  $G slash H$.
]<cor:gallagher-invariant-character>

This result is, of course, a special case of @th:gallagher-character-extension.
We note also that $(zeta,psi^G)>0$ if and only if $(zeta|_H,psi)>0$. Thus, in
this situation $zeta$ is an irreducible $K$-character of $G$ such that the
components of $zeta|_H$ are mutually isomorphic. In terms of the notation in
@th:clifford-theorem, $zeta$ comes from a $K G$-module $M$ such that
$L tilde.equiv attach(L, tl: x)$ for all $x in G$, where $L$ is a simple
submodule of $op("res")_H^G lr((M))$.

#source(287)
Combining the preceding results, we discover a rare phenomenon: a family of
groups for which we can describe all the irreducible characters in terms of
characters of proper subgroups. The technique described here is sometimes called
the _method of little groups_.#idx("method of little groups")

#proposition[
  Let $G=A ⋊ B$ be a semidirect product of an abelian normal subgroup $A$ and a
  subgroup $B$. Then the following statements hold:

  #enum(
    numbering: "(i)",
    [Every $zeta in op("Irr")_K lr((G))$ satisfies $(zeta,psi^G)>0$ for some
      $psi in op("Irr")_K lr((A))$.],
    [Each $psi in op("Irr")_K lr((A))$ can be extended to a character $psi_1$ of
      $G_psi$. Moreover $G_psi=A B_psi$, where $B_psi=G_psi inter B$, and (as in
      @th:gallagher-character-extension(iii))
      $ psi^G=sum_(omega in op("Irr")_K lr((B_psi)))omega(1)(omega psi_1)^G. $],
  )
]<prop:little-groups>
#proof[
  Let $rho_A=sum psi(1)psi$ be the regular character of $A$. Then
  $(rho_A)^G=sum psi(1)psi^G$ is the regular character of $G$, from which (i)
  follows.

  Now let $psi in op("Irr")_K lr((A))$. Then $psi$ is linear because $A$ is
  abelian. It is also clear that $G_psi=A B_psi$, where $B_psi=G_psi inter B$.
  It is then easy to check that the extension $psi_1$ exists, and is defined by
  $ psi_1 lr((a b))=psi(a), a in A, b in B_psi. $
  The final statement is a consequence of Theorem
  @th:gallagher-character-extension.
]

We conclude this section with another application, where we obtain decisive
information on the irreducible characters of groups belonging to a family which
includes the important Frobenius groups (see §@ss:frobenius-groups).

Let us begin with a general result, which will be applied in several different
ways. If $H ⊴ G$, then $G$ acts on both $op("Irr")_K lr((H))$ and the conjugacy
classes in $H$, and it is not surprising that these actions are related. The
situation leads to the following:

#theorem(title: [Brauer])[
  Let $A$ be a group which acts on $op("Irr")_K lr((G))$ and on the conjugacy
  classes of $G$, in such a way that#footnote[
    In this discussion, $zeta_(frak(C))$ means $zeta(x)$ for $x in frak(C)$.
  ]
  $
    alpha(zeta)_(alpha(frak(C)))=zeta_(frak(C))
    quad "for all" alpha in A, zeta in op("Irr")_K lr((G)),
  $
  and all conjugacy classes $frak(C)$ in $G$. Then for each $alpha in A$, the
  number of irreducible characters of $G$ fixed by $alpha$ is equal to the
  number of conjugacy classes fixed by $alpha$.
]<th:brauer-permutation-lemma>
#idx("Brauer's Theorem")
#proof[
  Let $upright(bold(Z))=(zeta_j^((i)))$ be the character table matrix of $G$, as
  in @def:character-table-data. Then each element $alpha in A$ permutes the rows
  and columns of $upright(bold(Z))$, sending the row
  #source(288)
  indexed by $zeta^((i))$ to the row indexed by $alpha(zeta^((i)))$, and the
  column indexed by the conjugacy class $frak(C)_j$ to the column indexed by the
  class $alpha^(-1) lr((frak(C)_j))$. (The reason for this choice will become
  clear in a moment.) The permutation of the rows is given by left
  multiplication $upright(bold(X))(alpha)upright(bold(Z))$, and the permutation
  of the columns by right multiplication
  $upright(bold(Z))upright(bold(Y))(alpha)$, where $upright(bold(X))(alpha)$ and
  $upright(bold(Y))(alpha)$ are permutation matrices. The hypothesis implies
  that
  $ alpha(zeta^((i)))_(frak(C)_j)=zeta_(alpha^(-1) lr((frak(C)_j)))^((i)). $
  Because of the way $upright(bold(X))(alpha)$ and $upright(bold(Y))(alpha)$ are
  defined, this equation implies that
  $
    upright(bold(X))(alpha)upright(bold(Z))
    =upright(bold(Z))upright(bold(Y))(alpha).
  $
  Since $upright(bold(Z))$ is invertible, it follows that
  $upright(bold(X))(alpha)$ and $upright(bold(Y))(alpha)$ have the same trace.
  The conclusion of Theorem @th:brauer-permutation-lemma is now an immediate
  consequence of the fact that the trace of a permutation matrix is the number
  of rows or columns (in the above situation) fixed by the permutation
  corresponding to $alpha$.
]

#corollary[
  Let $H ⊴ G$, and let $G$ act by conjugation on $op("Irr")_K lr((H))$ and on
  the conjugacy classes of $H$. The number of $G$-orbits of these two
  $G$-actions coincide.
]<cor:brauer-conjugacy-orbits>
#proof[
  The preceding theorem shows that the two permutation representations of $G$,
  one on $op("Irr")_K lr((H))$, and the other on the conjugacy classes of $H$,
  have the same character $theta$. The number of $G$-orbits in a permutation
  representation with character $theta$ is given by $(theta,1_G)$, by Exercise
  @exc:permutation-character-orbits, and the result follows.
]

#theorem[
  Let $H ⊴ G$, and assume that $C_G lr((h)) <= H$ for every $h!=1$ in $H$. Then
  the following statements hold:

  #enum(
    numbering: "(i)",
    [Let $psi in op("Irr")_K lr((H))$ be a character different from $1_H$. Then
      $psi^G in op("Irr")_K lr((G))$.],
    [Let $zeta in op("Irr")_K lr((G))$, and assume that
      $H subset.not.eq ker zeta$. Then $zeta=psi^G$ for some
      $psi in op("Irr")_K lr((H))$.],
  )
]<th:normal-self-centralizing-induction>
#proof[
  (i) Because $H ⊴ G$, the Intertwining Number Theorem @th:intertwining-number
  asserts that
  $ (psi^G,psi^G)=sum_x lr((psi,attach(psi, tl: x))), $
  where the sum is taken over a set of coset representatives of $H$ in $G$. Thus
  to prove irreducibility of $psi^G$, it is sufficient to prove that
  $attach(psi, tl: x)!=psi$ for each $x in.not H$. By Theorem
  @th:brauer-permutation-lemma, the irreducibility of $psi^G$ will follow if we
  can show that for each conjugacy class $frak(C)!=1$ in $H$ and each $x in G$,
  the equality $x frak(C)x^(-1)=frak(C)$ implies that $x in H$. Let
  $h in frak(C)$; then $x frak(C)x^(-1)=frak(C)$ implies that
  $x h x^(-1)=y h y^(-1)$ for
  #source(289)
  some $y in H$, and hence $y^(-1)x in C_G lr((h))$. Since $h!=1$, the
  hypothesis implies that $y^(-1)x in H$, whence also $x in H$ since $y in H$.
  This completes the proof of (i).

  (ii) Let $zeta in op("Irr")_K lr((G))$, and assume that
  $H subset.not.eq ker zeta$. Then $zeta|_H$ has at least one component
  $psi in op("Irr")_K lr((H))$ such that $psi!=1_H$. Then
  $psi^G in op("Irr")_K lr((G))$ by part (i), and $(zeta,psi^G)!=0$ by Frobenius
  Reciprocity. It follows that $zeta=psi^G$, and
  @th:normal-self-centralizing-induction is proved.
]

=== Decomposition of Induced Modules from Normal Subgroups <ss:clifford-systems>

In this subsection, we shall settle the problem raised in §@ss:clifford-theorem
(see the remarks following Clifford’s Theorem @th:clifford-theorem). The
objective is to determine the structure of a simple $K G$-module $M$ such that
for some normal subgroup $H$ of $G$, $M_H$ contains a simple $K H$-module which
is isomorphic to all its conjugates. In case $K$ is a splitting field, the
result is due to Clifford @bib:Clifford1937 (see also @bib:CurtisReiner1962[CR
  §~51]). The solution of the problem involves projective representations. Here
we shall solve the problem for an arbitrary field $K$. Later, in
§@ss:green-indecomposability, we shall decompose induced modules $L^G$ from
normal subgroups $H$ of $G$, where $L$ is an absolutely indecomposable
$R H$-lattice, and $R$ is a discrete valuation ring.

Our approach is based on the work of Tucker (@bib:Tucker1962, @bib:Tucker1963,
@bib:Tucker1965a, @bib:Tucker1965b), and extensions and refinements of her work
by Conlon @bib:Conlon1964, Ward @bib:Ward1968, Dade @bib:Dade1970, and Cline
@bib:Cline1972. The key idea is to show that the endomorphism algebra of $L^G$
has essentially the structure of a twisted group algebra over the quotient group
$G slash H$, with coefficients in the endomorphism algebra of the $R H$-module
$L$. The work can be viewed as an extension of §@ss:intertwining-number, where
results on the structure of $Hom_(R G) lr((L^G,L^G))$ were established in
connection with the Intertwining Number Theorem.

As preparation for the discussion in this section and in §@sec:vertices-sources,
it will be useful to set up the problem in a more general context than that of
group algebras.

#definition[
  Let $S$ be a finite group, $R$ a commutative ring, and $A$ an $R$-algebra,
  f.g./$R$ as module. A family of $R$-submodules ${A_s}_(s in S)$ of $A$,
  indexed by the elements of $S$, is called an _$S$-graded Clifford system_ in
  $A$, if the following conditions are satisfied:

  #enum(
    numbering: "(i)",
    [$A_s A_t=A_(s t)$ (module product).],
    [For each $s in S$, there exists a unit $a_s in A$ such that
      $ A_s=a_s A_1=A_1 a_s. $],
    [$A=plus.o.big_(s in S)A_s$. (This decomposition is called the _grading_ of
      $A$).],
    [$1 in A_1$.],
  )

  An $R$-algebra satisfying these conditions will sometimes be called an
  _$S$-graded $R$-algebra_.
]<def:graded-clifford-system>
#idx("Clifford system")#idx("graded algebra")

#source(290)
#examples(name: "Examples", numbered: false)[
  (a) Let $H ⊴ G$, $S=G slash H$, and $A=R G$. Then $A$ has an $S$-graded
  Clifford system, where the $R$-submodule $A_s$ corresponding to a coset
  $s in G slash H$ is given by
  $ A_s=sum_(x in s)R x, $
  and the element $a_s$ can be taken as any representative $x_s$ of the coset
  $s$.

  (b) Let $H ⊴ G$, $S=G slash H$, and let $A=(R G)_alpha$ be the _twisted group
  algebra_ with factor set $alpha$, and trivial $G$-action on $R$ (see
  @exm:crossed-products-twisted-group-algebras(ii)). The algebra $(R G)_alpha$
  has an $R$-basis ${a_x}_(x in G)$, and (associative) multiplication given by
  the formulas
  $
    xi a_x=a_x xi, quad a_x a_y=alpha(x, y)a_(x y), quad forall x,y in G, xi
    in R,
  $
  for some factor set $alpha:G times G -> R^bullet$ satisfying
  @eq:multiplicative-factor-set, where, in the context of
  §@sec:ext-tor-cohomology, $G$ acts trivially on $R^bullet$: $x xi=xi$ for all
  $x in G$ and $xi in R^bullet$. Then $A$ is an $S$-graded Clifford system
  exactly as in (a), with
  $ A_s=sum_(x in s)R a_x, $
  and $a_s$ taken to be any element $a_x$, $x in s$. The fact that the elements
  ${a_s}$ are units follows from the definition of multiplication, and the
  assumption that the factor set $alpha$ takes values in the units of $R$. #idx(
    "twisted group algebra",
  )#idx("twisted group ring")

]

Returning to the general case of an $R$-algebra $A$ satisfying Definition
@def:graded-clifford-system, we first note that $A_1$ is an $R$-subalgebra of
$A$, and that we may take $a_1=1$. Moreover, $A$ is a free right and left
$A_1$-module with basis ${a_s}_(s in S)$. It also follows from the definition
that
$
  a_s a_t a_(s t)^(-1) in A_1, quad a_s A_1 a_s^(-1) subset.eq A_1, quad s,t
  in S.
$
Thus
$
  a_s a_t=alpha(s, t)a_(s t), quad s,t in S, "where" alpha(s, t) in A_1^bullet,
$
and for each $xi in A_1$ and $s in S$,
$ a_s xi=xi^s a_s, quad "for some" xi^s in A_1. $
Therefore an $S$-graded Clifford system is a generalization of the idea of a
twisted group algebra considered in Example (b), with coefficients in the
possibly noncommutative ring $A_1$.

For a left $A_1$-module $L$, we shall denote by $L^A$, or by
$op("ind")_(A_1)^A lr((L))$ when there is risk of confusion, the _induced_
$A$-module $A times.o_(A_1)L$ (see §@ss:induction-frobenius). #idx(
  "induced module",
) Similarly, if $M$
#source(291)
is a left $A$-module, we denote by $M_(A_1)$, or $op("res")_(A_1)^A lr((M))$,
the $A_1$-module obtained by restriction of scalars from $A$ to $A_1$.

In the discussion to follow, all modules are assumed to be f.g./$R$. The symbol
$times.o$ will denote $times.o_(A_1)$, until later in the subsection, when
several tensor products have to be considered at once.

For each $A_1$-module $L$, we have
$ L^A=plus.o.big_(s in S)a_s A_1 times.o L=plus.o.big_(s in S)a_s times.o L, $
because $A$ is a free right $A_1$-module with basis ${a_s}_(s in S)$. By part
(ii) of Definition @def:graded-clifford-system, we have $A_1 a_s=a_s A_1$ for
all $s in S$; hence all of the $R$-submodules ${a_s times.o L}$ are also
$A_1$-submodules of $L^A$, and are called the conjugates of $L$ in $L^A$. Since
the elements ${a_s}$ are units in $A$, left multiplication by $a_s$ defines an
$R$-isomorphism
$ 1 times.o L tilde.equiv a_s lr((1 times.o L))=a_s times.o L. $
We also note that $L tilde.equiv 1 times.o L$ as $A_1$-modules, and that
$a_s times.o L=a'_s times.o L$ as $A_1$-modules for any two units $a_s$ and
$a'_s$ of $A$ contained in $A_s$. A left $A_1$-module $L$ is called _stable_ (or
stable relative to $A$) if $L$ is $A_1$-isomorphic to all its conjugates. #idx(
  "stable module",
) In the situation of Example (a), a left $R H$-module $L$ is stable if and only
if it is isomorphic to all its conjugates ${attach(L, tl: x)}_(x in G)$.

In the course of our discussion, we shall require both versions of Frobenius
Reciprocity considered earlier (see @th:frobenius-reciprocity and
@prop:frobenius-right-adjoint) in a slightly generalized form, as follows. In
this result, and subsequently in this subsection, we shall write homomorphisms
of modules on the opposite side from the scalars, as in §@ss:morita-theorems.

#proposition(title: [Frobenius Reciprocity])[
  Let $A$ be an $R$-algebra with an $S$-graded Clifford system, and let $L$ be a
  left $A_1$-module, and $M$ a left $A$-module.

  #enum(
    numbering: "(i)",
    [There is an isomorphism of $R$-modules
      $ Hom_(A_1) lr((L,M_(A_1))) tilde.equiv Hom_A lr((L^A,M)), $
      given by $phi arrow.r hat(phi)$, where
      $
        (a times.o l)hat(phi)=a(l phi), quad a in A, l in L, phi in Hom_(A_1)
        lr((L,M_(A_1))).
      $
      If we embed $L$ in $L^A$ using the isomorphism of $A_1$-modules
      $L tilde.equiv 1 times.o L$, then the restriction of $hat(phi)$ to
      $1 times.o L$ coincides with $phi$:
      $
        (1 times.o l)hat(phi)=l phi, quad l in L, phi in Hom_(A_1)
        lr((L,M_(A_1))).
      $],
    [There is an isomorphism of $R$-modules,
      $ Hom_(A_1) lr((M_(A_1),L)) tilde.equiv Hom_A lr((M,L^A)), $
      #source(292)
      which assigns to each $A_1$-homomorphism $theta:M_(A_1) -> L$ the
      homomorphism $tilde(theta):M -> L^A$ given by
      $
        tilde(theta)(m)=sum_(s in S)a_s times.o theta(a_s^(-1)m), quad m in M.
      $],
  )
]<prop:graded-frobenius-reciprocity>
#idx("Frobenius Reciprocity Theorem")
#proof(head: emph[Sketch of Proof.])[
  The proof of (i) is the same as the proof of @th:frobenius-reciprocity, and is
  omitted. Likewise, the proof of (ii) is an easy adaptation of the proof of
  @prop:frobenius-right-adjoint. The key point is the verification that
  $tilde(theta)$, defined as above, is an $A$-homomorphism. To prove this, first
  let $x in A_1$; then
  $ tilde(theta)(x m)=sum_(s in S)a_s times.o theta(a_s^(-1)x m). $
  From the remarks about Clifford systems following the examples, for each
  $s in S$ we may write $x a_s=a_s y$ for some $y in A_1$. Then
  $a_s^(-1)x=y a_s^(-1)$, so for $m in M$,
  $
    a_s times.o theta(a_s^(-1)x m)&=a_s times.o theta(y a_s^(-1)m)
    =a_s times.o y theta(a_s^(-1)m)\
    &=a_s y times.o theta(a_s^(-1)m)=x{a_s times.o theta(a_s^(-1)m)}.
  $
  This shows that $tilde(theta)(x m)=x tilde(theta)(m)$ for all $x in A_1$,
  $m in M$. It now suffices to prove that
  $tilde(theta)(a_t^(-1)m)=a_t^(-1)tilde(theta)(m)$ for all $t in S$, $m in M$.
  We have
  $ tilde(theta)(a_t^(-1)m)=sum_(s in S)a_s times.o theta(a_s^(-1)a_t^(-1)m), $
  and by the preliminary remarks, $a_s^(-1)a_t^(-1)=beta_(s t)a_(t s)^(-1)$ for
  some $beta_(s t) in A_1$. Then $a_s beta_(s t)=a_t^(-1)a_(t s)$, and
  $
    tilde(theta)(a_t^(-1)m)=sum_(s in S)a_s beta_(s t) times.o theta(
      a_(t
      s)^(-1)m
    )
    =a_t^(-1)sum_(s in S)a_(t s) times.o theta(a_(t s)^(-1)m).
  $
  Because $S$ is a finite group, this shows that $tilde(theta)$ is an
  $A$-homomorphism. The rest of the proof is left as an exercise.

]

#proposition[
  Let $A$ have an $S$-graded Clifford system, let $L$ be a left $A_1$-module,
  and let $E$ denote the endomorphism algebra $End_A L^A$, viewed as a ring of
  right operators on $L^A$. For each $s in S$, let
  $ E_s={f in E:(1 times.o L)f subset.eq a_s times.o L}. $
  Then

  #enum(
    numbering: "(i)",
    [For all $s,t in S$, we have
      $
        A_s lr((a_t times.o L))=a_(s t) times.o L; quad
        (a_s times.o L)E_t subset.eq (a_(s t) times.o L);
      $
      $
        E_s E_t subset.eq E_(s t), quad 1 in E_1, quad E=plus.o.big_(s in S)E_s.
      $
      #source(293)],
    [Each element $phi in Hom_(A_1) lr((1 times.o L,a_s times.o L))$ extends to
      a unique element $hat(phi) in E_s$, given by
      $(a times.o l)hat(phi)=a((1 times.o l)phi)$ for $l in L$, $a in A$. The
      map $phi arrow.r hat(phi)$ defines an isomorphism of $R$-modules
      $
        Hom_(A_1) lr((1 times.o L,a_s times.o L)) tilde.equiv E_s, quad s in S,
      $
      and this is an isomorphism of $R$-algebras when $a_s=1$.],
    [If $L$ is stable and $R$ is noetherian, then $E$ has an $S$-graded Clifford
      system, with units $hat(e)_s in E_s$ defined by (ii) from
      $A_1$-isomorphisms $e_s:1 times.o L arrow.r^tilde a_s times.o L$, for all
      $s in S$.],
  )
]<prop:graded-endomorphism-algebra>
#proof[
  (i) We have
  $
    A_s lr((a_t times.o L))=a_s A_1 lr((a_t times.o L))
    =a_s lr((A_1 a_t times.o L))
    =a_s lr((a_t A_1 times.o L))=a_s a_t times.o L=a_(s t) times.o L,
  $
  since $A_1 a_t=a_t A_1$ for $t in S$, and $a_(s t)$ differs from $a_s a_t$ by
  an element of $A_1^bullet$. We next obtain
  $
    (a_s times.o L)E_t=a_s lr((1 times.o L))E_t
    subset.eq a_s lr((a_t times.o L))=a_s a_t times.o L=a_(s t) times.o L,
  $
  by the definition of $E_t$. From this fact we have
  $
    (1 times.o L)E_s E_t subset.eq (a_s times.o L)E_t subset.eq a_(s t)
    times.o L,
  $
  and hence $E_s E_t subset.eq E_(s t)$. Clearly $1 in E_1$. We postpone showing
  that $E=plus.o.big E_s$ until after we prove (ii).

  (ii) By Proposition @prop:graded-frobenius-reciprocity with $M=L^A$, each
  $phi in Hom_(A_1) lr((1 times.o L,a_s times.o L))$ extends to an element
  $hat(phi) in E$ satisfying
  $ (a times.o l)hat(phi)=a((1 times.o l)phi). $
  Then $(1 times.o L)hat(phi)=(1 times.o L)phi subset.eq a_s times.o L$, so
  $hat(phi) in E_s$. The map $phi arrow.r hat(phi)$ is $R$-injective, by
  @prop:graded-frobenius-reciprocity. Moreover, if $f in E_s$, then
  $phi=f|_(1 times.o L)$ is an $A_1$-homomorphism from $1 times.o L$ to
  $a_s times.o L$, and
  $
    (a times.o l)f=(a(1 times.o l))f=a((1 times.o l)phi) quad "for all" l in L,
  $
  so that $f=hat(phi)$. Therefore the map $phi arrow.r hat(phi)$ is surjective.
  It is clear from the definition of $hat(phi)$ that the map
  $phi arrow.r hat(phi)$ is an isomorphism of $R$-algebras
  $End_(A_1) lr((1 times.o L)) tilde.equiv E_1$, and (ii) is proved.

  We can now prove that $E=plus.o.big_s E_s$. If $f in E$, then since
  $L^A=plus.o.big a_s times.o L$, we have
  $ f|_(1 times.o L)=sum_s f_s, $
  #source(294)
  where $f_s in Hom_(A_1) lr((1 times.o L,a_s times.o L))$. Then
  $f=sum_s hat(f)_s$, where $hat(f)_s in E_s$ is the extension of $f_s$ defined
  in (ii), because both sides agree on $1 times.o L$, and $1 times.o L$ generate
  $L^A$ as $A$-module. This proves that $E=sum_s E_s$. To show that the sum is
  direct, suppose that $sum hat(f)_s=0$, where $hat(f)_s in E_s$. Then clearly
  each $hat(f)_s|_(1 times.o L)=0$, and by the proof of part (ii),
  $hat(f)_s=hat(hat(f)_s|_(1 times.o L))=0$. This proves that
  $E=plus.o.big_s E_s$.

  (iii) Now let $L$ be stable, and for each $s in S$, let
  $e_s:1 times.o L arrow.r^tilde a_s times.o L$ be an $A_1$-isomorphism. Then
  each extension $hat(e)_s$ defined in (ii) belongs to $E_s$, and satisfies
  $
    (a_t times.o L)hat(e)_s=a_t lr(((1 times.o L)hat(e)_s))
    =a_t lr((a_s times.o L))=a_(t s) times.o L quad "for all" t in S.
  $
  Because $S$ is a finite group, it follows that
  $ L^A hat(e)_s=(sum_t a_t times.o L)hat(e)_s=sum_t a_(t s) times.o L=L^A, $
  and hence $hat(e)_s$ is a unit in $E$ by
  @prop:surjective-noetherian-endomorphism. Finally, we have to prove that
  $ E_1 hat(e)_s=hat(e)_s E_1=E_s, quad "and" E_s E_t=E_(s t), $
  for all $s,t in S$. We have, by (i),
  $ E_1 hat(e)_s subset.eq E_1 E_s subset.eq E_s. $
  But also $E_s hat(e)_s^(-1) subset.eq E_1$, using the definition of $hat(e)_s$
  and the fact that it is invertible. Thus $E_1 hat(e)_s=E_s$. On the other
  hand, $(a_(s^(-1)) times.o L)hat(e)_s subset.eq 1 times.o L$ by (i), so
  $hat(e)_s^(-1) in E_(s^(-1))$, and we have by (i):
  $
    hat(e)_s E_1 subset.eq E_s, quad "and"
    hat(e)_s^(-1)E_s subset.eq E_(s^(-1))E_s subset.eq E_1,
  $
  proving that $hat(e)_s E_1=E_s$. Moreover, from what has been proved,
  $hat(e)_(s t)^(-1)hat(e)_s hat(e)_t in E_1$, and hence
  $
    E_s E_t=hat(e)_s E_1 hat(e)_t E_1=hat(e)_s hat(e)_t E_1
    =hat(e)_(s t)E_1=E_(s t),
  $
  completing the proof of (iii).
]

We remark that in case $L$ is stable and $R$ is noetherian, then $E$ has an
$S$-graded Clifford system over $E_1$, and hence is a twisted group algebra over
the endomorphism algebra of $L$, by the remarks preceding the proof.

We now begin the main theme of this subsection: the analysis of $L^A$, in case
$L$ is a simple $A_1$-module, and the coefficient ring over which $A$ is defined
is a field $K$.

#source(295)
#proposition[
  Let $A$ have an $S$-graded Clifford system over a field $K$, and let $L$ be a
  simple $A_1$-module. Then $E_1$ is a f.d. division algebra over $K$, and
  $ T={t in S:1 times.o L tilde.equiv a_t times.o L "as" A_1 "-modules"} $
  is a subgroup of $S$. Further
  $ E_T=sum_(t in T)E_t, $
  is a $T$-graded $K$-algebra.
]<prop:graded-inertia-subgroup>
#proof[
  By Proposition @prop:graded-endomorphism-algebra(ii), $E_1=End_(A_1)L$, and
  $E_1$ is a division algebra because $L$ is simple. We next prove that an
  element $t in S$ belongs to $T$ if and only if $E_t$ contains a unit. If $e_t$
  is a unit in $E_t$, then $(1 times.o L)e_t subset.eq a_t times.o L$, and
  $ker(e_t|_(1 times.o L))=0$. From our preliminary remarks, $1 times.o L$ and
  $a_t times.o L$ are $K$-isomorphic, and so $(1 times.o L)e_t=a_t times.o L$ by
  counting dimensions over the field $K$. Therefore $e_t$ defines an
  $A_1$-isomorphism, as required, and thus $t in T$. Conversely, if $t in T$,
  and $phi:1 times.o L arrow.r^tilde a_t times.o L$ is an $A_1$-isomorphism, it
  follows from Proposition @prop:graded-endomorphism-algebra that
  $hat(phi) in E_t$, and that $hat(phi)$ is a unit in $E$. The above
  observation, combined with the fact that $E_s E_t subset.eq E_(s t)$, shows
  that $T$ is a subgroup of $S$. The rest of the proof is an immediate
  application of Proposition @prop:graded-endomorphism-algebra(iii) to the
  $A_1$-module $L$, which is stable relative to the $T$-graded Clifford system
  $B=plus.o.big_(t in T)A_t$. Here $E_T=plus.o.big_(t in T)E_t$ can be
  identified with the $B$-endomorphism algebra of $L^B$ (see Exercise
  @exc:graded-endomorphism-restriction). This completes the proof.
]

#idx("Clifford's Theorem")
The next result is a generalization of Clifford’s Theorem @th:clifford-theorem.

#proposition[
  Let $A$ be an $S$-graded Clifford system over a field $K$, $M$ a simple
  $A$-module, and $L$ a simple submodule of $M_(A_1)$. Then the following
  statements hold:

  #enum(
    numbering: "(i)",
    [$M_(A_1)$ is a semisimple $A_1$-module, whose simple summands are
      isomorphic to conjugates ${a_s times.o L:s in S}$ of $L$.],
    [Let $T={t in S:L tilde.equiv a_t times.o L "as" A_1 "-modules"}$, and let
      $B=sum_(t in T)A_t$. Then the homogeneous component $N$ of $M_(A_1)$
      containing $L$ is a $B$-module, and $M$ is $A$-isomorphic to the induced
      module $A times.o_B N$.],
    [$N$ is a simple submodule of $L^B$, and $L$ is stable relative to $B$.],
  )
]<prop:graded-clifford-theorem>
#proof(head: emph[Sketch of Proof.])[
  The proofs of parts (i) and (ii) are essentially the same as the proofs of the
  corresponding parts of Theorem @th:clifford-theorem, and are left as
  exercises. The starting point is the observation that $T$ is a subgroup of
  $S$, by Proposition @prop:graded-inertia-subgroup. Let ${s_1,dots,s_m}$ be a
  set of coset representatives of $S slash T$; then it is not difficult to prove
  that $A$ is a free right $B$-module, with basis
  #source(296)
  ${a_(s_1),dots,a_(s_m)}$. It can then be shown that $M$ is a direct sum of the
  modules ${a_s times.o N}$ and that $M tilde.equiv A times.o_B N$, as in the
  proof of Theorem @th:clifford-theorem.

  Using (ii), it follows that $N$ is a simple $B$-module; otherwise, if $N_1$ is
  a proper $B$-submodule of $N$, then $sum_(i=1)^m a_(s_i) times.o N_1$ is a
  proper $A$-submodule of $A times.o_B N$. The latter is a simple $A$-module by
  part (ii), and we have reached a contradiction. We now apply Proposition
  @prop:graded-frobenius-reciprocity(ii) to deduce that because $L$ is an
  $A_1$-submodule of $N$, there is a nonzero homomorphism from $N$ to $L^B$.
  Since $N$ is simple, this shows that $N$ is isomorphic to a submodule of
  $L^B$. Finally, $L$ is a $B$-stable submodule of $N$ because $N$ is a
  homogeneous component of $M_(A_1)$, and because of the way $T$ is defined.
  This completes the proof.

]

By Propositions @prop:graded-inertia-subgroup and @prop:graded-clifford-theorem,
a simple $A$-module is constructed in two stages. The first step is induction
from a simple $B$-module $N$, for a $T$-graded Clifford system $B$ associated
with a subgroup $T$ of $S$. The second stage is the analysis of the structure of
a simple submodule $N$ of $L^B$, for a simple $A_1$-module $L$ which is stable
relative to $B$. The latter problem was left open in §@ss:clifford-theorem, and
is settled by the following theorem:

#theorem[
  Let $A$ be an $S$-graded $K$-algebra, where $K$ is a field, and let $L$ be a
  simple $A_1$-module which is stable relative to $A$. Let $E=End_A L^A$.

  #enum(
    numbering: "(i)",
    [There is an isomorphism $theta$ from the lattice of left ideals $I$ in $E$
      onto the lattice of $A$-submodules $U$ of $L^A$, given by
      $ U=L^A dot I, quad I={gamma in E:L^A gamma subset.eq U}. $],
    [The $A$-module $L^A dot I$ corresponding to $I$ is $A$-isomorphic to
      $L times.o_(E_1)I$, where the action of $A$ on this tensor product is
      given by
      $
        a(l times.o gamma)=(a l)hat(e)_s^(-1) times.o hat(e)_s gamma
        quad "for" a in A_s, l in L, gamma in I,
      $
      with $E_1$ and the units ${hat(e)_s}$ in $E_s$ defined as in
      @prop:graded-endomorphism-algebra. Furthermore,
      $ dim_K lr((L times.o_(E_1)I))=(dim_(E_1)L)(dim_K I). $],
    [The lattice isomorphism $theta$ is functorial, in the sense that
      $E$-homomorphisms $f:I -> I'$, between left ideals of $E$, correspond
      bijectively to $A$-homomorphisms
      $1 times.o f:L times.o_(E_1)I -> L times.o_(E_1)I'$.],
  )
]<th:graded-clifford-correspondence>
#proof[
  We first recall that in this situation, by Propositions
  @prop:graded-endomorphism-algebra and @prop:graded-inertia-subgroup, $E$ has
  an $S$-graded Clifford system, and $E_1$ is a f.d. division algebra over $K$.
  The units $hat(e)_s in E_s$ correspond as in
  @prop:graded-endomorphism-algebra(iii) to $A_1$-isomorphisms
  $e_s:1 times.o L arrow.r^tilde a_s times.o L$, $s in S$. The argument now
  proceeds in a number of steps.

  _Step 1._ We show first that $L^A$ is a free right $E$-module. Let
  ${l_1,dots,l_m}$ be a basis of $1 times.o L$ over the division algebra $E_1$;
  we shall prove that these elements
  #source(297)
  form an $E$-basis of $L^A$. We have
  $
    a_s times.o L=(1 times.o L)hat(e)_s
    =(sum_i l_i E_1)hat(e)_s=sum_i l_i lr((E_1 hat(e)_s)),
  $
  and hence the elements ${l_i}$ generate $L^A$ over $E$. Next, let
  $ sum_i l_i e_i=0, quad e_i in E. $
  Each element $e_i$ can be expressed in the form
  $ e_i=sum_(s in S)xi_(i s)hat(e)_s, quad xi_(i s) in E_1, $
  and we have
  $ sum_s sum_i l_i xi_(i s)hat(e)_s=0. $
  Then
  $ sum_i l_i xi_(i s)=0, quad s in S, $
  because
  $ (sum_i l_i xi_(i s))hat(e)_s in a_s times.o L, $
  and the sum $sum_s a_s times.o L$ is direct. Finally, each $xi_(i s)=0$
  because of the independence of the elements ${l_i}$ over $E_1$.

  _Step 2._ Let $I$ be a left ideal of $E$. Since $L^A$ is a free right
  $E$-module, the inclusion map $i:I -> E$ extends to a monomorphism
  $ 1 times.o i:L^A times.o_E I -> L^A times.o_E E $
  by @prop:projective-is-flat, and $L^A times.o_E E tilde.equiv L^A$ by
  @eq:tensor-regular-module. The image of $1 times.o i$ in $L^A$ is clearly
  $L^A I$, so we have
  $ L^A times.o_E I tilde.equiv L^A dot I. $

  _Step 3._ Given a left ideal $I$ of $E$, set $U=L^A I$, an $A$-submodule of
  $L^A$. We claim that
  $ I={gamma in E:L^A dot gamma subset.eq U}. $
  #source(298)
  Since $L^A=A(1 times.o L)$, it is clear that
  $
    {gamma in E:L^A gamma subset.eq U}={gamma in E:(1 times.o L)gamma
      subset.eq U}.
  $
  Next, by Step 1, a right $E_1$-basis ${l_j}$ of $1 times.o L$ is also an
  $E$-basis of $L^A$. It follows that each element of $U$ can be expressed in
  the form $sum l_j gamma_j$, with uniquely determined coefficients ${gamma_j}$
  in $I$. Hence if $(1 times.o L)gamma subset.eq U$, then $gamma in I$. This
  shows that ${gamma in E:L^A dot gamma subset.eq U}
  subset.eq I$; the reverse inclusion is obvious, and the equality is
  established.

  _Step 4._ Now let $U$ be an arbitrary $A$-submodule of $L^A$, and define $I$
  as in Step 3, so $I$ is a left ideal of $E$ such that $L^A dot I subset.eq U$.
  In order to prove that equality holds, we again start with an $E_1$-basis
  ${l_j}$ of $1 times.o L$. Suppose that $sum l_j gamma_j in U$, $gamma_j in E$;
  we must prove that each $gamma_j in I$. Since $E_1=End_(A_1)1 times.o L$, and
  $1 times.o L$ is a simple $A_1$-module, it follows from the Density Theorem
  @th:density that, for each $i$, there exists an element $a_i in A_1$ such that
  $a_i l_i=l_i$, $a_i l_j=0$ for $j!=i$. Then (for each $i$)
  $ a_i lr((sum l_j gamma_j))=l_i gamma_i in U. $
  Therefore also $(A_1 l_i)gamma_i subset.eq U$. But $A_1 l_i=1 times.o L$ since
  $1 times.o L$ is simple, so we have $(1 times.o L)gamma_i subset.eq U$, and
  therefore $gamma_i in I$, as desired. This completes the proof that $L^A I=U$,
  and shows that the correspondence $I arrow.l.r U$ is indeed a lattice
  isomorphism.

  _Step 5._ We now prove assertion (ii) of the theorem. We have
  $L^A=sum_s lr((1 times.o L))hat(e)_s$, and $hat(e)_s I=I$ for each $s in S$,
  and hence
  $ L^A I=sum_s lr((1 times.o L))hat(e)_s I=(1 times.o L)I. $
  Now let ${l_j}$ be a right $E_1$-basis of $1 times.o L$. By Step 1, we have
  $
    (1 times.o L)I=plus.o.big l_j I, quad
    L times.o_(E_1)I=plus.o.big(l_j times.o I),
  $
  the latter because tensor products commute with direct sums. Since both
  $l_j I$ and $l_j times.o I$ are isomorphic to $I$ as $K$-spaces, there exists
  a $K$-isomorphism
  $
    L^A I=(1 times.o L)I tilde.equiv L times.o_(E_1)I.
  $ <eq:graded-clifford-tensor-identification>
  If we identify $L$ with the $A_1$-submodule $1 times.o L$ of $L^A$, then the
  isomorphism in @eq:graded-clifford-tensor-identification is given by
  $ l gamma arrow.r l times.o gamma, quad l in L, gamma in I. $
  #source(299)
  If $a in A_s$, then for $l in L$, $gamma in I$, we have
  $ a(l gamma)=(a l hat(e)_s^(-1))hat(e)_s gamma, $
  with $a l hat(e)_s^(-1) in L$, $hat(e)_s gamma in I$. The isomorphism in
  @eq:graded-clifford-tensor-identification maps this element onto
  $ a l hat(e)_s^(-1) times.o hat(e)_s gamma in L times.o_(E_1)I. $
  Thus if the action of $A$ on $L times.o_(E_1)I$ is defined as in part (ii) of
  the theorem, the $K$-isomorphism @eq:graded-clifford-tensor-identification
  becomes an $A$-isomorphism, and Step 5 is finished.

  _Step 6._ As in Step 2, we can identify $L^A I$ with $L^A times.o_E I$, for
  each left ideal $I$ in $E$. Clearly each $E$-homomorphism $f:I -> I'$ defines
  an $A$-homomorphism $1 times.o f:L^A times.o_E I -> L^A times.o_E I'$.
  Conversely, let $g:L^A I -> L^A I'$ be an $A$-homomorphism, where $I$ and $I'$
  are left ideals in $E$. For each $gamma in I$, the map
  $ 1 times.o l arrow.r ((1 times.o l)gamma)g, quad l in L, $
  lies in $Hom_(A_1) lr((1 times.o L,L^A))$; hence, by reciprocity
  @prop:graded-frobenius-reciprocity, there is a unique element
  $hat(gamma) in E$ such that
  $ (1 times.o l)hat(gamma)=((1 times.o l)gamma)g in L^A I', quad l in L. $
  By Step 3, $hat(gamma) in I'$, and it is easily checked that the map
  $gamma arrow.r hat(gamma)$ is an $E$-homomorphism from $I$ to $I'$, which we
  denote by $f$. Finally, to prove that $g=1 times.o f$, it is sufficient to
  check that both agree on $(1 times.o L)I$, since both are $A$-homomorphisms,
  and $A((1 times.o L)I)=L^A dot I$. For $l in L$ and $gamma in I$, we have
  $
    ((1 times.o l)gamma)(1 times.o f)=(1 times.o l)(gamma f)
    =(1 times.o l)hat(gamma)=((1 times.o l)gamma)g.
  $
  Hence $g=1 times.o f$, and Step 6 is done.

  This completes the proof of all parts of the theorem except the statement in
  part (ii) about dimensions, which we leave as an exercise.
]

Our final topic in this subsection is the long-awaited application of Theorem
@th:graded-clifford-correspondence to complete the discussion of Clifford’s
Theorem. (A more direct approach was given in @bib:CurtisReiner1962[CR §~51].)

#definition[
  Let $K$ be a field, and $G$ a finite group. A _projective representation_ of
  $G$, with _factor set_ $alpha$, is a map $T:G -> GL(M)$ for some f.d. vector
  space $M$ over $K$, such that
  $ T(x)T(y)=alpha(x, y)T(x y), quad x,y in G, $
  where $alpha$ is a map from $G times G$ taking values in the multiplicative
  group $K^bullet$ of nonzero elements of $K$.
]<def:projective-representation>
#idx("projective representation")#idx("factor set")

#source(300)
Using the associative law in $G$ and in $GL(M)$, it is easily checked that the
map $alpha$ defined above is a factor set in the sense of
@eq:multiplicative-factor-set, with $A=K^bullet$, and with trivial action of $G$
on $K^bullet$. In §@ss:central-extensions below, we shall give a more extensive
discussion of projective representations in the context of central extensions
(see also @bib:CurtisReiner1962[CR §~53]).

The following theorem shows that projective representations arise in an
unavoidable way in completing the analysis of simple $K G$-modules $M$ in the
stable case (see the remarks following Theorem @th:clifford-theorem).

#theorem(title: [Clifford @bib:Clifford1937])[
  Let $H$ be a normal subgroup of $G$, and let $K$ be an algebraically closed
  field. Let $M$ be a simple $K G$-module, and $L$ a simple $K H$-submodule of
  $M_H$ such that $L$ is stable relative to $G$ (that is, $L$ is isomorphic to
  all of its conjugates). Set $S=G slash H$. Then
  $ M tilde.equiv L times.o_K I $
  for a left ideal $I$ in the $S$-graded algebra $E=End_(K G)L^G$. The
  $G$-action on $L times.o_K I$ is given by
  $ x arrow.r U(x) times.o V(x), quad x in G, $
  where $U:G -> GL(L)$ is a projective representation of $G$ on $L$, and
  $V:G -> GL(I)$ is a projective representation of $S$, that is, $V(x)$ depends
  only on the coset $x H$ of $x$ in $S$, for each $x in G$. The factor sets
  associated with $U$ and $V$ are inverses of each other.
]<th:clifford-projective-factorization>
#idx("Clifford's Theorem")
#proof[
  We view $K G$ as an $S$-graded Clifford system, as in Example (a) following
  Definition @def:graded-clifford-system. Then $K H$ plays the role of $A_1$,
  and $L$ is a stable $K H$-module relative to $K G$. Since $K$ is algebraically
  closed, we can identify the division algebra $E_1$ with $K$. The $S$-graded
  Clifford system $E=End_(K G)L^G$ becomes, in this case, a twisted group
  algebra $(K S)_alpha$, as in Example (b) following
  @def:graded-clifford-system, with a $K$-basis ${hat(e)_s}_(s in S)$, and
  multiplication given by
  $ hat(e)_s hat(e)_t=alpha(s, t)hat(e)_(s t), quad s,t in S, $
  for some factor set $alpha:S times S -> K^bullet$. By part (ii) of Proposition
  @prop:graded-frobenius-reciprocity, $M$ is isomorphic to an $A$-submodule of
  $L^G$, hence by part (ii) of Theorem @th:graded-clifford-correspondence, we
  have
  $ M tilde.equiv L times.o_K I $
  for some left ideal $I$ in $E$. The $G$-action on $M$ is given by
  $
    x(l times.o gamma)=(x l)hat(e)_s^(-1) times.o hat(e)_s gamma,
    quad x in G, gamma in I,
  $
  where $s$ is the coset in $S=G slash H$ containing $x$. We define
  $ U(x)l=(x l)hat(e)_s^(-1), quad V(x)gamma=hat(e)_s gamma, $
  #source(301)
  for $x in G$ and $s in S$ as above. It is then clear that $V$ defines a
  projective representation of $S$ on $I$ with factor set $alpha$. Moreover, the
  action of $G$ on $M$ is given by
  $ x arrow.r U(x) times.o V(x), quad x in G, $
  and it follows from this that $U$ is a projective representation of $G$ on $L$
  with factor set $alpha^(-1)$, completing the proof.
]

#remark(numbered: false)[
  It is useful to make a few comments about the structure of the projective
  representation $U$ on $L$, in @th:clifford-projective-factorization. For each
  fixed $x in G$, the map
  $ U(x):l arrow.r x l hat(e)_s^(-1), quad l in L, $
  is an isomorphism of vector spaces $L tilde.equiv U(x)L$, such that for all
  $h in H$, $l in L$, we have
  $ h U(x)l=x(x^(-1)h x)l hat(e)_s^(-1)=U(x)(h^x l). $
  Thus $U(x)$ defines a $K H$-isomorphism between $L$ and its conjugate
  $attach(L, tl: x)$, for each $x in G$ (see §@ss:mackey-theorems). We also
  have, if $hat(e)_1=1$,
  $ U(h)l=h l, quad h in H, l in L, $
  so $U$ extends the action of $H$ on $L$. Thus, if the factor set associated
  with either $U$ or $V$ is identically 1, it follows that the action of $H$ on
  the $G$-stable module $L$ can be extended to an action of $G$.

  Suppose next that $U':G -> GL(L)$ is another projective representation of $G$
  on $L$, such that $U'$ extends the action of $H$ on $L$, satisfies
  $U'(x h)=U'(x)U'(h)$ for $x in G$, $h in H$, and such that for each $x in G$,
  $U'(x)$ gives a $K H$-isomorphism $L arrow.r^tilde attach(L, tl: x)$ as above.
  Since $L$ is absolutely simple, it is easy to prove that $U'$ is equivalent to
  $U$, in the sense that there exists a map $xi:G -> K^bullet$ such that
  $ U'(x)=xi(x)U(x), quad x in G $
  (see §@ss:central-extensions). Given such a $U'$, we can modify the
  representation $V$ occurring in @th:clifford-projective-factorization
  accordingly, by setting
  $ V'(x)=xi(x)^(-1)V(x), quad x in G. $
  Then $V'$ is also a projective representation of $G slash H$, and we
  have#ed-note[
    The printed remark omits the condition $U'(x h)=U'(x)U'(h)$, which ensures
    that $xi$ is constant on $H$-cosets. Without it, take
    $G=⟨g⟩ tilde.equiv ZZ slash 4ZZ$, $H=⟨g^2⟩$, and $L=M=CC$ with trivial
    action, so $U=V=1$. Set $xi(1)=xi(g^2)=xi(g)=1$ and $xi(g^3)=2$. Then
    $U'=xi$ is projective, extends $H$, and intertwines its trivial action, but
    $V'=xi^(-1)$ does not factor through $G slash H$.
  ]
  $ U times.o V tilde.equiv U' times.o V'. $
]

=== Hecke Algebras and Induced Modules <ss:hecke-algebras>

In §@ss:clifford-character-theory, @ss:clifford-systems[C], we discussed the
decomposition of modules induced from normal subgroups. In this subsection, we
consider the more general situation of modules induced from arbitrary subgroups.
In order to obtain sharp results,
#source(302)
however, we shall restrict the base field $K$ to be a subfield of the complex
numbers, such that $K$ is a splitting field for $G$ and all its subgroups, as in
§@ss:clifford-character-theory. We shall pay special attention to characters
induced from linear characters of subgroups of $G$, and in particular, to the
decomposition of transitive permutation representations of $G$. The main results
are due to Curtis–Fossum @bib:Curtis1968 and Ree. As mentioned earlier, these
results will be essential for the representation theory of finite groups of Lie
type (Chapter~7 of Volume~II).

As in §@ss:finite-group-character-orthogonality, characters of a group $G$ will
always be viewed as the restrictions to $G$ of characters of the group algebra
$K G$. We shall use the notation $op("Irr")G$ to denote the characters of a
basic set of simple $K G$-modules, and also for the restrictions of these
characters to $G$.

It will sometimes be convenient to identify the group algebra $K G$ with the set
of $K$-valued functions $f$ on $G$, with the element $sum alpha_x x in K G$
corresponding to the function $f:G -> K$ defined by $f(x)=alpha_x$, $x in G$,
$alpha_x in K$. The operation of multiplication in $K G$ carries over to
_convolution_#idx("convolution") of the corresponding functions. If $f$ and $g$
are $K$-valued functions on $G$, their convolution product $f dot g:G -> K$ is
the function defined by
$ (f dot g)(x)=sum_(y in G)f(x y)g(y^(-1)), quad x in G. $
Then $K G$ is isomorphic (as $K$-algebra) to the algebra of functions
$f:G -> K$, multiplied using the convolution product.

#proposition[
  Let $H <= G$, and let $e in K H$ be an idempotent such that the left ideal
  $K H e$ affords the $K$-character $psi$ of $H$. Then $K G e$ affords the
  induced character $psi^G$. Moreover, if $zeta in op("Irr")G$, then
  $ (zeta,psi^G)=zeta(e)=dim_K e M, $
  where $M$ is a $K G$-module affording $zeta$.
]<prop:hecke-character-multiplicity>
#proof[
  For the first statement, it is easily checked that, since $K G$ is a free
  right $K H$-module, there is an isomorphism of left $K G$-modules
  $ K G e=K G dot K H e tilde.equiv K G times.o_(K H)K H e; $
  hence $K G e$ affords $psi^G$. For the second statement, we have
  $ zeta(e)=op("Tr")(e,M)=dim_K e M, $
  since $e$ is an idempotent. By Exercise @exc:idempotent-multiplicities,
  $e M tilde.equiv Hom_(K G) lr((K G e,M))$, and the dimension of the latter is
  equal to the scalar product of characters $(zeta,psi^G)$ by
  @prop:character-scalar-products-multiplicities(iii). This completes the proof.
]

Let $e$ be an idempotent in $K G$. By @lem:idempotent-corner-endomorphisms, the
subalgebra $e dot K G e$ of $K G$, with identity element $e$, is isomorphic to
the opposite ring ${End_(K G)K G e}^0$,
#source(303)
where $End_(K G)K G e$ is viewed as an algebra of left operators on $K G e$. The
algebra $e dot K G e$ is semisimple, by @prop:radical-idempotent-corner and
@th:artinian-semisimple-radical-zero, since $K G$ is semisimple.

#definition[
  Let $H <= G$, and let $psi$ be a $K$-character afforded by $K H e$ for some
  idempotent $e in K H$, as in @prop:hecke-character-multiplicity. The _Hecke
  algebra_ $frak(X)(G,H,psi)$ is the subalgebra $e dot K G e$ of $K G$. (We
  shall denote this Hecke algebra simply by $frak(X)$, when $H$ and $psi$ are
  fixed by the context.)
]<def:hecke-algebra>
#idx("Hecke algebra")

By the remarks preceding the definition, a Hecke algebra $frak(X)$ is a
semisimple algebra with identity element $e$. Moreover, if
$K H e tilde.equiv K H e'$ for another idempotent $e'$, then clearly
$K G e tilde.equiv K G e'$ by the first statement of
@prop:hecke-character-multiplicity, and $e K G e tilde.equiv e' K G e'$ by
@lem:idempotent-corner-endomorphisms. Thus the Hecke algebra $frak(X)$ is
defined independently of the left ideal $K H e$ affording $psi$. G. Seitz has
pointed out that many properties of Hecke algebras become transparent if we view
$K G$ as a split semisimple $K$-algebra, with Wedderburn components
$A_i tilde.equiv M_(n_i)(K)$. Then an idempotent $e$ as in @def:hecke-algebra
can be expressed in the form $e=sum e e_i$, where $e_i$ is the identity element
of $A_i$. Properties of $frak(X)$ such as @lem:hecke-primitive-idempotents,
@th:hecke-character-correspondence, and @cor:hecke-central-idempotents can then
be checked easily by using the results of §@sec:semisimple-rings-modules.

#example(numbered: false)[
  Let $H <= G$, and let $psi$ be the trivial character $1_H$ of $H$. Then $1_H$
  is afforded by the idempotent $e_H=|H|^(-1)sum_(h in H)h$ of $K H$. The Hecke
  algebra $frak(X)(G,H,1_H)$ equals $e_H K G e_H$, and is easily shown to be
  isomorphic to the algebra of functions $f:G -> K$, with multiplication defined
  by convolution, which are constant on the $(H,H)$-double cosets of $G$. For
  the proof, we use the interpretation of $K G$ as an algebra of functions, and
  then check that the subalgebra $e_H K G e_H$ corresponds to the functions
  constant on double cosets. As far as we know, this is the origin of the term
  Hecke algebra (see Shimura @bib:Shimura1971, p. 54). Hecke algebras of
  permutation representations, and generalizations of them called _$S$-rings_ or
  _Schur algebras_,#idx("S-rings (Schur algebras)") have been studied
  extensively by Tamaschke (@bib:Tamaschke1960, @bib:Tamaschke1964a,
  @bib:Tamaschke1964b), Wielandt @bib:Wielandt1964 and Roesler @bib:Roesler1972.
  A different approach to the decomposition of permutation and monomial
  representations, based on the study of $G$-orbits in $X times X$, where $X$ is
  the set on which $G$ acts, was given by Schur, Wielandt @bib:Wielandt1964 and
  D. G. Higman (@bib:Higman1964, @bib:Higman1967). The representation theory of
  Hecke algebras to follow was suggested partly by the analogy with the theory
  of spherical functions on symmetric spaces (see Helgason @bib:Helgason1962,
  Chapter X). This interpretation was pursued for finite groups by Travis
  @bib:Travis1974.
]

Until further notice, we shall fix a finite group $G$, a subgroup $H$ of $G$, an
idempotent $e in K H$ such that $K H e$ affords the $K$-character $psi$ of $H$,
and the Hecke algebra $frak(X)=e dot K G e$.

#lemma[
  An idempotent $u in frak(X)$ is primitive in $frak(X)$ if and only if it is
  primitive in $K G$.
]<lem:hecke-primitive-idempotents>
#source(304)
#proof[
  We recall (Exercise @exc:primitive-idempotents) that an idempotent $u$ in a
  semisimple ring $A$ is primitive if and only if it generates a simple left
  ideal, and that the condition for this to occur is that $u A u$ be a division
  ring, by @prop:semisimple-left-ideals(iii). Since $u in frak(X)$ and $e$ is
  the identity element in $frak(X)$, we have $e u=u e=u$; hence
  $ u K G u=u e K G e u=u frak(X)u, $
  and the result follows.
]

#corollary[
  The field $K$ is a splitting field for $frak(X)$.
]<cor:hecke-splitting-field>
#proof[
  We have to prove that each simple $frak(X)$-module is absolutely simple. By
  @prop:semisimple-left-ideals and @th:absolute-simplicity-centralizer, it is
  sufficient to prove that $u frak(X)u=K u$ for each primitive idempotent
  $u in frak(X)$. This is immediate by Lemma @lem:hecke-primitive-idempotents,
  since $K$ is a splitting field for $G$.
]

#theorem[
  Let $frak(X)$ be the Hecke algebra associated with $G$, $H$, $e$ and $psi$, as
  above. The following statements hold:

  #enum(
    numbering: "(i)",
    [Let $zeta in op("Irr")G$. Then the restriction $zeta|_(frak(X))!=0$ if and
      only if the multiplicity $(zeta,psi^G)!=0$.],
    [The map $zeta arrow.r zeta|_(frak(X))$ is a bijection from the set of
      irreducible characters $zeta$ of $G$ such that $(zeta,psi^G)!=0$, to the
      set of all irreducible characters of the semisimple $K$-algebra
      $frak(X)$.],
    [If $phi$ is an irreducible character of $frak(X)$ corresponding to
      $zeta in op("Irr")G$ according to part (ii), then
      $deg phi=(zeta,psi^G)$.],
  )
]<th:hecke-character-correspondence>
#proof[
  (i) Let $M$ be a simple $K G$-module affording $zeta$, and suppose
  $zeta|_(frak(X))!=0$. Then $zeta(e a e)!=0$ for some $a in K G$, and hence
  $e M!=0$. By @prop:hecke-character-multiplicity, $(zeta,psi^G)!=0$.
  Conversely, if $(zeta,psi^G)!=0$, the multiplicity formula
  @prop:hecke-character-multiplicity asserts that $zeta(e)!=0$, whence
  $zeta|_(frak(X))!=0$, and (i) is proved.

  (ii) First let $zeta in op("Irr")G$, and suppose $zeta|_(frak(X))!=0$. Let $M$
  afford $zeta$, as in (i). Then $e M!=0$ by (i) and
  @prop:hecke-character-multiplicity, and $e M$ is a left $frak(X)$-module since
  $frak(X)=e K G e$. If $m!=0$ and $m in e M$, then $frak(X)m=e K G e m=e M$,
  because $M$ is a simple $K G$-module, so we have proved that $e M$ is a simple
  $frak(X)$-module. We now compute its character. For $x in frak(X)$, we have
  $x M subset.eq e M$, whence
  $ zeta(x)=op("Tr")(x,M)=op("Tr")(x,e M). $
  Therefore $zeta|_(frak(X))$ is the character of the simple $frak(X)$-module
  $e M$.

  Next we prove that the map $zeta arrow.r zeta|_(frak(X))$ is surjective. Let
  $phi$ be the character of a simple $frak(X)$-module. Then $phi$ is afforded by
  a minimal left ideal $frak(X)u$, generated by a primitive idempotent
  $u in frak(X)$. By Lemma @lem:hecke-primitive-idempotents, $u$ is primitive in
  $K G$, and
  #source(305)
  $K G u$ is a simple $K G$-module affording some irreducible character
  $zeta in op("Irr")G$. Upon applying the argument in the preceding paragraph to
  $K G u$, we see that $zeta|_(frak(X))$ is the character of the simple
  $frak(X)$-module $e K G u=frak(X)u$, and therefore $zeta|_(frak(X))=phi$.

  Finally suppose that $zeta,zeta' in op("Irr")G$ have the same nonzero
  restrictions to $frak(X)$. By the first part of the argument,
  $zeta|_(frak(X))$ is an irreducible character $phi$ of $frak(X)$, and there
  exists $zeta_0 in op("Irr")G$ afforded by a minimal left ideal $K G u$ with
  $u in frak(X)$, such that $zeta_0|_(frak(X))=phi$. Let $M$ be a simple module
  affording $zeta$. Then
  $ zeta(u)=phi(u)!=0, $
  whence $u M!=0$, and it follows that $K G u tilde.equiv M$. Similarly
  $K G u tilde.equiv M'$, where $M'$ affords $zeta'$, and we conclude that
  $zeta'=zeta$.

  (iii) Let $phi=zeta|_(frak(X))$, for $zeta in op("Irr")G$. By part (i), $phi$
  is afforded by $e M$, where $M$ is a simple $K G$-module affording $zeta$.
  Then $deg phi=phi(e)=zeta(e)=dim_K e M=(zeta,psi^G)$, by Proposition
  @prop:hecke-character-multiplicity, and the proof is complete.
]

Let $op("Irr")G={zeta^1,dots,zeta^s}$, and for $1 <= i <= s$, let $epsilon_i$ be
the central primitive idempotent in $K G$ corresponding to $zeta^i$, given by
$ epsilon_i=zeta^i lr((1))|G|^(-1)sum_(x in G)zeta^i lr((x^(-1)))x, $
according to @prop:group-character-orthogonality-idempotents.

#corollary[
  Let $I={i:1 <= i <= s, "and" (zeta^i,psi^G)!=0}$. Then
  ${e epsilon_i}_(i in I)$ are the central primitive idempotents of $frak(X)$.
]<cor:hecke-central-idempotents>
#proof[
  The central primitive idempotents in a semisimple algebra are characterized as
  elements which act as the identity on one simple module $V$, and annihilate
  all other simple modules not isomorphic to $V$. By Theorem
  @th:hecke-character-correspondence, the simple $frak(X)$-modules are all of
  the form $e M$, where $M$ is a simple $K G$-module affording a character
  $zeta^i in op("Irr")G$ for which $(zeta^i,psi^G)!=0$. It is then clear from
  what has been said that $e epsilon_i$ acts as the identity on $e M$ and
  annihilates all simple $frak(X)$-modules not isomorphic to $e M$, proving the
  corollary.
]

#corollary(title: [Janusz @bib:Janusz1966])[
  Let $zeta^i in op("Irr")G$ be a character for which $(zeta^i,psi^G)=1$. Then
  $e epsilon_i$ is a primitive idempotent in $K G$ such that the simple module
  $K G e epsilon_i$ affords $zeta^i$.
]<cor:induced-primitive-idempotent>
#idx("Janusz's Theorem")
#proof[
  By Corollary @cor:hecke-central-idempotents and Theorem
  @th:hecke-character-correspondence(iii), $e epsilon_i$ is a central primitive
  idempotent in $frak(X)$, which corresponds to a character of $frak(X)$ of
  degree one. Hence $e epsilon_i$ is a primitive idempotent in $frak(X)$, so by
  @lem:hecke-primitive-idempotents, $e epsilon_i$ is also primitive in $K G$.
  The fact that $K G e epsilon_i$ affords $zeta^i$ follows from
  @th:hecke-character-correspondence. For another proof see Exercise
  @exc:induced-primitive-idempotent.
]

#source(306)
#theorem(title: [Ree])[
  Keep the notation of @th:hecke-character-correspondence. Let
  $zeta in op("Irr")G$, and assume that $(psi^G,zeta)!=0$. Let $t in G$, and let
  $frak(C)$ be the conjugacy class containing $t$, and $C$ the class sum
  $sum_(x in frak(C))x$. Then
  $
    zeta(t)=|C_G lr((t))|zeta(e C e)
    lr({sum_(x in G)zeta(e x^(-1)e)zeta(e x e)})^(-1).
  $
]<th:ree-character-formula>
#idx("Ree's Theorem")
#proof[
  Let $upright(bold(M))$ be a matrix representation of $G$ affording $zeta$.
  Then $e C e=C e$ because $C$ is contained in the center of $K G$, and
  $
    upright(bold(M))(C)=omega upright(bold(I)), quad "where"
    omega=|frak(C)|zeta(t)zeta(1)^(-1),
  $
  as one sees by taking traces of both sides. Then
  $
    upright(bold(M))(e C e)=upright(bold(M))(C)upright(bold(M))(e)
    =omega upright(bold(M))(e).
  $
  Taking traces again, we have
  $ zeta(e C e)=omega zeta(e)=|frak(C)|zeta(t)zeta(e)zeta(1)^(-1). $
  Now let
  $ epsilon=zeta(1)|G|^(-1)sum_(x in G)zeta(x^(-1))x $
  be the central primitive idempotent in $K G$ corresponding to $zeta$. Then
  $ epsilon e=zeta(1)|G|^(-1)sum_(x in G)zeta(x^(-1))e x e. $
  Let $e=sum_(h in H)alpha_h h$. Because $e^2=e$, we have
  $
    epsilon e=zeta(1)|G|^(-1)sum_(x in G)sum_(h,k in H)
    zeta(x^(-1))alpha_h alpha_k e h x k e.
  $
  Putting $y=h x k$, we have $x^(-1)=k y^(-1)h$, and
  $
    epsilon e=zeta(1)|G|^(-1)sum_(y in G)
    zeta(sum_(h,k in H)alpha_h alpha_k k y^(-1)h)e y e.
  $
  Therefore
  $
    epsilon e=zeta(1)|G|^(-1)sum_(x in G)zeta(e x^(-1)e)e x e.
  $ <eq:ree-central-idempotent>
  Now apply $upright(bold(M))$ and take traces; since
  $upright(bold(M))(epsilon)=upright(bold(I))$, we obtain
  $ zeta(e)=zeta(1)|G|^(-1)sum_(x in G)zeta(e x^(-1)e)zeta(e x e). $
  #source(307)
  Upon substituting this expression into the previous formula for $zeta(e C e)$,
  we obtain the desired result.
]

The preceding theorem, combined with Theorem @th:hecke-character-correspondence,
gives the values of characters of $G$ which appear with nonzero multiplicity in
$psi^G$, in terms of the values of the irreducible characters of the Hecke
algebra. Thus Ree’s formula reduces the problem of calculating character values
from $K G$ to $frak(X)$, where $frak(X)$ is usually of much smaller dimension
than $K G$. Nevertheless, Ree’s formula is still not effectively computable
without more information about the idempotent $e$. The following result provides
an illustration of what can be said when the idempotent $e$ is known explicitly.

We first recall from §@ss:mackey-theorems that for $x in G$,
$attach(psi, tl: x)$ denotes the character of the conjugate subgroup
$attach(H, tl: x)$, defined by
$ attach(psi, tl: x)(attach(h, tl: x))=psi(h), quad h in H. $
We also define the _index_#idx("index") of $x$ by
$ op("ind")x=|H:attach(H, tl: x) inter H|, quad x in G. $
Then it is easily checked that $op("ind")x$ is the number of left (or right)
cosets of $H$ contained in the double coset $H x H$. The numbers
${op("ind")x:x in G}$ coincide with the degrees of the transitive permutation
representations appearing as direct summands of $(1_H^G)_H$, and were called
_subdegrees_#idx("subdegrees") of $1_H^G$ in §@ss:mackey-theorems.

#proposition[
  Keep the notation of @th:hecke-character-correspondence, and assume further
  that $psi$ is a linear character of $H$, so
  $e=|H|^(-1)sum_(h in H)psi(h^(-1))h$ is the central idempotent in $K H$ which
  corresponds to $psi$. Let
  $
    H backslash G slash H={D_i}_(1 <= i <= r), quad "where"
    D_i=H x_i H, quad 1 <= i <= r.
  $
  Then the following statements concerning the Hecke algebra $frak(X)$ hold:

  #enum(
    numbering: "(i)",
    [Let $J={j:1 <= j <= r, attach(psi, tl: x_j)=psi "on" H inter attach(
          H, tl: x_j
        )}$, and define
      $ a_j=(op("ind")x_j)e x_j e, quad j in J. $
      Then ${a_j}_(j in J)$ is a basis for $frak(X)$. The basis elements ${a_j}$
      are determined independently of the double coset representatives if
      $psi=1_H$, and up to multiplication by a root of unity if $psi!=1_H$.],
    [For $i,j in J$, we have
      $ a_i a_j=sum_(k in J)mu_(i j k)a_k, quad mu_(i j k) in K. $
      #source(308)
      The structure constants are given by
      $
        mu_(i j k)=|H|sum_(y in D_i inter x_k D_j^(-1))a_i lr((y))a_j
        lr((y^(-1)x_k)),
      $
      where in this formula we identify the elements $a_i in K G$ with
      $K$-valued functions on $G$. We have
      $ mu_(i j k) in op("alg. int."){K} quad "for all" i,j,k. $],
    [Choose $j_0 in J$ with $x_(j_0)=1$, so $a_(j_0)=e$, and define a linear
      function $lambda$ on $frak(X)$ by setting
      $lambda(sum_(j in J)xi_j a_j)=xi_(j_0)$. Then the bilinear form $B$ on
      $frak(X)$ defined by $B(a,b)=lambda(a b)$, $a,b in frak(X)$, is
      nondegenerate, symmetric and associative
      (§@ss:frobenius-symmetric-algebras). Moreover,
      $ {a_j}_(j in J) quad "and" quad {(op("ind")x_j)^(-1)hat(a)_j}_(j in J) $
      are dual bases of $frak(X)$ with respect to the form $lambda$, where
      $ hat(a)_j=(op("ind")x_j)e x_j^(-1)e, quad j in J. $],
  )
]<prop:hecke-standard-basis>
#remark(numbered: false)[
  The basis elements ${a_j}_(j in J)$ are called _standard basis elements_ of
  $frak(X)$.#idx("standard basis elements") The basis elements
  ${hat(a)_j}_(j in J)$ form another set of standard basis elements, differing
  from the first by permutation of the indices, and in case $D_j=D_j^(-1)$, by
  multiplication by a root of unity.
]
#proof[
  (i) We have $h e=e h=psi(h)e$ for all $h in H$. First suppose
  $h in H inter attach(H, tl: x)$, for some $x in G$. Then
  $h=attach(h_1, tl: x)$ for some $h_1 in H$, and
  $
    attach(psi, tl: x)(h)e x e=psi(h_1)e x e=e x e h_1=e x h_1 e
    =e attach(h_1, tl: x)x e=psi(h)e x e.
  $
  Therefore $e x e!=0$ implies $attach(psi, tl: x)=psi$ on
  $H inter attach(H, tl: x)$.

  Conversely, suppose $psi=attach(psi, tl: x)$ on $H inter attach(H, tl: x)$. We
  first calculate the coefficient of $x$ in
  $ e x e=|H|^(-2)sum_(h_1,h_2 in H)psi(h_1)^(-1)psi(h_2)^(-1)h_1 x h_2. $
  If $h_1 x h_2=x$, then $h_1 in H inter attach(H, tl: x)$ and
  $h_1=attach((h_2^(-1)), tl: x)$. Since $psi=attach(psi, tl: x)$ on
  $H inter attach(H, tl: x)$, we have $psi(h_1)=psi(h_2)^(-1)$, so the
  coefficient of $x$ in $e x e$ is $|H|^(-2)|H inter attach(H, tl: x)|$.
  Similarly, the coefficient of $h_1 x h_2$ in $e x e$ is
  $psi(h_1)^(-1)psi(h_2)^(-1)|H|^(-2)|H inter attach(H, tl: x)|$. Therefore
  $a_j!=0$ if $j in J$, and
  $
    a_j=|H|^(-1)sum_(h_1 x_j h_2 in D_j)psi(h_1)^(-1)psi(h_2)^(-1)h_1 x_j h_2,
  $ <eq:hecke-basis-coefficients>
  #source(309)
  where the sum is taken over distinct elements of $D_j$. From these remarks, it
  follows that the elements ${a_j}_(j in J)$ are linearly independent, and form
  a basis for $frak(X)$. It is also clear that changing the double coset
  representatives will multiply each basis element $a_j$ by some root of unity,
  which is equal to 1 if $psi=1_H$.

  (ii) Let
  $ a_i a_j=sum_(k in J)mu_(i j k)a_k, quad i,j,k in J, mu_(i j k) in K. $
  In order to compute the structure constants $mu_(i j k)$, we view the elements
  ${a_i}$ as complex-valued functions on $G$, multiplied by convolution.
  Evaluating both sides at $x_k$ and using the results of part (i), we obtain
  $ (a_i a_j)(x_k)=mu_(i j k)|H|^(-1), $
  where
  $
    (a_i a_j)(x_k)=sum_(y in G)a_i lr((y))a_j lr((y^(-1)x_k))
    =sum_(y in D_i inter x_k D_j^(-1))a_i lr((y))a_j lr((y^(-1)x_k)).
  $
  Comparing these expressions, we obtain the required formula for the
  ${mu_(i j k)}$. It is now easily checked, using part (i), that for all
  $h in H$ we have
  $
    a_i lr((y))a_j lr((y^(-1)x_k))
    =a_i lr((y h))a_j lr(((y h)^(-1)x_k)), quad y in G.
  $
  Finally, it follows by @eq:hecke-basis-coefficients that
  $ mu_(i j k)=|H^2||H|^(-2)alpha $
  for some $alpha in op("alg. int."){K}$, and part (ii) is proved.

  (iii) Upon using $x_j^(-1)$ instead of $x_j$ in @eq:hecke-basis-coefficients,
  we obtain
  $
    hat(a)_j=|H|^(-1)sum_(h_1 x_j^(-1)h_2 in
    D_j^(-1))psi(h_1)^(-1)psi(h_2)^(-1)h_1 x_j^(-1)h_2.
  $
  Hence, by the same calculation used in part (ii) we have
  $
    lambda(a_i hat(a)_j)=|H|sum_(y in D_i inter D_j)a_i lr((y))hat(a)_j
    lr((y^(-1)))
  $
  $
    =cases(
      0 & "if" D_i!=D_j,
      |H||H|^(-2)|H x_j H|=op("ind")x_j & "if" D_i=D_j
    ).
  $
  This completes the proof of the proposition.
]

#source(310)
#theorem[
  Let $psi$ be a linear character of the subgroup $H$ of $G$ and let $frak(X)$
  be the Hecke algebra $frak(X)(G,H,psi)$.

  #enum(
    numbering: "(i)",
    [The central primitive idempotents ${e epsilon_i:(zeta^i,psi^G)!=0}$ of
      $frak(X)$ (see @cor:hecke-central-idempotents) are given by
      $
        e epsilon_i=zeta^i lr((1))|G:H|^(-1)
        sum_(j in J) lr((op("ind")x_j))^(-1)zeta^i lr((hat(a)_j))a_j,
      $
      where ${a_j}_(j in J)$ and ${(op("ind")x_j)^(-1)hat(a)_j}_(j in J)$ are
      the dual bases of $frak(X)$ defined in @prop:hecke-standard-basis(iii).],
    [(Orthogonality relations). Let $phi,phi'$ be irreducible characters of
      $frak(X)$. Then
      $
        sum_(j in J) lr((op("ind")x_j))^(-1)phi(hat(a)_j)phi'(a_j)
        =cases(
          0 & phi!=phi',
          phi(e)|G:H|zeta(1)^(-1) & phi=phi' ", where" zeta|_(frak(X))=phi
        ).
      $],
    [If $zeta|_(frak(X))=phi$, where $zeta in op("Irr")G$ and $(zeta,psi^G)!=0$,
      then
      $
        zeta(1)=|G:H|(zeta,psi^G)
        lr({sum_(j in J) lr((op("ind")x_j))^(-1)phi(hat(a)_j)phi(a_j)})^(-1).
      $],
    [Let $zeta in op("Irr")G$, and assume that $(zeta,psi^G)!=0$. Then
      $ zeta(1) "divides" |G:H|op("L.C.M.")_(j in J)(op("ind")x_j). $],
  )
]<th:hecke-character-formulas>
#idx("orthogonality relations")
#proof[
  (i) By @cor:hecke-central-idempotents, the elements
  ${e epsilon_i:(zeta^i,psi^G)!=0}$ are the central primitive idempotents in
  $frak(X)$. By @eq:ree-central-idempotent, we have
  $ e epsilon_i=zeta^i lr((1))|G|^(-1)sum_(x in G)zeta^i lr((e x^(-1)e))e x e, $
  for each $zeta^i in op("Irr")G$ such that $(zeta^i,psi^G)!=0$. Let
  $x=h x_j k in D_j$, where $h,k in H$. Then $x^(-1)=k^(-1)x_j^(-1)h^(-1)$, and
  $
    zeta^i lr((e x^(-1)e))e x e
    =psi(h)psi(h^(-1))psi(k)psi(k^(-1))zeta^i lr((e x_j^(-1)e))e x_j e
    =(op("ind")x_j)^(-2)zeta^i lr((hat(a)_j))a_j,
  $
  by definition of ${a_j}$ and ${hat(a)_j}$ (see @prop:hecke-standard-basis). It
  follows from this formula that
  $
    e epsilon_i&=zeta^i lr((1))|G|^(-1)
    sum_(j in J)sum_(x in D_j) lr((op("ind")x_j))^(-2)zeta^i lr((hat(a)_j))a_j\
    &=zeta^i lr((1))|G|^(-1)sum_(j in J)|H x_j H|(op("ind")x_j)^(-2)zeta^i
    lr((hat(a)_j))a_j\
    &=zeta^i lr((1))|G:H|^(-1)sum_(j in J) lr((op("ind")x_j))^(-1)zeta^i
    lr((hat(a)_j))a_j,
  $
  as required, since $|H x_j H|=|D_j|=(op("ind")x_j)|H|$.

  #source(311)
  (ii) Let us set $phi_i=zeta^i|_(frak(X))$ where $zeta^i$ ranges over all
  characters in $op("Irr")G$ such that $(zeta^i,psi^G)!=0$. By
  @th:hecke-character-correspondence(ii), these $phi_i$ are the irreducible
  characters of $frak(X)$. Since $e epsilon_i$ is the central primitive
  idempotent in $frak(X)$ corresponding to $phi_i$, we have
  $
    phi_(i') lr((e epsilon_i))=cases(
      0 & i'!=i,
      phi_i lr((e epsilon_i)) & i'=i
    ),
  $
  where $phi_i lr((e epsilon_i))=phi_i lr((e))$. Upon substituting the formula
  for $e epsilon_i$ from part (i) into this expression, we obtain the
  orthogonality formulas (ii).

  (iii) From part (ii) we have
  $
    zeta^i lr((1))=phi_i lr((e))|G:H|
    lr(
      {sum_(j in J) lr((op("ind")x_j))^(-1)phi_i lr((hat(a)_j))phi_i
        lr((a_j))}
    )^(-1).
  $
  Since $phi_i lr((e))=zeta^i lr((e))=(zeta^i,psi^G)$ by
  @prop:hecke-character-multiplicity, we obtain (iii).

  (iv) We may assume $K$ is an algebraic number field which is, as usual, a
  splitting field for $G$ and all of its subgroups. By
  @cor:hecke-splitting-field, $K$ is a splitting field for $frak(X)$.

  Let $v$ range over the discrete valuations of $K$, and let $R_v$ be the
  valuation ring associated with $v$. From §@sec:dedekind-domains,
  $op("alg. int."){K}=inter.big_v R_v$.

  Now let $R$ be one of the $R_v$ and set
  $ Lambda=sum_(j in J)R a_j, $
  where ${a_j}$ is the basis of $frak(X)$ defined in @prop:hecke-standard-basis.
  Then $R$ is a P.I.D. with quotient field $K$, and $Lambda$ is an
  $R$-order#footnote[See Definition @def:order.] in $frak(X)$ because the
  structure constants ${mu_(i j k)}$ lie in $op("alg. int."){K} subset.eq R$, by
  @prop:hecke-standard-basis(ii). Moreover, $hat(a)_j in Lambda$ for all
  $j in J$, since $hat(a)_j$ either coincides with one of the ${a_j}$ or differs
  from one by multiplication by a root of unity. Let $phi=zeta|_(frak(X))$ for
  some $zeta in op("Irr")G$ with $(zeta,psi^G)!=0$, and let $V$ be a simple
  $frak(X)$-module affording $phi$. Choose a $K$-basis ${v_1,dots,v_d}$ of $V$,
  and set
  $ M=sum_(i=1)^d Lambda v_i. $
  Since $Lambda$ is finite over $R$ and contains $e$, $M$ is a finitely
  generated torsionfree $R$-module spanning $V$, and $Lambda M subset.eq M$.
  Since $R$ is a P.I.D., $M$ is free, and hence is a full $R$-lattice in $V$
  (see §@sec:lattices-orders).#ed-note[
    The printed proof asserts that $V$ is $R$-free merely because $R$ is a
    P.I.D. A nonzero $K$-space need not be free over a proper discrete valuation
    ring $R$. The finite $Lambda$-stable lattice constructed here supplies the
    required finite free $R$-module without that assertion.
  ] Let ${m_1,dots,m_d}$ be an $R$-basis of $M$, hence a $K$-basis of $V$, and
  let $T:frak(X) -> M_d lr((K))$ be the matrix representation of $frak(X)$
  afforded by $V$ with respect to this basis. Then
  $ T(a) in M_d lr((R)), quad forall a in Lambda. $
  Let $m=op("L.C.M.")_(j in J){op("ind")x_j}$, and set
  $ w=m sum_(j in J) lr((op("ind")x_j))^(-1)phi(hat(a)_j)a_j. $
  Then $w in Lambda$ since $hat(a)_j in Lambda$, and
  $phi(hat(a)_j)=op("Tr")(hat(a)_j,M) in R$. From part (i), $w$ belongs
  #source(312)
  to the center of $frak(X)$, so
  $ T(w)=alpha dot upright(bold(I)) $
  for some $alpha in R$, since $K$ is a splitting field for $frak(X)$, and
  $w in Lambda$. Taking the traces of both sides, we have
  $ phi(w)=alpha phi(e). $
  By part (i) again,
  $ w=m|G:H|zeta(1)^(-1)e epsilon, $
  where $epsilon$ is the central primitive idempotent of $K G$ associated with
  $zeta$. Then
  $ phi(w)=m|G:H|zeta(1)^(-1)phi(e). $
  Comparing these expressions we have
  $ m|G:H|zeta(1)^(-1) in R. $
  Since this formula holds for every valuation ring $R=R_v$, and the displayed
  scalar is rational, we obtain
  $
    m|G:H|zeta(1)^(-1) in QQ inter inter.big_v R_v
    =QQ inter op("alg. int."){K}=ZZ,
  $
  as required. This completes the proof.
]

Part (iv) of the preceding theorem was proved independently by a different
method by Keller @bib:Keller1968. It includes as a special case the basic result
that $zeta^i lr((1))$ divides $|G|$ for all $zeta^i in op("Irr")G$ (see
@prop:character-degree-divides-group-order). It also yields other interesting
divisibility formulas, such as the following:

#corollary(title: [Ito @bib:Ito1951])[
  Let $A$ be an abelian normal subgroup of $G$, and let $zeta in op("Irr")G$.
  Then $deg zeta$ divides $|G:A|$.
]<cor:ito-character-degree>
#idx("Ito's Theorem")
#proof[
  Since $A$ is abelian, the irreducible characters of $A$ are all linear. By
  Frobenius Reciprocity, $(zeta,psi^G)!=0$ for some linear character $psi$ of
  $A$, and the result follows from part (iv) of @th:hecke-character-formulas.
]

Some aspects of the preceding discussion become significantly simpler in the
important case of transitive permutation representations $1_H^G$.

#proposition[
  Let $H <= G$, let $psi=1_H$, and let $frak(X)$ be the Hecke algebra
  $frak(X)(G,H,1_H)$. Then the standard basis elements of $frak(X)$ are given by
  $ a_j=|H|^(-1)sum_(x in D_j)x, quad j in J, $
  #source(313)
  where, in this case, ${D_j}_(j in J)$ is the full set of $(H,H)$-double
  cosets. The structure constants ${mu_(i j k)}$ associated with the basis
  ${a_j}$ are given by
  $ mu_(i j k)=|H|^(-1)|D_i inter x_k D_j^(-1)|, quad x_k in D_k, i,j,k in J. $
  Finally, let $zeta in op("Irr")G$ appear with nonzero multiplicity in the
  permutation character $1_H^G$, and let $phi=zeta|_(frak(X))$ be the
  corresponding character of the Hecke algebra. Then the character formula
  @th:ree-character-formula becomes
  $
    zeta(t) & =|C_G lr((t))||H|^(-1)
              lr(
                {sum_(j in J)
                  lr((op("ind")x_j))^(-1)phi(a_j)|frak(C) inter D_j|}
              ) \
            & quad times lr(
                {sum_(j in J)
                  lr((op("ind")x_j))^(-1)phi(hat(a)_j)phi(a_j)}
              )^(-1),
  $
  where $t$ belongs to the conjugacy class $frak(C)$ of $G$.
]<prop:permutation-hecke-formulas>
#proof[
  The first two statements are immediate consequences of parts (i) and (ii) of
  @prop:hecke-standard-basis. For the character formula, Ree’s Theorem
  @th:ree-character-formula gives
  $
    zeta(t)=|C_G lr((t))|zeta(e C e)
    lr({sum_(x in G)zeta(e x^(-1)e)zeta(e x e)})^(-1).
  $
  Since $e x e=(op("ind")x_j)^(-1)a_j$ for all $x in D_j$, we have
  $
    zeta(e C e)=sum_(j in J) lr((op("ind")x_j))^(-1)phi(a_j)|frak(C) inter D_j|,
  $
  and
  $
    sum_(x in G)zeta(e x^(-1)e)zeta(e x e)
    &=sum_(j in J)|D_j|(op("ind")x_j)^(-2)phi(hat(a)_j)phi(a_j)\
    &=|H|sum_(j in J) lr((op("ind")x_j))^(-1)phi(hat(a)_j)phi(a_j).
  $
  From these results we obtain the desired formula for $zeta(t)$, completing the
  proof.
]

=== Projective Representations and Central Extensions <ss:central-extensions>

We have seen in Theorem @th:clifford-projective-factorization of
§@ss:clifford-systems that Clifford’s analysis of the structure of a simple
$K G$-module in terms of a stable simple $K H$-module, for a normal subgroup $H$
of $G$, leads in a natural way to the consideration of projective
representations of finite groups. In this subsection, we shall give an
#source(314)
account of Schur’s theory of projective representations and central extensions
of finite groups. Our discussion will follow @bib:CurtisReiner1962[CR §~53],
with some additions and improvements from Yamazaki @bib:Yamazaki1964, Foote
@bib:Foote1967, and Isaacs (@bib:Isaacs1976, Chapter 11). Until further notice,
$G$ denotes a finite group and $K$ an arbitrary field.

Let $T:G -> GL(M)$ be a projective representation of $G$ with factor set
$alpha:G times G -> K^bullet$, as in Definition @def:projective-representation.
The map $T$ satisfies the condition
$ T(x)T(y)=alpha(x, y)T(x y), quad forall x,y in G, $
and is not in general a homomorphism. Nevertheless, $T$ does define a
homomorphism $tau:G -> op("PGL")(M)$, where $op("PGL")(M)$ is the _projective
general linear group_,#idx("projective general linear group") given by
$op("PGL")(M)=GL(M) slash (K^bullet dot 1_M)$, where the set $K^bullet dot 1_M$
of nonzero scalar multiples of $1_M$ coincides with the center of $GL(M)$. The
homomorphism $tau$ is given by $tau=omega compose T$, where
$omega:GL(M) -> op("PGL")(M)$ is the natural homomorphism. We leave it to the
reader to check that the map $tau$ is indeed a homomorphism, and that
conversely, all homomorphisms from $G$ to $op("PGL")(M)$ arise in this manner.
This connection between projective representations and homomorphisms into the
projective general linear group explains the terminology.#idx(
  "projective representation",
)

Now let $S:G -> GL(M)$ and $T:G -> GL(N)$ be projective representations of $G$,
with factor sets $alpha$ and $beta$, respectively. We call $S$ and $T$
_equivalent_ if there exists a $K$-isomorphism $X:M -> N$ and a map
$mu:G -> K^bullet$ such that
$ mu(x)X S(x)=T(x)X, quad forall x in G. $
When this occurs, the factor sets $alpha$ and $beta$ differ by the principal
factor set (see @eq:multiplicative-principal-factor-set) defined by the map
$mu$. Thus we may associate with each equivalence class of projective
representations a well defined element of the second cohomology group
$H^2(G,K^bullet)$, where $G$ acts trivially on the multiplicative group
$K^bullet$.

Our objective is to show that problems about projective representations of $G$
can be transferred, to a great extent, to problems about representations of
certain _central extensions_#idx("central extension") of $G$. We recall from
§@ss:schur-split-extensions that a central extension of $G$ with kernel $A$ is
an exact sequence
$ 1 -> A -> E arrow.r^pi G -> 1, $
with $A=ker pi$, and $A$ contained in the center of $E$. We shall denote such a
central extension of $G$ by $(E,pi)$. The factor set $f:G times G -> A$
associated with the above central extension $(E,pi)$ is defined by
$ f(x,y)=u_x u_y u_(x y)^(-1), quad x,y in G, $
where $u:G -> E$ is a $pi$-section (see @eq:extension-factor-set and
§@ss:schur-split-extensions). In §@ss:cohomology-groups, we defined equivalence
of central extensions of $G$ with kernel $A$, and pointed out that
#source(315)
these equivalence classes are in bijective correspondence with the elements of
$H^2(G,A)$, with trivial action of $G$ on $A$.

A central extension $(E,pi)$ of $G$ is said to have the _projective lifting
property_#idx("projective lifting property") (relative to the field $K$) if
every homomorphism $tau:G -> op("PGL")(M)$, for a f.d. $K$-space $M$, can be
completed to a commutative diagram of homomorphisms of groups:
#projective-lifting
When this can be done, we say that the projective representation of $G$ defined
by $tau$ is _lifted_#idx("lifting (of projective representations)") to the
(ordinary) representation $lambda$ of $E$. Practically speaking, this means that
if $T:G -> GL(M)$ is any projective representation of $G$, then there exists an
(ordinary) representation $lambda:E -> GL(M)$ of $E$, such that $T$ is
equivalent, as a projective representation of $G$, to the projective
representation $lambda compose u:G -> GL(M)$, where $u:G -> E$ is a
$pi$-section.

Schur’s theory is concerned with the existence of central extensions of $G$ with
the projective lifting property. We shall discuss the problem in the following
more general context.

#definition[
  Let $G$ be a group, and $B$ a multiplicative abelian group. A central
  extension $(E,pi)$ of $G$ is said to be _$B$-universal_ if for each central
  extension $(E^*,pi^*)$ of a group $G^*$ with kernel $B$, and each homomorphism
  $theta:G -> G^*$, there exists a homomorphism $lambda:E -> E^*$ such that the
  diagram
  #universal-extension
  commutes.
]<def:universal-central-extension>
#idx("universal central extension")

Notice the connection between this concept and the projective lifting property:
if $(E,pi)$ is a $K^bullet$-universal central extension of $G$, then $(E,pi)$
has the projective lifting property. We now seek a criterion for a given central
extension to be $B$-universal, for an abelian group $B$. We omit some details in
the proofs below, which we feel the reader can easily supply.

Let us first introduce some additional concepts from the theory of cohomology of
groups. Let
$ 1 -> A -> E arrow.r^pi G -> 1 $
#source(316)
be a central extension of $G$ with kernel $A$, and let $B$ be an arbitrary
abelian multiplicative group. We let
$ op("res"):Hom(E, B) -> Hom(A, B) $
be the homomorphism defined by restriction of maps from $E$ to $A$.#idx(
  "restriction",
) Similarly, we define a homomorphism, called _inflation_:#idx("inflation")
$ op("inf"):Hom(G, B) -> Hom(E, B), $
where $op("inf")psi=psi compose pi$, for $psi in Hom(G, B)$. There is also an
inflation homomorphism
$ op("inf"):H^2(G,B) -> H^2(E,B), $
defined as follows. Let $b in H^2(G,B)$, and let $f:G times G -> B$ be a factor
set representing the cohomology class $b$. Then $op("inf")b$ is defined as the
cohomology class in $H^2(E,B)$ represented by the factor set $g:E times E -> B$,
where
$ g(u,v)=f(pi(u),pi(v)), quad u,v in E. $
Another important homomorphism in this situation is the _transgression map_
#idx("transgression")
$ t:Hom(A, B) -> H^2(G,B), $
defined as follows. Let $f:G times G -> A$ be a factor set defined by a
$pi$-section from the central extension $(E,pi)$ defined above, and let
$phi in Hom(A, B)$. The image of $phi$ under the transgression map $t$ is
defined to be the cohomology class $t phi in H^2(G,B)$ with representative
factor set
$ (x,y) arrow.r phi(f(x,y)), quad x,y in G. $
We leave it to the reader to check that all these maps are well defined
homomorphisms. They can be combined to form the _Hochschild–Serre sequence_
#idx("Hochschild-Serre-Lyndon spectral sequence")#idx("spectral sequence")
#hochschild-serre-sequence
It can be proved that this sequence is exact (Hochschild–Serre
@bib:Hochschild1953; see also the latter half of the hint in Exercise
@exc:diederichsen-extension-annihilator). We do not require this fact here, but
will merely make use of some of the mappings defined above.

// Preserve the vacant position before Proposition 11.37.
#numbering-gap()
#proposition[
  The central extension
  $ 1 -> A -> E arrow.r^pi G -> 1, quad A=ker pi, $
  #source(317)
  is $B$-universal, for an abelian group $B$, if and only if the transgression
  homomorphism
  $ t:Hom(A, B) -> H^2(G,B) $
  is surjective.
]<prop:universal-extension-transgression>
#proof[
  Assume the extension $(E,pi)$ is $B$-universal, and let $b in H^2(G,B)$. By
  the correspondence between central extensions of $G$ by $B$ and elements of
  $H^2(G,B)$ (see Rotman @bib:Rotman1979, Theorem 10.24), there exists a central
  extension
  $ 1 -> B -> E^* arrow.r^(pi^*) G -> 1 $
  such that the factor set associated with a $pi^*$-section $u^*:G -> E^*$ is a
  representative of $b$. By $B$-universality, the identity map $1:G -> G$ can be
  completed to a commutative diagram
  #universal-identity-lift
  It is then easily checked that there exists a homomorphism $phi:A -> B$ making
  the diagram
  #universal-kernel-lift
  commutative. For such a map $phi$, we have $t(phi)=b$, and so $t$ is
  surjective.

  Conversely, let $t:Hom(A, B) -> H^2(G,B)$ be surjective. Let
  $ 1 -> B -> E^* arrow.r^(pi^*) G^* -> 1, quad B=ker pi^*, $
  be a given central extension of a group $G^*$ by $B$, and let $theta:G -> G^*$
  be a homomorphism. We have to construct a homomorphism $lambda:E -> E^*$ such
  that $pi^* compose lambda=theta compose pi$. Let $u:G -> E$ be a $pi$-section,
  and $v:G^* -> E^*$ a $pi^*$-section, chosen so that $u_1=v_1=1$. Let
  $f:G times G -> A$ be the factor set associated with $u$, and
  $g:G^* times G^* -> B$ the factor set associated with $v$. As in the previous
  discussion, we may form the inflation of $g$ by the homomorphism
  $theta:G -> G^*$, obtaining a factor set $g_theta:G times G -> B$ defined by
  $ g_theta lr((x,y))=g(theta(x),theta(y)), quad x,y in G. $
  #source(318)
  Since the transgression map $t$ is surjective, we may assume that there exists
  $phi in Hom(A, B)$ for which the factor sets
  $ g_theta lr((x,y)) quad "and" quad phi(f(x,y)), quad x,y in G, $
  define the same element of $H^2(G,B)$. Therefore these factor sets differ by a
  principal factor set, and there exists a function $tau:G -> B$ such that
  $tau(1)=1$ and
  $ phi(f(x,y))=g(theta(x),theta(y))tau(x)tau(y)tau(x y)^(-1), quad x,y in G. $
  Now define $lambda:E -> E^*$ by
  $ lambda(a u_x)=phi(a)tau(x)v_(theta(x)), quad a in A, x in G. $
  It is then easily checked that $lambda$ is the required homomorphism.
]

#idx("universal central extension")
Now let $K$ be an algebraically closed field. We shall use the preceding result
to give a new proof of Schur’s Theorem (see Schur @bib:Schur1904 or
@bib:CurtisReiner1962[CR §~53]) that a finite group $G$ always has a central
extension $(E,pi)$ with kernel $H^2(G,K^bullet)$ having the projective lifting
property. This theorem will follow from the existence of a $K^bullet$-universal
central extension of $G$ with kernel $H^2(G,K^bullet)$. The connection between
projective representations and central extensions is further clarified by the
result that any central extension $(E,pi)$ of $G$ with the projective lifting
property is necessarily a $K^bullet$-universal central extension.

#lemma[
  Let $G$ be a finite group acting trivially on the multiplicative group
  $K^bullet$ of an algebraically closed field $K$. Then the second cohomology
  group $H^2(G,K^bullet)$ is finite, of order not divisible by $char K$.
  Moreover, the order $e$ of any class $c in H^2(G,K^bullet)$ is a divisor of
  $|G|$, and $c$ can be represented by a factor set
  $alpha:G times G -> K^bullet$ whose values are $e$-th roots of unity.
]<lem:schur-multiplier-finiteness>
#proof[
  Let $c in H^2(G,K^bullet)$, and let $alpha:G times G -> K^bullet$ be a
  representative factor set of $c$. The product argument in the proof of Lemma
  @lem:second-cohomology-order-exponent, which applies to any abelian
  coefficient group, shows that the order $e$ of $c$ is a divisor of $|G|$. If
  $char K=p>0$, write $e=p^a m$, where $m$ is the $p'$-part of $e$. We must
  prove that $a=0$. We have
  $ alpha(x, y)^e=mu(x)mu(y)mu(x y)^(-1), $ <eq:factor-set-order-coboundary>
  for some principal factor set defined by $mu:G -> K^bullet$. Since $K$ is
  algebraically closed of characteristic $p$, each of its elements has a unique
  $p^a$-th root, and we can write
  $
    (alpha(x, y)^m)^(p^a)
    =(mu(x)^(1 slash p^a)mu(y)^(1 slash p^a)mu(x y)^(-1 slash p^a))^(p^a).
  $
  Since $p^a$-th roots are unique in $K$, we obtain
  $
    alpha(x, y)^m=mu(x)^(1 slash p^a)mu(y)^(1 slash p^a)mu(x y)^(-1 slash p^a),
  $
  #source(319)
  which contradicts the assumption that $c$ has order $e$, unless $p^a=1$. This
  proves that $c$ has order not divisible by $char K$.

  Returning to @eq:factor-set-order-coboundary, for each $x in G$ we can find an
  element $rho(x) in K^bullet$ such that $rho(x)^e=mu(x)^(-1)$. Then the map
  $alpha':G times G -> K^bullet$ defined by
  $ alpha'(x,y)=alpha(x, y)rho(x)rho(y)rho(x y)^(-1), quad x,y in G, $
  is also a representative factor set of $c$, and by
  @eq:factor-set-order-coboundary we have $alpha'(x,y)^e=1$ for all $x,y in G$.
  Since $e$ divides $|G|$, every class has a representative valued in the finite
  group of $|G|$-th roots of unity in $K$. There are only finitely many maps
  from $G times G$ to this group, so $H^2(G,K^bullet)$ is finite. This completes
  the proof.
]
#remark(numbered: false)[
  The above proof shows incidentally that for any perfect field $K$ of
  characteristic $p>0$, $H^2(G,K^bullet)$ contains no nontrivial $p$-elements,
  since each element in such a field has a unique $p$-th root.
]

#theorem[
  Let $G$ be a finite group, and $K$ an algebraically closed field. Then the
  following statements hold:

  #enum(
    numbering: "(i)",
    [There exists a central extension $(E,pi)$ of $G$ with kernel
      $H^2(G,K^bullet)$, such that $(E,pi)$ has the projective lifting
      property.],
    [Any central extension $(E,pi)$ of $G$ with the projective lifting property
      is a $K^bullet$-universal central extension.],
  )
]<th:schur-projective-lifting>
#proof[
  (i) By Proposition @prop:universal-extension-transgression and the remark
  following @def:universal-central-extension, it is sufficient to construct a
  central extension
  $ 1 -> H^2(G,K^bullet) -> E arrow.r^pi G -> 1 $
  such that the transgression map
  $ t:Hom(H^2(G,K^bullet), K^bullet) -> H^2(G,K^bullet) $
  is surjective. We may express $H^2(G,K^bullet)$ as a direct product of cyclic
  groups:
  $ H^2(G,K^bullet)=⟨c_1⟩ times dots times ⟨c_d⟩, $
  with generators ${c_i}$ of orders ${e_i}$ not divisible by the characteristic
  of $K$, by Lemma @lem:schur-multiplier-finiteness. Since $K$ is algebraically
  closed, for each $i$ we can choose a primitive $e_i$-th root of unity $zeta_i$
  in $K$ (the ${zeta_i}$ need not be distinct). By
  @lem:schur-multiplier-finiteness again, for each $i$ there exists a
  representative factor set $alpha_i$ of $c_i$ such that
  $ alpha_i lr((x,y))=zeta_i^(a_i lr((x,y))), quad x,y in G, 1 <= i <= d, $
  where the exponents $a_i lr((x,y))$ are uniquely determined integers such that
  $0 <= a_i lr((x,y))<e_i$, $x,y in G$, $1 <= i <= d$. For each pair $x,y in G$,
  let
  $ a(x,y)=c_1^(a_1 lr((x,y))) dots c_d^(a_d lr((x,y))). $
  #source(320)
  The condition @eq:multiplicative-factor-set gives
  $
    alpha_i lr((y,z))alpha_i lr((x,y z))=alpha_i lr((x y,z))alpha_i lr((x,y)),
    quad 1 <= i <= d,
  $
  which implies that for each $i$,
  $
    a_i lr((y,z))+a_i lr((x,y z)) equiv a_i lr((x y,z))+a_i lr((x,y))
    quad (mod e_i)
  $
  for all $x,y,z in G$. Since $c_i$ has order $e_i$, for $1 <= i <= d$, it
  follows that $a(x,y)$ satisfies the condition @eq:multiplicative-factor-set,
  and defines a factor set $a:G times G -> H^2(G,K^bullet)$. From
  §@ss:cohomology-groups (see also Exercise @exc:factor-set-central-extension),
  there exists a central extension
  $ 1 -> H^2(G,K^bullet) -> E arrow.r^pi G -> 1 $
  such that $a$ is the factor set associated with some $pi$-section.

  It remains to prove that the transgression map
  $t:Hom(H^2(G,K^bullet), K^bullet) -> H^2(G,K^bullet)$ is surjective. Let $b$
  be an arbitrary element of $H^2(G,K^bullet)$. Then
  $b=product_(i=1)^d c_i^(b_i)$, $b_i in ZZ$, and it follows that
  $ beta(x, y)=product_(i=1)^d zeta_i^(b_i a_i lr((x,y))), quad x,y in G, $
  is a representative factor set of $b$. Then there is a well defined
  homomorphism $phi:H^2(G,K^bullet) -> K^bullet$ such that
  $ phi(c_i)=zeta_i^(b_i), quad 1 <= i <= d, $
  and for this homomorphism we have
  $ phi(a(x,y))=beta(x, y), quad x,y in G. $
  Then $t(phi)=b$, and we have proved that $t$ is surjective, completing the
  proof of (i).

  (ii) Let $(E,pi)$ be a central extension
  $ 1 -> A -> E arrow.r^pi G -> 1 $
  with the projective lifting property, and let $f:G times G -> A$ be a factor
  set associated with a $pi$-section $u:G -> E$. In order to prove that $(E,pi)$
  is a $K^bullet$-universal central extension, it is sufficient by
  @prop:universal-extension-transgression to prove that the transgression map
  $t:Hom(A, K^bullet) -> H^2(G,K^bullet)$ is surjective. Let
  $a in H^2(G,K^bullet)$, and let $alpha:G times G -> K^bullet$ be a
  representative factor set of $a$. By Exercise
  @exc:factor-set-projective-representation there exists a projective
  $K$-representation $T:G -> GL(M)$ with factor set $alpha$. Letting
  $tau:G -> op("PGL")(M)$ be the corresponding homomorphism as
  #source(321)
  above, by the projective lifting property there exists a homomorphism
  $lambda:E -> GL(M)$ such that the diagram
  #projective-lifting-full
  is commutative. Then the restriction $phi=lambda|_A$ satisfies the condition
  $phi(A) <= ker omega=K^bullet 1_M$, so we may view $phi$ as an element of
  $Hom(A, K^bullet)$. Moreover, from the formula
  $ u_x u_y=f(x,y)u_(x y), quad x,y in G, $
  we obtain
  $ lambda(u_x)lambda(u_y)=phi(f(x,y))lambda(u_(x y)). $
  The projective lifting property implies that the projective representation
  $x arrow.r lambda(u_x)$ of $G$ is equivalent to $T$; hence the factor set
  $phi compose f$ is equivalent to the given factor set $alpha$, and we have
  $t(phi)=a$. Thus $t$ is surjective, and the proof is completed.
]

For the remainder of this subsection, $K$ always denotes an algebraically closed
field of characteristic zero. In this situation, we shall obtain a
group-theoretical characterization of minimal central extensions with the
projective lifting property. This characterization can be used to discuss the
uniqueness of such groups, and to investigate the structure of $H^2(G,K^bullet)$
(see Huppert @bib:Huppert1967, Kap. V, §23–25).

#definition[
  A _representation group_ of a finite group $G$ is a central extension $(E,pi)$
  of minimal order with the projective lifting property. The _Schur multiplier_
  of $G$ is the cohomology group $H^2(G,K^bullet)$.
]<def:representation-group-schur-multiplier>
#idx("representation group")#idx("Schur multiplier")

By Lemma @lem:schur-multiplier-finiteness, it follows easily that since $K$ is
algebraically closed, of characteristic zero, we have
$H^2(G,K^bullet) tilde.equiv H^2(G,CC^bullet)$, where $CC$ is the complex field.

#lemma[
  Let $(E,pi)$ be a central extension of $G$ of finite order, with kernel $A$,
  and let $t:Hom(A, K^bullet) -> H^2(G,K^bullet)$ be the transgression map. Then
  $ ker t=(A inter E')^perp $
  where $E'$ is the commutator subgroup of $E$, and
  $ (A inter E')^perp={phi in Hom(A, K^bullet):A inter E' <= ker phi}. $
]<lem:transgression-kernel-commutator>
#source(322)
#proof[
  Each $phi in (A inter E')^perp$ can be extended to a linear $K$-character
  $tilde(phi)$ of $A E'$, where
  $ tilde(phi)(a u)=phi(a), quad forall a in A, u in E'. $
  Then $E' <= ker tilde(phi)$, and since every linear character of the finite
  abelian group $A E' slash E'$ can be extended to a character of $E slash E'$
  (by Exercise @exc:abelian-character-extension), there exists a linear
  $K$-character $psi$ of $E$ extending $tilde(phi)$. Let $a:G times G -> A$ be a
  factor set associated with a $pi$-section $u:G -> E$ of the extension
  $(E,pi)$. Applying $psi$ to the formula
  $ u_x u_y=a(x,y)u_(x y), quad forall x,y in G, $
  we obtain
  $ psi(u_x)psi(u_y)=phi(a(x,y))psi(u_(x y)). $
  Thus $phi compose a$ is a principal factor set defined by the mapping
  $x arrow.r psi(u_x) in K^bullet$, and we have shown that $phi in ker t$.

  Conversely, let $phi in ker t$; then $phi compose a$ is a principal factor
  set, and we have
  $ phi(a(x,y))=mu(x)mu(y)mu(x y)^(-1), quad forall x,y in G, $
  for some map $mu:G -> K^bullet$. Define a map $tilde(phi):E -> K^bullet$ by
  setting $tilde(phi)(a u_x)=phi(a)mu(x)$, $a in A$, $x in G$. Then it is easily
  checked that $tilde(phi)$ is a linear $K$-character of $E$. Hence
  $E' <= ker tilde(phi)$, and $E' inter A <= ker phi$, as required.
]

#theorem[
  Let $G$ be a finite group. Then representation groups of $G$ exist, and are
  characterized as follows: a central extension $(E,pi)$ of $G$ with kernel $A$
  is a representation group if and only if $A <= E'$ and
  $|A|=|H^2(G,K^bullet)|$. If these conditions are satisfied then, in addition,
  $A tilde.equiv H^2(G,K^bullet)$.
]<th:representation-group-characterization>
#proof[
  Representation groups certainly exist, by Theorem
  @th:schur-projective-lifting(i). Let $(E,pi)$ be any one of them, and let $A$
  be the kernel. By @th:schur-projective-lifting(ii), the transgression map
  $t:Hom(A, K^bullet) -> H^2(G,K^bullet)$ is surjective. Since
  $|Hom(A, K^bullet)|=|A|$ for every finite abelian group $A$ and every
  algebraically closed field $K$ of characteristic zero, we have
  $ |A|=|Hom(A, K^bullet)| >= |H^2(G,K^bullet)|. $
  Since there exists a representation group with kernel $H^2(G,K^bullet)$ by
  @th:schur-projective-lifting, and since $(E,pi)$ has minimal order, it follows
  that
  $ |A|=|H^2(G,K^bullet)| $
  for any representation group $(E,pi)$. From this equality, since $|A|=$
  #source(323)
  $|Hom(A, K^bullet)|$ and $t$ is surjective, it follows that $ker t=1$.
  Therefore $A inter E'=A$, and $A <= E'$. Finally, we have shown that $t$ is an
  isomorphism; hence
  $A tilde.equiv Hom(A, K^bullet) tilde.equiv H^2(G,K^bullet)$, using Exercise
  @exc:finite-abelian-character-duality.

  Conversely, let $(E,pi)$ be a central extension with kernel $A$ such that the
  conditions $|A|=|H^2(G,K^bullet)|$ and $A <= E'$ are satisfied. We have to
  prove that $(E,pi)$ is a representation group, and for this it suffices to
  show that the transgression map
  $ t:Hom(A, K^bullet) -> H^2(G,K^bullet) $
  is surjective. Since $A <= E'$, we can apply Lemma
  @lem:transgression-kernel-commutator to obtain
  $ ker t=(A inter E')^perp=A^perp=1. $
  Since $t$ is injective, and $|Hom(A, K^bullet)|=|A|=|H^2(G,K^bullet)|$ by
  assumption, it follows that $t$ is surjective, as required. This completes the
  proof.
]

#example(numbered: false)[
  Let $K$ be the complex field, and $G$ a metacyclic group given by
  $ G=⟨a,b:a^m=1,b^s=a^t,b a b^(-1)=a^r⟩. $
  Since $b^s$ commutes with $a$, and $b$ commutes with $a^t$, the positive
  integers $m$, $r$, $s$ and $t$ must satisfy the conditions that
  $ r^s equiv 1 quad (mod m), quad m divides t(r-1). $
  We shall show how to compute $H^2(G,K^bullet)$ by brute force.

  Each factor set $f:G times G -> K^bullet$ gives rise to a twisted group
  algebra
  $ (K G)_f=plus.o.big_(x in G)K u_x, $
  where the ${u_x}$ are units which commute with the elements of $K$, and where
  multiplication is given by
  $ u_x u_y=f(x,y)u_(x y) quad "for all" x,y in G. $
  Replacing each $u_x$ by $alpha_x u_x$, with $alpha_x in K^bullet$, replaces
  $f$ by an equivalent factor set.

  For convenience of notation, put $u_a=A$, $u_b=B$. We may then suppose (after
  suitable basis changes) that
  $
    A^m=1, quad B^s=A^t, quad u_(a^i b^j)=A^i B^j
    quad "for" 0 <= i <= m, 0 <= j <= s,
  $
  and that
  $ B A=xi A^r B $
  #source(324)
  for some $xi in K^bullet$. We find readily that for each $i in ZZ$ and
  $j >= 0$, with the empty sum interpreted as zero,
  $ B^j A^i=xi^(i(1+r+dots+r^(j-1)))A^(i r^j)B^j. $
  Since $A^m=1$, we also have $xi^m=1$. Taking $i=t$, $j=1$, and then $i=1$,
  $j=s$, we find that $xi$ must be a $k$-th root of 1, where
  $k=op("G.C.D.")(m,t,1+r+dots+r^(s-1))$. Further, each such choice for $xi$
  yields a possible factor set.

  On the other hand, we may replace $A$ by $omega A$, and $B$ by $zeta B$, where
  $omega$ and $zeta$ are roots of unity such that
  $ omega^m=1 quad "and" quad zeta^s=omega^t. $
  This has the effect of replacing $xi$ by $xi omega^(1-r)$. The above
  conditions easily imply that $omega^((r-1)k)=1$, so $omega^(r-1)$ is a $k$-th
  root of 1, and $m divides (r-1)k$. It follows that $l divides k$, where
  $l=m slash (r-1,m)$, and that $omega^(r-1)$ ranges over all $l$-th roots of 1.
  Therefore
  $
    H^2(G,K^bullet) tilde.equiv (ZZ slash k ZZ) slash (q ZZ slash k ZZ)
    tilde.equiv ZZ slash q ZZ,
  $
  where $q=k slash l=k(r-1,m) slash m$.

  The following presentation is proposed in the original as a representation
  group of $G$:
  $ G^*=⟨a,b,c:a^m=1,b^s=a^t,c^q=1,b a b^(-1)=c a^r,c a=a c,c b=b c⟩, $
  and $G=G^* slash ⟨c⟩$.#ed-note[
    This presentation is not always a representation group. For $m=4$, $r=3$,
    $s=2$, $t=4$, the quotient $G$ is the dihedral group $D_8$ of order $8$, and
    $k=4$, $l=2$, $q=2$. The displayed $G^*$ is
    $(ZZ slash 4ZZ times ZZ slash 2ZZ) ⋊ ZZ slash 2ZZ$, of order $16$, with
    $a,c$ independent and conjugation by $b$ given by $a arrow.r c a^(-1)$,
    $c arrow.r c$. Its kernel over $D_8$ is $⟨c⟩$, whereas $(G^*)'=⟨c a^2⟩$ does
    not contain $c$. Thus it fails the criterion in Theorem
    @th:representation-group-characterization. The multiplier calculation
    $H^2(D_8,CC^bullet) tilde.equiv ZZ slash 2ZZ$ is unaffected: the quotient of
    fourth roots of unity by second roots cannot be represented by simply
    choosing a root of order $2$. A valid representation group in this
    particular case is $D_(16)=⟨u,v:u^8=v^2=1,v u v^(-1)=u^(-1)⟩$, mapping $u$
    to $a$ and $v$ to $b$. Its kernel $⟨u^4⟩$ lies in $D'_(16)=⟨u^2⟩$ and has
    order $2$, so the same theorem applies. This is a particular cover, not a
    replacement for the proposed general presentation.
  ]

  For other calculations of this type, and other approaches to such
  computations, see Huppert @bib:Huppert1967.
]

We conclude with some applications of the preceding results. A projective
representation $T:G -> GL(M)$ is called _irreducible_ if $M$ has no proper
$K$-subspaces invariant under the set of linear transformations
${T(x):x in G}$.#idx("irreducible projective representation")

#proposition[
  The degrees of the irreducible projective representations of $G$ in an
  algebraically closed field $K$ of characteristic zero are divisors of $|G|$.
]<prop:projective-character-degree>
#proof[
  By Theorem @th:representation-group-characterization, there exists a
  representation group $(E,pi)$. Each irreducible projective representation
  $T:G -> GL(M)$ can be lifted to a representation $lambda:E -> GL(M)$. It is
  clear that $lambda$ is an irreducible representation of $E$ and that
  $deg T=deg lambda$. Since $K$ is algebraically closed and of characteristic
  zero, $deg lambda$ divides $|E:A|$ by Ito’s Theorem (Corollary
  @cor:ito-character-degree). But $|E:A|=|G|$, so the result follows.
]

We now return to the important problem of extendability of irreducible invariant
$K$-characters $psi$ of a normal subgroup $H$ of a finite group $G$ (see
§@ss:clifford-character-theory).

#source(325)
#proposition[
  Let $H ⊴ G$, and let $psi$ be an irreducible invariant $K$-character of $H$,
  that is, a character which coincides with all of its $G$-conjugates. If the
  Schur multiplier of $G slash H$ is trivial, that is,
  $H^2(G slash H,K^bullet)=1$, then $psi$ can be extended to an irreducible
  $K$-character of $G$.
]<prop:invariant-character-extension>
#proof[
  Let $L$ be a simple $K H$-module affording $psi$, and $M$ a simple
  $K G$-module with $L subset.eq M_H$. By Clifford’s Theorem
  @th:clifford-projective-factorization,
  $ M tilde.equiv L times.o_K I, $
  where $L$ and $I$ afford projective representations $U$ of $G$ on $L$, and $V$
  of $G slash H$ on $I$, respectively. Since $H^2(G slash H,K^bullet)=1$, we may
  assume that $V$ is an ordinary representation of $G slash H$ (see Exercise
  @exc:trivial-multiplier-projective-representations). Hence $U$ is an ordinary
  representation of $G$ on $L$ extending the action of $H$, and $psi$ can be
  extended to a character of $G$, as required.
]

#proposition[
  Let $p$ be a prime divisor of $|H^2(G,K^bullet)|$. Then each Sylow
  $p$-subgroup of $G$ is non-cyclic.
]<prop:multiplier-noncyclic-sylow>
#proof(head: emph[Proof (Isaacs @bib:Isaacs1976, p. 186).])[
  By @th:representation-group-characterization, there exists a representation
  group $(E,pi)$. Let $A=ker pi$, so $E slash A tilde.equiv G$; let $S$ be a
  subgroup of $E$ such that $S slash A$ is a Sylow $p$-subgroup of $E slash A$,
  and suppose that $S slash A$ is cyclic. Since $A$ is central in $E$, $S$ is
  abelian, and it follows that $E$ has an abelian Sylow $p$-subgroup. By
  Exercise @exc:abelian-sylow-central-commutator,
  $p divides.not |E' inter Z(E)|$, where $Z(E)$ is the center of $E$. Since
  $A <= E' inter Z(E)$ and $A tilde.equiv H^2(G,K^bullet)$ by
  @th:representation-group-characterization, we have
  $p divides.not |H^2(G,K^bullet)|$, contrary to assumption.
]

Combining the last two results, we obtain:

#corollary[
  Let $H ⊴ G$, and let $psi$ be an irreducible invariant $K$-character of $H$.
  If $G slash H$ is cyclic, then $psi$ can be extended to a $K$-character of
  $G$.
]<cor:cyclic-quotient-character-extension>
#proof[
  By Proposition @prop:multiplier-noncyclic-sylow, $H^2(G slash H,K^bullet)=1$.
  Then $psi$ can be extended to a character of $G$ by Proposition
  @prop:invariant-character-extension.
]

#exercises-heading
All representations and characters are taken in an algebraically closed field
$K$ of characteristic 0, unless otherwise specified.

#exercise[
  A finite group $G$ is called _supersolvable_ if there exists a normal series
  $ G=G_1 >= G_2 >= dots >= G_(s+1)=1, $
  with cyclic factors of prime order, where each $G_i ⊴ G$. (See
  §@ss:background-group-theory.)#idx("supersolvable group")#idx(
    "group",
    "supersolvable",
  )
  #source(326)
  #enum(
    numbering: "(i)",
    [Prove that there are inclusions
      $
        {"nilpotent groups"} subset.eq {"supersolvable groups"} subset.eq
        {"solvable groups"},
      $
      with strict inclusions at each stage.],
    [Prove that supersolvable groups are $M$-groups.],
  )

  #hint([@exc:supersolvable-monomial])[
    First prove that subgroups and homomorphic images of supersolvable groups
    are supersolvable, so that we can reduce to the case of a faithful
    irreducible representation (as in the proof of
    @th:nilpotent-group-monomial). Then show that each non-abelian supersolvable
    groups has an abelian normal subgroup not contained in the center, and apply
    @prop:blichfeldt-imprimitivity.
  ]
]<exc:supersolvable-monomial>

#exercise[
  Find an example of a solvable group which is not an $M$-group.
]<exc:solvable-nonmonomial>

#exercise[
  Let $H ⊴ G$, and let $psi in op("Irr")H$, $zeta in op("Irr")G$, and assume
  $(zeta,psi^G)>0$. In @prop:clifford-character-restriction, it was proved that
  there exists a character $mu in op("Irr")G_psi$ such that $zeta=mu^G$ and
  $mu_H=a psi$ for some $a in ZZ$. Prove that $mu$ is uniquely determined by
  these conditions.
]<exc:clifford-character-uniqueness>

#exercise[
  Let $E$ be a field of characteristic $p>0$, and let $H$ be a normal
  $p$-subgroup of a finite group $G$. Prove that $H$ acts trivially on every
  simple $E G$-module.
  #hint([@exc:normal-p-subgroup-simple-module])[
    Use @th:clifford-theorem and @th:p-group-algebra-local.
  ]
]<exc:normal-p-subgroup-simple-module>

#exercise[
  Let $G$ be the group of all rigid motions of a cube. Show that $|G|=48$, and
  that $G$ is isomorphic to the group of signed permutations.
  $
    lr(
      {mat(1, 2, 3; plus.minus i_1, plus.minus i_2, plus.minus i_3), 1 <=
        i_j <= 3}
    ).
  $
  Show that the subgroup $H$, consisting of all permutations
  $ mat(1, 2, 3; plus.minus 1, plus.minus 2, plus.minus 3), $
  is an abelian normal subgroup of $G$, and that $G=H ⋊ S$, for a subgroup
  $S tilde.equiv S_3$. Find $op("Irr")G$. In particular, find the degree of each
  $zeta in op("Irr")G$, and express $zeta$ in the form $(tilde(psi)omega)^G$,
  where $psi in op("Irr")H$, $tilde(psi)$ is the extension of $psi$ to $G_psi$,
  and $omega in op("Irr")(G_psi slash H)$.
  #hint([@exc:cube-signed-permutation-characters])[
    First show that the non-conjugate characters $psi$ of $H$ can be described
    by the notations $(+ + +)$, $(+ + -)$, $(+ - -)$ and $(- - -)$, according as
    $psi$ takes a generator of $H$ to $+1$ or $-1$. Show that for these 4
    choices of the character $psi$, $G_psi slash H$ has the structure $S_3$,
    $S_2 times S_1$, $S_1 times S_2$, and $S_3$, respectively. Then apply
    @prop:little-groups. The same method applies to the _hyper-octahedral
    group_, which is the symmetry group of an $n$-dimensional cube.#idx(
      "group",
      "hyper-octahedral",
    )
  ]
]<exc:cube-signed-permutation-characters>

#exercise[
  Let $H$ be a finite group whose characters are known, and let $G$ be a
  semidirect product $(H times H) ⋊ ⟨tau⟩$, where $tau$ has order 2 and acts on
  the direct product $H times H$ as follows:
  $ tau(h, h')tau^(-1)=(h',h), quad forall h,h' in H. $
  Show how to construct $op("Irr")G$ from a knowledge of $op("Irr")H$.
  #source(327)
  #hint([@exc:wreath-product-characters])[
    Let $phi,psi in op("Irr")H$. Prove that
    $ (phi dot psi)^G in op("Irr")G quad "if" phi!=psi, $
    and that
    $ (phi dot phi)^G=zeta+epsilon zeta, $
    where $zeta$ is an extension of $phi dot phi$ to $G$, and $epsilon$ is the
    non-trivial character of $G slash (H times H)$. Prove that every irreducible
    character of $G$ is obtained by one or the other of these constructions. The
    extension of $phi dot phi$ to $G$ is obtained as follows. Let $V$ be a
    $K H$-module affording $phi$; then $V hash V$ affords $phi dot phi$. Prove
    that the action of $tau$ on $V times.o V$ given by
    $v times.o v' arrow.r v' times.o v$, $v,v' in V$, extends the action of
    $H times H$.
  ] (We remark that the group $G$ is the _wreath product_ $H wreath ZZ_2$ (see
  Hall @bib:Hall1959, p. 81 or Huppert @bib:Huppert1967, p. 94).#idx(
    "wreath product",
  ) Representations of wreath products were discussed in general by Kerber
  @bib:Kerber1968. For extensions of the method, and applications to chemistry,
  see Alvis–Curtis–Dyke–Odutola @bib:Alvis1981.)
]<exc:wreath-product-characters>

#exercise[
  A metacyclic group $G$ has a presentation
  $ ⟨a,b:a^m=1,b a b^(-1)=a^r,b^s=a^t⟩, $
  where ${m,s,r,t}$ are integers such that (see @bib:CurtisReiner1962[CR §~47])
  $
    (m,r)=1, quad m divides t(r-1), quad m divides (r^s-1)
    .
  $
  Find $op("Irr")G$. #hint([@exc:metacyclic-characters])[
    First prove that if $H=⟨a⟩$, then $H <= G$, and each $psi in op("Irr")H$ has
    an extension $tilde(psi)$ to $G_psi$. Describe $tilde(psi)$ explicitly. Then
    apply @th:gallagher-character-extension to construct $op("Irr")G$.
  ] (We remark that this exercise provides an illustration of
  @cor:cyclic-quotient-character-extension, and includes more general cases than
  in @prop:little-groups, where $G$ is assumed to be a semidirect product.)
]<exc:metacyclic-characters>

#exercise[
  Let $A$ be an $S$-graded $R$-algebra, and let $L$, $E$, etc., be as in
  @prop:graded-endomorphism-algebra and @prop:graded-inertia-subgroup. Let
  $T <= S$,
  $ B=sum_(t in T)A_t, quad L^B=sum_t lr((a_t times.o L)) subset.eq L^A, $
  and $E_T=sum_(t in T)E_t$. Prove that $E_T tilde.equiv End_B L^B$, where the
  isomorphism is given by restriction of $f in E_T subset.eq E$ to the submodule
  $L^B$.
]<exc:graded-endomorphism-restriction>

#exercise[
  Let $T:G -> GL(M)$ be a projective representation with factor set $alpha$, and
  let $d=dim_K M$. Prove that $alpha^d tilde 1$, that is, $alpha^d$ is
  equivalent to a principal factor set.
  #hint([@exc:projective-determinant-factor-set])[
    Take the determinant of both sides in the formula for $T(x)T(y)$.
  ]
]<exc:projective-determinant-factor-set>

#exercise[
  Let $alpha:G times G -> K^bullet$ be a factor set. Prove that there exists an
  irreducible projective representation of $G$ with factor set $alpha$.
  #hint([@exc:factor-set-projective-representation])[
    Let $(K G)_alpha$ be the twisted group algebra with factor set $alpha$ (see
    @exm:crossed-products-twisted-group-algebras(ii)). Then show that each
    simple $(K G)_alpha$-module defines an irreducible projective representation
    of $G$ with factor set $alpha$.
  ]
]<exc:factor-set-projective-representation>

#source(328)
#exercise[
  Prove that if $H^2(G,K^bullet)=1$, then every irreducible projective
  representation of $G$ with factor set $alpha$ is equivalent to an ordinary
  representation.
  #hint([@exc:trivial-multiplier-projective-representations])[
    Use @th:representation-group-characterization.
  ]
]<exc:trivial-multiplier-projective-representations>

#exercise[
  Let $p$ be a prime. Prove that if $G$ has an abelian Sylow $p$-subgroup, then
  $p$ does not divide $|G' inter Z(G)|$, where $G'$ is the derived group of $G$,
  and $Z(G)$ the center of $G$.
]<exc:abelian-sylow-central-commutator>

#exercise[
  In @th:clifford-projective-factorization, prove that if the action of $H$ on
  $L$ can be extended to an action of $G$ on $L$, then both $U$ and $V$ can be
  taken to be ordinary representations.
]<exc:clifford-ordinary-factorization>

#exercise[
  Use the preceding exercise and @th:clifford-projective-factorization to prove
  that if $K$ is an algebraically closed field (of any characteristic), and
  $G=G_1 times G_2$, then every simple $K G$-module can be expressed in the form
  $L_1 hash L_2$, for simple modules $L_1$ and $L_2$ over $K G_1$ and $K G_2$,
  respectively. (See also §@ss:outer-tensor-products.)
]<exc:clifford-direct-product-simple>

#exercise[
  Let $alpha:G times G -> A$ be a factor set taking values in an abelian
  multiplicative group $A$, with $G$ acting trivially on $A$. Prove that there
  exists a central extension
  $ 1 -> A -> E arrow.r^pi G -> 1 $
  such that $alpha$ is the factor set associated with some $pi$-section.
]<exc:factor-set-central-extension>

#exercise[
  Prove that every finite abelian group $A$ is isomorphic to its character group
  $Hom(A, K^bullet)$ (where $K$ is algebraically closed and of characteristic
  0.)
]<exc:finite-abelian-character-duality>

#exercise[
  Let $B$ be a subgroup of a finite abelian group $A$. Prove that every linear
  character $lambda:B -> K^bullet$ can be extended to a character of $A$.
  #hint([@exc:abelian-character-extension])[
    Consider the irreducible constituents of $lambda^A$.
  ]
]<exc:abelian-character-extension>

#exercise[
  Let $frak(X)(G,H,psi)$ be a Hecke algebra, as in @def:hecke-algebra. Prove
  that $frak(X)(G,H,psi)$ is a commutative algebra if and only if $psi^G$ is
  multiplicity-free, in the sense that
  $ (zeta,psi^G)=0 "or" 1 quad forall zeta in op("Irr")G. $
]<exc:hecke-commutative-multiplicity-free>

#exercise[
  The linear map $op("ind"):frak(X)(G,H,1_H) -> K$, defined by
  $op("ind")(a_j)="index of" x_j$, where $x_j in D_j$, is a homomorphism of
  $K$-algebras, corresponding to the trivial character $1_G$ according to
  @th:hecke-character-correspondence.
]<exc:hecke-index-homomorphism>

The following result gives a useful method for computing degrees of irreducible
components of permutation characters $1_H^G$ (compare with
@th:hecke-character-formulas(iii)).

#exercise[
  (D. G. Higman @bib:Higman1967). Let $frak(X)=frak(X)(G,H,1_H)$ be the Hecke
  algebra of a permutation representation $1_H^G$, and assume that
  $frak(X)=K[a_1]$ for some standard basis element $a_1$ (see
  @prop:permutation-hecke-formulas). Let $e=|H|^(-1)sum_(h in H)h$, $V=K G e$,
  and view $V$ as a $(K G,frak(X))$-bimodule, with $frak(X)=e K G e$ acting on
  the right in the obvious way. Let $upright(bold(M))$ be the matrix of right
  multiplication by $a_1$ on $frak(X)$, and $upright(bold(A))$ the matrix of
  right multiplication by $a_1$ on $V$. The matrix $upright(bold(M))$ is
  determined by the structure constants ${mu_(i j k)}$, and is called the
  _intersection matrix_ of the permutation representation.#idx(
    "intersection matrix",
  ) Prove that the following statements hold:
  #source(329)
  #enum(
    numbering: "(i)",
    [The minimal polynomials of $upright(bold(M))$ and $upright(bold(A))$
      coincide, and are both equal to $op("char. pol.")upright(bold(M))$.],
    [Let $p(t)=op("char. pol.")upright(bold(M))$. Then $p(t)$ has distinct zeros
      ${theta_1,dots,theta_m}$. The simple $K G$-submodules of $V$ all appear
      with multiplicity 1, and coincide with the eigenspaces ${V_(theta_i)}$
      corresponding to the eigenvalues ${theta_i}$ of $upright(bold(A))$.],
    [For each $i$, $1 <= i <= m$, let $p_i lr((t))=p(t) slash (t-theta_i)$. Then
      $
        dim_K V_(theta_i)=frac(
          op("Trace")p_i lr((upright(bold(A)))), p_i
          lr((theta_i))
        ).
      $],
    [Let $a_1^s=sum_(i=0)^(m-1) eta_(s i)a_i$, $s=1,2,dots$, where $a_0=e$, and
      ${a_0,dots,a_(m-1)}$ are the standard basis elements of $frak(X)$. Then
      $ op("Trace")upright(bold(A))^s=|G:H|eta_(s 0), $
      so the dimensions of the simple submodules of $1_H^G$ given in (iii) are
      effectively computable from the intersection matrix $upright(bold(M))$.],
  )

  #hint([@exc:hecke-intersection-matrix-degrees])[
    (i) We have $frak(X) tilde.equiv K[t] slash (m(t))$, where
    $m(t)=op("min. pol.")upright(bold(M))$. Since $frak(X)$ is semisimple, and
    $K$ is algebraically closed, $m(t)$ has distinct roots in $K$. Therefore
    $m(t)=p(t)$, where $p(t)=op("char. pol.")upright(bold(M))$. From
    $p(upright(bold(M)))=0$ we obtain $p((a_1)_r)=0$; therefore $p(a_1)=0$,
    since the map $a arrow.r a_r$, $a in frak(X)$, is a faithful representation.
    Then $V dot p(a_1)=0$, and hence $p(upright(bold(A)))=0$, so
    $op("min. pol.")upright(bold(A))$ divides $p(t)$. On the other hand,
    $frak(X)=e K G e subset.eq V$, and $frak(X)$ is stable under right
    multiplication by $a_1$ on $V$. Hence for each polynomial $f(t) in K[t]$,
    $f(upright(bold(A)))=0$ implies that $frak(X)f(a_1)=0$, and therefore
    $p(t) divides f(t)$.

    (ii) By Exercise @exc:hecke-commutative-multiplicity-free, $1_H^G$ is
    multiplicity-free, since $frak(X)$ is commutative. The irreducible
    characters $zeta^i$ occurring in $1_H^G$ are afforded by submodules
    $ epsilon_i V=V_(epsilon_i e), $
    where $epsilon_i$ is as in @cor:hecke-central-idempotents. Now $epsilon_i e$
    is a central primitive idempotent in $frak(X)$ by
    @cor:hecke-central-idempotents, and it follows that
    $epsilon_i V=V_(theta_i)$ for some $theta_i$, $1 <= i <= m$.

    (iii) The matrix $upright(bold(A))$ is semisimple, with eigenvalues
    ${theta_i}$. Hence for each $f(t) in K[t]$, we have
    $ op("Tr")f(upright(bold(A)))=sum_i lr((dim V_(theta_i)))f(theta_i). $
    In particular, for each $j$ we obtain
    $
      op("Tr")p_j lr((upright(bold(A))))
      =sum_i lr((dim V_(theta_i)))p_j lr((theta_i))
      =(dim V_(theta_j))p_j lr((theta_j)),
    $
    which is (iii).

    (iv) It is sufficient to check that if $a_1^s=sum_0^(m-1)eta_(s i)a_i$,
    $s=1,2,dots$, then $op("Tr")((a_0)_r,V)=|G:H|$ and $op("Tr")((a_i)_r,V)=0$
    for $i!=0$. The first statement is clear since $e$ acts as the
    #source(330)
    identity on $V$, and $dim V=|G:H|$. Secondly, $V=K G e$ has a basis
    ${h x_j e}$ corresponding to the left $H$-cosets in the double cosets
    ${D_j}$. Right multiplication by $a_i$ on these elements yields
    #named-equation(name: [$(ast)$])[
      $ (h x_j e)a_i=sum alpha(i; h, x_j, h', x_(j'))h' x_(j')e, $
    ] <eq:hecke-coset-multiplication>
    with non-negative integer coefficients $alpha(i; h, x_j, h', x_(j'))$,
    describing the partitioning of $h x_j D_i$ into $H$-cosets. For $i!=0$, a
    simple calculation shows that if $op("Tr")((a_i)_r,V)!=0$, then some
    diagonal coefficient $alpha(i; h_i, x_j, h_i, x_j)!=0$, and upon
    multiplication of @eq:hecke-coset-multiplication by $(h x_j)^(-1)$, we
    obtain $D_i inter H!=emptyset$, which is impossible.
  ]
]<exc:hecke-intersection-matrix-degrees>
