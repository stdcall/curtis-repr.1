#import "main-defs.typ": *
#import "statements.typ": *

== The Artin and Brauer Induction Theorems <sec:artin-brauer-induction>
#idx("Induction Theorems", target: [@sec:artin-brauer-induction])
#source(399)

Let $H$ be a subgroup of a finite group $G$, and let $R$ be a commutative ring.
The connections between $R H$-modules and $R G$-modules defined by the induction
and restriction maps were discussed in
§§@sec:induced-modules–@sec:tensor-algebras, and in
§@sec:tensor-induction-transfer for tensor induction. It is not surprising that
significant new information is obtained when several subgroups are brought into
the picture simultaneously. This section contains powerful results in this
direction, due to Artin in case $R$ is the rational field, and to Brauer in case
$R$ is the field of complex numbers.

There is no doubt that Brauer's Theorem has played a central role in character
theory since its discovery. One of the first applications, due to Brauer
himself, was to prove a long-standing conjecture that the cyclotomic field of
$n$-th roots of unity is always a splitting field for a finite group $G$ of
order $n$. Another application was Brauer's characterization of virtual
characters, which has been used to prove a wide variety of theorems. These
applications and others, as well as a converse of Brauer's Theorem due to Green,
are all included in the latter part of this section.

=== Artin's Induction Theorem Revisited <ss:artin-induction-revisited>

Let $G$ be a finite group. A $QQ$-character $phi$ of $G$, or a _rational
character_#idx("rational character")#idx("character", "rational") of $G$, is a
character afforded by a $QQ G$-module. Permutation characters ${1_H^G}$ arising
from subgroups $H$ of $G$ are examples of rational characters. Artin's Induction
Theorem asserts that every rational character $phi$ of $G$ can be expressed in
the form
$ phi=|G|^(-1)sum a_C 1_C^G, $ <eq:artin-integral-denominator>
where the sum is taken over all cyclic subgroups $C$ of $G$, and the
coefficients $a_C$ are rational integers. For a proof and discussion of this
result, see @bib:CurtisReiner1962[CR §39].

Our objective here is to give Brauer's @bib:Brauer1951 proof and refinement of
the theorem, in which the coefficients $a_C$ are given explicitly. Brauer was
interested in these formulas in connection with calculations of class numbers in
algebraic number fields (see @bib:Brauer1951). We present them here partly
because such formulas do not seem to be known for two other induction theorems
with which we shall be concerned: the Brauer Induction Theorem
(§@ss:character-rings-brauer-induction or @bib:CurtisReiner1962[CR §40]), and
the Berman-Witt Theorem (@th:witt-berman-induction or @bib:CurtisReiner1962[CR
  §42]).

For the proof of Brauer's Theorem we require first the fact that if $phi$ is a
rational character of $G$, then
$ phi(x)=phi(y) quad "whenever" chevron.l x chevron.r=chevron.l y chevron.r. $
<eq:rational-character-cyclic-generators>
For a proof see Exercise~@exc:rational-character-conjugate-cyclic-subgroups.

#source(400)
We shall also use the Möbius $mu$-function,#idx("Möbius μ-function") defined by
$
  mu(n)=cases(
    1 & quad "if" n=1,
    0 & quad "if" a^2 divides n "for some" a>1,
    (-1)^r & quad "if" n=p_1 p_2 dots.c p_r comma p_i "distinct primes".
  )
$
Then $mu(n_1 n_2)=mu(n_1)mu(n_2)$ if $(n_1,n_2)=1$, and we have
$ sum_(d divides n) mu(d)=cases(1 & quad "if" n=1, 0 & quad "if" n>1). $
<eq:mobius-divisor-sum>
(see Niven and Zuckerman (@bib:Niven1980, §4.3) for @eq:mobius-divisor-sum and
further discussion of the Möbius function.)

We now have:

#theorem(name: "Artin Induction Theorem")[
  Each rational character $phi$ of $G$ can be expressed in the form
  $ phi=sum a_C 1_C^G, $
  where the sum is taken over all cyclic subgroups ${C}$ of $G$, and the
  coefficients are given by
  $ a_C=frac(1, |G:C|)sum_(C^*>=C) mu(|C^*:C|)phi(z^*), $
  where ${C^*}$ ranges over all cyclic subgroups containing $C$, and $z^*$ is a
  generator of $C^*$.
] <th:artin-induction-explicit-coefficients>
#idx(
  "Artin Induction Theorem",
  target: [@th:artin-induction-explicit-coefficients],
)
#idx(
  "Induction Theorems",
  "Artin",
  target: [@th:artin-induction-explicit-coefficients],
)

#proof(head: emph[Proof (Brauer).])[
  From @eq:rational-character-cyclic-generators, we know that the value
  $phi(z^*)$ is independent of the choice of the generator of $C^*$. Let
  $ phi^*=sum a_C 1_C^G, $
  where the coefficients $a_C$ are given as in the statement of the theorem. We
  have to prove that $phi^*=phi$.

  Let $x in G$; then from @eq:induced-character-average we have
  $ 1_C^G lr((x))=frac(1, |C|)sum_(y in G) dot(1)_C lr((y x y^(-1))), $
  which is zero unless $y x y^(-1) in C$ for some $y in G$. In case
  $1_C^G lr((x))!=0$, we may assume that $x in C$, since $1_C^G$ is a class
  function. If $y in N_G lr((chevron.l x chevron.r))$, then certainly
  $y x y^(-1) in C$; the converse also holds, since if $y x y^(-1) in C$ then
  $y x y^(-1)$ is a power
  #source(401)
  of $x$, because the elements $y x y^(-1)$ and $x$ of the cyclic group $C$ have
  the same order. Therefore
  $
    1_C^G lr((x))=cases(
      0 & quad "if" y x y^(-1) in.not C "for all" y in G,
      |N_G lr((chevron.l x chevron.r))| slash |C|
      & quad "if" y x y^(-1) in C "for some" y in G.
    )
  $
  Using this result, we have
  $
    phi^*(x)=frac(|N_G lr((chevron.l x chevron.r))|, |G|)
    sum'_C sum_(C^*>=C) mu(|C^*:C|)phi(z^*),
  $
  where the sum $sum'$ is taken over cyclic subgroups $C$ containing a conjugate
  of $x$. Now $G$ contains exactly $|G:N_G lr((chevron.l x chevron.r))|$ cyclic
  groups conjugate to $chevron.l x chevron.r$, and an arbitrary cyclic subgroup
  $C$ contains at most one of these conjugates. Therefore the expression for
  $phi^*(x)$ simplifies to
  $ phi^*(x)=sum''_(C in.rev x) sum_(C^*>=C) mu(|C^*:C|)phi(z^*), $
  where the sum $sum''$ is taken over those cyclic subgroups $C$ which contain
  $x$. Rearranging the sums, we obtain
  $ phi^*(x)=sum_(C^* in.rev x) phi(z^*)sum_C mu(|C^*:C|), $
  where the outer sum is over cyclic subgroups $C^*$ containing $x$, and the
  inner sum over subgroups $C$ satisfying $C^*>=C>=chevron.l x chevron.r$. For
  each fixed subgroup $C^*$ of order $m$, the inner sum can be expressed as
  $ sum_(d divides (m slash t)) mu(d), $
  where $|chevron.l x chevron.r|=t$. By @eq:mobius-divisor-sum this sum is zero
  unless $m slash t=1$, that is, unless $C^*=chevron.l x chevron.r$. In that
  case, $x$ is a generator of $C^*$, and by
  @eq:rational-character-cyclic-generators we have $phi^*(x)=phi(x)$, completing
  the proof.
]

In Chapter~6 of Volume~II, we shall give Conlon's generalization of the Artin
Induction Theorem, dealing with permutation representations of $G$ over a field
$K$ of characteristic $p>=0$. Conlon's Theorem gives an equality of the type
@eq:artin-integral-denominator, valid in the representation algebra of $K G$
rather than in its character ring. In this formula, the subgroup $C$ of $G$ must
be allowed to range over all semidirect products $P times.r E$, in which $P$ is
any $p$-group and $E$ any cyclic $p'$-group.

#heading(level: 3)[
  Character Rings and the Brauer Induction Theorem
] <ss:character-rings-brauer-induction>
#source(402)

Throughout this section $G$ denotes a finite group, and $K$ the field of complex
numbers. The Brauer Induction Theorem states that every $K$-character of $G$ is
a $ZZ$-linear combination of induced linear characters from certain subgroups of
$G$, called elementary subgroups, which have a relatively simple structure.

After the appearance of Brauer's original proof @bib:Brauer1947b of his theorem,
new proofs were found by Roquette~@bib:Roquette1952 and by Brauer and
Tate~@bib:Brauer1955a. These made it clear that the key to the proof of the
induction theorem was the consideration of certain ideals in the commutative
ring $"ch"(K G)$ of virtual $K$-characters of $G$ (see
§@ss:finite-group-character-orthogonality). The Brauer-Tate proof of the
induction theorem was given in @bib:CurtisReiner1962[CR §40]. Here we give a new
proof, due to Goldschmidt and Isaacs~@bib:Goldschmidt1975, which has some
interesting features. These include an induction theorem for permutation
characters (due to L. Solomon), which will be used to achieve a preliminary
reduction of the problem. From this point on, the Goldschmidt-Isaacs approach is
quite constructive and explicit.

We begin with a basic lemma concerning induction of class functions. A
module-theoretic version was proved earlier in
Corollary~@cor:induction-tensor-identity.

#lemma[
  Let $H$ be a subgroup of $G$, and let $zeta in cf_K lr((G))$ and
  $psi in cf_K lr((H))$. Then
  $ zeta dot psi^G=(zeta|_H dot psi)^G. $
] <lem:class-function-induction-product>
#proof[
  Let $x in G$. Then
  $
    (zeta dot psi^G)(x)
    &=zeta(x)(|H|^(-1)sum_(y in G) dot(psi)(y x y^(-1))) \
    &=|H|^(-1)sum_(y in G) zeta(y x y^(-1))dot(psi)(y x y^(-1)) \
    &=|H|^(-1)sum_(y in G) zeta|_H lr((y x y^(-1)))
    dot(psi)(y x y^(-1))=(zeta|_H dot psi)^G lr((x)),
  $
  as required.
]

Now let us recall from §@ss:finite-group-character-orthogonality the definition
of $"ch"(K G)$, the ring of virtual $K$-characters#idx("virtual characters")
#idx("character", "virtual") of $G$. This ring consists of all $ZZ$-linear
combinations of $K$-characters of $G$, with operations of pointwise addition and
multiplication. An element $zeta in cf_K lr((G))$ belongs to $"ch"(K G)$ if and
only if the multiplicities $(zeta,zeta^((i)))$ lie in $ZZ$, for a basic set
${zeta^((1)),dots,zeta^((s))}$ of irreducible $K$-characters of $G$. Thus
$zeta in "ch"(K G)$ if and only if $zeta$ can be expressed as
$ zeta=sum_(i=1)^s a_i zeta^((i)),a_i in ZZ. $

#source(403)
#definition[
  Let $cal(H)$ be a family of subgroups of $G$. We define
  $ v(cal(H),G)=sum_(H in cal(H)) sum_(psi in "ch"(K H)) ZZ psi^G. $
] <def:induced-character-ideal>

We may express $v(cal(H),G)$ more concisely as
$ v(cal(H),G)=sum_(H in cal(H)) {"ch"(K H)}^G, $
because of the additivity of the induction map $psi -> psi^G$.

From Lemma~@lem:class-function-induction-product, it follows at once that
$v(cal(H),G)$ is an ideal in the commutative ring $"ch"(K G)$, for an arbitrary
family of subgroups $cal(H)$. Brauer's Theorem is mainly the assertion that
$v(cal(E),G)="ch"(K G)$ when $cal(E)$ is the family of elementary subgroups of
$G$.

#definition[
  A subgroup $H$ of $G$ is called _p-elementary_#idx("elementary subgroup") for
  a prime $p$, if $H$ is the direct product of a $p$-group and a cyclic group of
  order prime to $p$. The family of _elementary subgroups_ $cal(E)$ consists of
  all such subgroups, each of which is $p$-elementary for some prime $p$.
] <def:elementary-subgroup>

The Primary Decomposition Theorem implies that a cyclic group is $p$-elementary
for every prime $p$, and thus every element of $G$ is contained in some
elementary subgroup. The same result also shows that a direct product of a
$p$-group and an arbitrary cyclic group is $p$-elementary. Finally, we note that
elementary groups are nilpotent, and that subgroups of elementary groups are
elementary (because a nilpotent group is the direct product of its $p$-Sylow
subgroups).

Another family of subgroups which will be important for our considerations is
the family of _hyper-elementary groups_#idx("hyper-elementary subgroups")
$cal(H)$, defined as follows: A group $H$ is _hyper-elementary_ if there exists
a cyclic normal subgroup $chevron.l x chevron.r$ of $H$ of order prime to $p$,
such that $H slash chevron.l x chevron.r$ is a $p$-group; in other words, $H$
has a cyclic normal $p$-complement. Equivalently, $H$ is a semidirect product
$chevron.l x chevron.r times.r P$ of a cyclic $p'$-group $chevron.l x chevron.r$
and a $p$-group $P$, for some prime $p$. It follows from the homomorphism
theorems that subgroups of hyper-elementary groups are hyper-elementary. We also
observe that elementary groups are hyper-elementary, so that
$cal(E) subset.eq cal(H)$.

We can now state the main results of this section:

#theorem[
  Let $cal(E)$ be the family of elementary subgroups of $G$. Then
  $v(cal(E),G)="ch"(K G)$.
] <th:brauer-elementary-character-ideal>

#theorem(name: "Brauer Induction Theorem")[
  Every virtual character of $G$ is a $ZZ$-linear combination of induced linear
  characters from elementary subgroups of $G$. In
  #source(404)
  other words, for each $zeta in "ch"(K G)$ there exist linear characters
  ${lambda_i}$ of elementary subgroups ${H_i}$ and integers ${a_i}$, depending
  on $zeta$, such that
  $ zeta=sum a_i lambda_i^G. $
] <th:brauer-induction>
#idx("Brauer Induction Theorem", target: [@th:brauer-induction])
#idx("Induction Theorems", "Brauer", target: [@th:brauer-induction])

#theorem(title: [L. Solomon])[
  There exist rational integers ${c_i}$ such that
  $ 1_G=sum c_i lr((1_(H_i)))^G, $
  for some hyper-elementary subgroups ${H_i}$ of $G$.
] <th:solomon-permutation-induction>
#idx("Solomon's Theorem", target: [@th:solomon-permutation-induction])
#idx(
  "Induction Theorems",
  "Solomon",
  target: [@th:solomon-permutation-induction],
)

We shall first prove theorem~@th:solomon-permutation-induction, and will then
show how theorems~@th:brauer-elementary-character-ideal and @th:brauer-induction
follow from it.

This approach to Brauer's Theorem is due to Goldschmidt and
Isaacs~@bib:Goldschmidt1975 (see also Isaacs @bib:Isaacs1976, Chapter~8). The
idea is to use Solomon's Theorem~@th:solomon-permutation-induction to prove that
$1_G in v(cal(E),G)$. It will then follow that $v(cal(E),G)="ch"(K G)$ because
by Lemma~@lem:class-function-induction-product, $v(cal(E),G)$ is an ideal in
$"ch"(K G)$.

To begin the proof of Theorem~@th:solomon-permutation-induction, let
$P(cal(H),G)$ be the additive group of $ZZ$-linear combinations of permutation
characters ${1_H^G:H in cal(H)}$. If $H$ and $H'$ are subgroups of $G$, then by
the Tensor Product Theorem~@th:mackey-tensor-product we have
$ (1_H)^G dot (1_(H'))^G=sum_x (1_(attach(H, tl: x) inter H'))^G $
for certain elements $x in G$. Since subgroups of hyper-elementary groups are
hyper-elementary, it follows that $P(cal(H),G)$ is a ring of $ZZ$-valued
functions on $G$, under pointwise addition and multiplication. We have to prove
that $1_G in P(cal(H),G)$. For this purpose, we use a special case of a result
due to Banaschewski (@bib:Banaschewski1963, §1):

#lemma[
  Let $A$ be a ring#footnote[In this lemma, rings are not assumed to have
    identity elements.] <fn:nonunital-function-rings> of $ZZ$-valued functions
  on a finite set $X$, under pointwise addition and multiplication. Let $1_X$ be
  the constant function, all of whose values are equal to~1. If $1_X$ does not
  belong to $A$, then there exists an $x in X$ and a prime $p$ such that
  $p divides f(x)$ for all $f in A$.
] <lem:integer-function-ring-unit>
#proof[
  For each $x in X$, let $I_x={f(x):f in A}$. Then $I_x$ is a subring#footnote(
    <fn:nonunital-function-rings>,
  ) of $ZZ$; if $I_x!=ZZ$, then $I_x subset.eq (p)$ for some prime $p$, and
  hence $p divides f(x)$ for all $f in A$. To prove the lemma, we have to show
  that if $I_x=ZZ$ for all $x in X$, then $1_X in A$. Assuming that $1 in I_x$
  for each $x in X$, we may choose $f_x in A$ with $f_x lr((x))=1$. Then
  $ product_(x in X) (1_X-f_x)=0, $
  #source(405)
  Expanding this product, we see that $1_X$ is a $ZZ$-linear combination of
  products of the functions ${f_x}$, and hence $1_X in A$, as required.
]

We can now complete the proof of @th:solomon-permutation-induction. By
Lemma~@lem:integer-function-ring-unit, it is sufficient to show that given
$x in G$ and a prime $p$, there exists a hyper-elementary subgroup $H$ such that
$p divides.not (1_H^G)(x)$. Let $C$ be the $p$-complement in
$chevron.l x chevron.r$, and let $N=N_G lr((C))$; let $H slash C$ be a Sylow
$p$-subgroup of $N slash C$. Then $H$ is hyper-elementary, with cyclic
$p$-complement $C$.

Now $1_H^G lr((x))$ is equal to the number of left cosets ${g H}$ fixed by $x$.
If $x g H=g H$, then $x^g in H$, whence $C^g<=chevron.l x chevron.r^g<=H$. Since
$C$ is the unique subgroup in $H$ of its order, we have $C^g=C$, and
$g in N_G lr((C))=N$. Noting that $x$ also lies in $N$, we have shown that
$ 1_H^G lr((x))=1_H^N lr((x)). $
Next, $C ⊴ N$ and $C<=H$, which imply that $C$ acts trivially on the cosets of
$H$ in $N$. Moreover, $chevron.l x chevron.r slash C$ is a $p$-group, so that
the number of elements in each non-trivial orbit of $chevron.l x chevron.r$
acting on $N slash H$ is divisible by $p$. The total number of cosets being
permuted is $|N:H|$, whence the number of fixed cosets under the action of $x$
is congruent to $|N:H|$ mod $p$. We have thus shown that
$ 1_H^N lr((x)) equiv |N:H| quad (mod p). $
But $|N:H|$ is prime to $p$, so that $p divides.not (1_H)^N lr((x))$, as
required. This completes the proof of @th:solomon-permutation-induction.

We next prove that Theorem~@th:solomon-permutation-induction implies
Theorem~@th:brauer-elementary-character-ideal. Because $v(cal(E),G)$ is an ideal
in $"ch"(K G)$ by Lemma~@lem:class-function-induction-product, it suffices to
prove that $1_G in v(cal(E),G)$. By @th:solomon-permutation-induction and
transitivity of induction, we may assume that $G$ is hyper-elementary. Using
induction on $|G|$, it thus suffices to prove that if $G$ is hyper-elementary
but not elementary, then $1_G$ is a $ZZ$-linear combination of characters
induced from proper subgroups of $G$. This can be established quite explicitly,
as follows:

We have $G=C times.r P$, where $C$ is a cyclic $p'$-group and $P$ is a
$p$-group, for some prime $p$. Let $Z$ be the centralizer in $C$ of the subgroup
$P$; then $Z<C$ since we are assuming that $G$ is not elementary. Put
$H=Z times P$, so $H<G$; we shall prove
$ 1_H^G=1_G+sum xi_i, $ <eq:hyper-elementary-proper-induction>
where the ${xi_i}$ are irreducible characters of $G$ which are induced from
proper subgroups of $G$. This will imply that $1_G$ is itself a $ZZ$-linear
combination of characters induced from proper subgroups, and so the proof of
@th:brauer-elementary-character-ideal will be finished.

#source(406)
Since $G=H C$, we have
$ (1_H^G)|_C=(1_(C inter H))^C=1_Z^C $
by the Subgroup Theorem~@th:mackey-subgroup. Let
@eq:hyper-elementary-proper-induction be the decomposition of $1_H^G$ as a sum
of irreducible complex characters. Restricting to $C$, we obtain
$ 1_Z^C=1_C+sum xi_i|_C. $ <eq:hyper-elementary-cyclic-restriction>
By Frobenius Reciprocity we deduce that $(xi_i|_Z,1_Z)!=0$ for each $i$;
further, $xi_i|_C!=1_C$ for each $i$, since $1_C$ occurs with multiplicity~1 in
$1_Z^C$. Since $C$ is a cyclic normal subgroup of $G$, it now follows from
@prop:clifford-character-restriction that for each $i$, $xi_i$ is a component of
$lambda^G$ for some linear character $lambda!=1$ of $C$, and furthermore
$Z<=ker lambda$. However, @th:gallagher-character-extension(iii) gives the
decomposition of $lambda^G$ into irreducible characters, each of which is
induced from a character of the stabilizer $G_lambda$. If we can show that
$G_lambda<G$, it will thus follow that each $xi_i$ occurring in
@eq:hyper-elementary-proper-induction is induced from a proper subgroup of $G$,
and we will have proved Theorem~@th:brauer-elementary-character-ideal. We need
only use the following (see Isaacs @bib:Isaacs1976, Lemma~8.11):

#lemma[
  Let $G$ be a finite group such that $G=N times.r P$, where $N$ is a $p'$-group
  and $P$ is a $p$-group for some prime $p$. Let $lambda$ be a linear character
  of $N$ whose stabilizer $G_lambda$ coincides with $G$, and is such that
  $Z<=ker lambda$, where $Z=C_N lr((P))$. Then $lambda=1_N$.
] <lem:coprime-invariant-linear-character>
#proof[
  Let $L=ker lambda$. Since $lambda$ is linear, $lambda$ takes distinct constant
  values on the cosets of $L$ in $N$. For $y in P$,
  $attach(lambda, tl: y)=lambda$ by hypothesis; the preceding remark then shows
  that each coset $n L$ of $L$ in $N$ is fixed under conjugation by $y$. Now $P$
  is a $p$-group, so the length of each nontrivial orbit in $n L$ under the
  action of $P$ is a multiple of $p$. Since the number of elements in $n L$ is
  prime to $p$, there must be at least one trivial orbit. Hence some element of
  $n L$ lies in the centralizer $Z$ of $P$ in $N$. Since $Z<=L$ by hypothesis,
  this shows that each coset $n L$ coincides with $L$, and therefore $L=N$. We
  have thus proved that $lambda=1_N$, as required.
]

Finally, we show that Theorem~@th:brauer-elementary-character-ideal implies the
Brauer Induction Theorem~@th:brauer-induction. By
Theorem~@th:brauer-elementary-character-ideal, it suffices to prove that each
irreducible character of an elementary group $H$ is induced from a linear
character of some elementary subgroup $H_0$ of $H$. We have already pointed out
that subgroups of elementary groups are elementary, and that elementary groups
are nilpotent. Thus the desired result follows from
Theorem~@th:nilpotent-group-monomial and the proof of @th:brauer-induction is
finished.

#heading(level: 3)[
  Applications of the Brauer Induction Theorem
] <ss:applications-brauer-induction>

Let us keep the notation of §@ss:character-rings-brauer-induction. In
particular, $K$ is the complex field, $"ch"(K G)$ the ring of virtual
$K$-characters of $G$, and $cal(E)$ denotes the family of all elementary
subgroups of $G$.

#source(407)
#theorem(name: "Brauer's Criterion for Virtual Characters")[
  A class function $phi in cf_K lr((G))$ belongs to $"ch"(K G)$ if and only if
  for all elementary subgroups $H<=G$, we have $phi|_H in "ch"(K H)$.
] <th:brauer-virtual-character-criterion>
#idx(
  "Brauer criterion for virtual characters",
  target: [@th:brauer-virtual-character-criterion],
)
#idx("character", "virtual", target: [@th:brauer-virtual-character-criterion])
#proof[
  One way is clear. For the other part, let $phi in cf_K lr((G))$ be such that
  $phi|_H in "ch"(K H)$ for all subgroups $H in cal(E)$. From
  @th:brauer-induction, we may write
  $ 1_G=sum a_i lambda_i^G,a_i in ZZ,lambda_i in "ch"(K H_i),H_i in cal(E). $
  Then by @lem:class-function-induction-product,
  $
    phi=phi dot 1_G=sum a_i lr((phi dot lambda_i^G))
    =sum a_i lr([(phi|_(H_i))lambda_i])^G in "ch"(K G),
  $
  as required. (The last step follows from the hypothesis and the fact that the
  product of two virtual characters of $H_i$ is a virtual character.)
]

The above result has been one of the most useful theorems for constructing
character tables of finite groups. For a given finite group, it is often
possible to guess at some class functions, and then use
@th:brauer-virtual-character-criterion to prove that they are virtual
characters. One then obtains irreducible characters from the observation that if
$phi$ is a virtual character for which $(phi,phi)=1$, then
$plus.minus phi in Irr(G)$.

The next result settles an old problem considered by Burnside, Maschke and
Schur. Evidently the value of the irreducible complex characters of $G$ belong
to the cyclotomic field $QQ(omega_n)$, where $n=|G|$ and $omega_n$ is a
primitive $n$-th root of~1 (see §@ss:cyclotomic-fields). The question is whether
$QQ(omega_n)$ is a splitting field for $G$.

#theorem(name: "Brauer's Splitting Field Theorem")[
  Let $G$ be a finite group of order $n$. The cyclotomic field $QQ(omega_n)$,
  generated by a primitive $n$-th root of~1, is a splitting field for $G$.
] <th:brauer-cyclotomic-splitting-field>
#idx(
  "Brauer Splitting Field Theorem",
  target: [@th:brauer-cyclotomic-splitting-field],
)
#idx("splitting field", target: [@th:brauer-cyclotomic-splitting-field])
#proof(head: emph[Proof (Feit).])[
  By Proposition~@prop:splitting-field-criteria, it is sufficient to prove that
  every irreducible $K$-representation of $G$ can be realized in $QQ(omega_n)$.
  Referring to @th:brauer-induction, it is clear that the linear representations
  $lambda$ of elementary subgroups of $G$ are $QQ(omega_n)$-representations, and
  hence each induced representation $lambda^G$ is also a
  $QQ(omega_n)$-representation. Now let $upright(bold(T))$ be an irreducible
  $K$-representation of $G$ with character $tau$. By @th:brauer-induction we
  have
  $ tau=sum a_i lambda_i^G,a_i in ZZ, $
  where the ${lambda_i^G}$ are characters of $QQ(omega_n)$-representations of
  $G$. If all the coefficients ${a_i}$ are positive then $tau$ is afforded by a
  $QQ(omega_n)$-representation, and there is nothing left to prove. If some
  coefficients ${a_i}$ are negative, then by rearranging terms we have
  $ tau_2=tau+tau_1, $ <eq:virtual-character-realization-difference>
  #source(408)
  where $tau_1$ and $tau_2$ are characters of $QQ(omega_n)$-representations
  $upright(bold(T))_1$ and $upright(bold(T))_2$ respectively, and we have
  $
    upright(bold(T))_2^K tilde.equiv
    upright(bold(T))_1^K plus.o upright(bold(T)).
  $
  But then $upright(bold(T))$ can be realized in $QQ(omega_n)$, by
  Exercise~@exc:semisimple-scalar-extension-complement, which completes the
  proof.
]

#corollary[
  Let $F$ be a field of characteristic~0, $G$ a finite group of
  exponent#footnote[The exponent of $G$ is the L.C.M. of the orders of the
    elements of $G$.] $n$, and $omega$ a primitive $n$-th root of~1 over $QQ$.
  Then every field $E$ containing $F(omega)$ is a splitting field for $G$ and
  all of its subgroups.
] <cor:exponent-cyclotomic-splitting-field>
#proof[
  The proof of Theorem~@th:brauer-cyclotomic-splitting-field shows in fact that
  $QQ(omega)$ is a splitting field for $G$. Since
  $E supset.eq F(omega) supset.eq QQ(omega)$, and extensions of splitting fields
  are also splitting fields, it follows that $E$ is a splitting field for $G$.
  The corresponding statement for subgroups of $G$ is then obvious.
]

Our next result is an interesting criterion, due to
Gallagher~@bib:Gallagher1966, for the vanishing of irreducible characters of $G$
on certain types of elements. The reader will note that many occurrences of
zeros in the character tables constructed in the exercises in
§§@sec:orthogonality-central-idempotents–@sec:clifford-theory-hecke-algebras,
for example, are accounted for by Gallagher's Theorem. Gallagher's result should
be compared with the classical result of Burnside that every irreducible
non-linear $CC$-character of $G$ has at least one zero (see
@bib:CurtisReiner1962[CR Exercise31.3]).

We first introduce some terminology. Let $Pi$ be a set of rational primes. A
positive integer $m$ is a $Pi$-number if each prime factor of $m$ belongs to
$Pi$, and a $Pi'$-number if no prime factor of $m$ belongs to $Pi$. Each $m$ can
be written uniquely as $m=m_Pi m_(Pi')$, where $m_Pi$ is the $Pi$-part#idx(
  "p-part",
) of $m$ and is a $Pi$-number, and $m_(Pi')$ is the $Pi'$-part and is a
$Pi'$-number. A finite group $G$ is a $Pi$-group if $|G|$ is a $Pi$-number.
Similarly, we define $Pi'$-groups, and $Pi$- and $Pi'$-elements of $G$.#idx(
  "p-element, Π-element",
)#idx("p′-element, Π′-element") Extending the terminology used for a single
prime, an element $x in G$ is called $Pi$-_regular_#idx("p-regular, Π-regular")
if $x$ is a $Pi'$-element, and $Pi$-_irregular_#idx("p-irregular, Π-irregular")
otherwise. Thus, $x$ is $Pi$-irregular if and only if the order of $x$ has a
prime factor from $Pi$.

#theorem(title: [Gallagher~@bib:Gallagher1966])[
  Let $G$ be a finite group and $Pi$ a set of primes. Let $zeta$ be an
  irreducible complex character of $G$ whose degree is divisible by $|G|_Pi$.
  Then $zeta$ vanishes on all $Pi$-irregular elements of $G$.
] <th:gallagher-character-vanishing>
#idx("Gallagher's Theorem", target: [@th:gallagher-character-vanishing])

#remark(numbered: false)[
  By Proposition~@prop:character-degree-divides-group-order, the degree of
  $zeta$ divides $|G|$, so the hypothesis is equivalent to the statement that
  $|G| slash deg zeta$ is a $Pi'$-number, or equivalently, that
  $|G|_Pi=zeta(1)_Pi$. It should also be noted that the Theorem follows at once
  from @prop:defect-zero-character-projective-simple below.
]

#proof[
  Throughout the proof, all characters of $G$ and its subgroups are taken in the
  complex field $K$. Here is the idea of the proof. Define a class function
  $phi$
  #source(409)
  on $G$ by setting,
  $
    phi(x)=cases(
      zeta(x) & quad "if" x "is" Pi "-regular",
      0 & quad "if" x "is" Pi "-irregular".
    )
  $
  We shall use Brauer's Criterion~@th:brauer-virtual-character-criterion to show
  that $phi in "ch"(K G)$. Once this is done, from the inequalities
  $0<(phi,phi)<=(zeta,zeta)=1$ we obtain $(phi,phi)=1$. Then
  $(phi,zeta)=(phi,phi)=1$, so $(phi-zeta,phi-zeta)=0$, whence $phi=zeta$, and
  the theorem is proved.

  In order to use Brauer's Criterion, we must show that $phi|_H in "ch"(K H)$
  for each $H in cal(E)$, where $cal(E)$ is the family of elementary subgroups
  of $G$. Equivalently, we must show that $(phi|_H,lambda)_H in ZZ$ for all
  $K$-characters $lambda$ of $H$, and all $H in cal(E)$. Given $H in cal(E)$, we
  may write $H=A times B$, where $A$ is a $Pi'$-subgroup and $B$ a
  $Pi$-subgroup. Using the definition of $phi$ and the factorization of $H$, we
  obtain for each $lambda$:
  $
    (phi|_H,lambda)_H & =|H|^(-1)sum_(x in H) phi(x)overline(lambda(x))
                        =|H|^(-1)sum_(x in A) phi(x)overline(lambda(x)) \
                      & =|A||H|^(-1)(zeta_A,lambda_A)_A
                        =|B|^(-1)(zeta_A,lambda_A)_A.
  $
  We shall prove below that $|B|^(-1)zeta(x) in "alg. int."{K}$ for each
  $x in A$. Taking this for granted for the moment, let $m=(zeta_A,lambda_A)_A$,
  so $m in ZZ$ because $zeta_A,lambda_A$ are $K$-characters of $A$. Then
  $ m|A| slash |B|=|A|(|B|^(-1)zeta_A,lambda_A)_A in "alg. int."{K}, $
  so $|B|$ divides $m|A|$. Since $|B|$ is relatively prime to $|A|$, this shows
  that $|B|$ divides $m$, whence $(phi|_H,lambda_H)_H in ZZ$ as desired.

  To complete the proof, let $x in A$ and let us show that $|B|^(-1)zeta(x)$ is
  an algebraic integer. We have
  $ zeta(x) dot |G:C_G lr((x))| slash zeta(1) in "alg. int."{K} $
  by @eq:central-character-class-sum-values and
  @prop:central-character-values-integral. But $C_G lr((x))>=B$, so
  $|G:C_G lr((x))||C_G lr((x)):B|=|G:B|$. Moreover $zeta(1)_Pi=|G|_Pi$ by
  hypothesis. Using the fact that
  $ |G:C_G lr((x))|_Pi=|G|_Pi |B|_Pi^(-1)|C_G lr((x)):B|_Pi^(-1), $
  we obtain
  $
    frac(
      zeta(x)|G:C_G lr((x))|,
      zeta(1)
    ) & =
        frac(
          zeta(x)|G:C_G lr((x))|_Pi |G:C_G lr((x))|_(Pi'),
          zeta(1)_Pi zeta(1)_(Pi')
        ) \
      & =
        frac(
          zeta(x)|G|_Pi |G:C_G lr((x))|_(Pi'),
          zeta(1)_Pi zeta(1)_(Pi') |B|_Pi |C_G lr((x)):B|_Pi
        ) \
      & =
        frac(
          zeta(x)|G:C_G lr((x))|_(Pi'),
          zeta(1)_(Pi') |B|_Pi |C_G lr((x)):B|_Pi
        ).
  $
  #source(410)
  Therefore,
  $ frac(zeta(x)|G:C_G lr((x))|_(Pi'), |B|) in "alg. int."{K}. $
  But $|G:C_G lr((x))|_(Pi')$ is invertible modulo the $Pi$-number $|B|$, so the
  above implies that $|B|^(-1)zeta(x) in "alg. int."{K}$. This completes the
  proof.
]

=== Extensions of Invariant Characters <ss:extensions-invariant-characters>

We continue with another application of Brauer's Theorem, to the question of
when an irreducible character $psi$ of a normal subgroup can be extended to its
stabilizer. We shall give several criteria for such extensions to exist; each
criterion, when combined with Theorem~@th:gallagher-character-extension, gives
an explicit construction of the irreducible components of $psi^G$. All the
results in this section are contained in Gallagher's paper @bib:Gallagher1962b.

We begin with some preliminary remarks. We shall be concerned throughout
exclusively with $K$-characters of a finite group $G$ and its subgroups, where
$K=CC$. Let $N ⊴ G$, and let $psi in Irr_K lr((N))$. We call $psi$ an _invariant
character_#idx("invariant character")#idx("character", "invariant") if its
stabilizer $G_psi$ coincides with $G$ (see §@ss:clifford-character-theory). A
$K$-character $zeta$ of $G$ _extends_ $psi$ (or is an _extension of_ $psi$)#idx(
  "extension of character",
) if $zeta|_N=psi$; such an extension, if it exists, is automatically
irreducible. Let $zeta_1$ be a fixed extension of $psi$; then from
@cor:gallagher-invariant-character we know that any other extension $zeta$ can
be expressed in the form $zeta=zeta_1 omega$ for a uniquely determined linear
character $omega$ of $G slash N$.

For a character $mu$ of $G$, irreducible or not, we shall write $mu in psi^G$ to
indicate that either $psi^G=mu$ or that $psi^G=mu+mu'$ for some other character
$mu'$. Next, we note that if $upright(bold(M))$ is a $K$-representation of $G$
with character $mu$, then $det upright(bold(M))$ is a linear representation of
$G$, which depends only on the equivalence class of $upright(bold(M))$. We
denote the character of $det upright(bold(M))$ by $det mu$, so
$ (det mu)(x)=det upright(bold(M))(x),x in G. $
(See §@ss:transfer-determinant-map for connections between $det mu$ and the
transfer map.) For each linear character $omega$ of $G$, we have
$ det(omega mu)=omega^(deg mu)det mu. $ <eq:linear-twist-determinant>
Our first result is an application of the results in
§@ss:clifford-character-theory:

#proposition[
  Let $N$ be a normal subgroup of prime index $p$ in $G$. Then each invariant
  irreducible character $psi$ of $N$ extends to a character of $G$.
] <prop:prime-index-invariant-character-extension>
#proof[
  Let $zeta in Irr(G)$ be such that $(zeta,psi^G)>0$. By
  Proposition~@prop:clifford-character-restriction, $zeta|_N=a psi$ for some
  positive integer $a$, because $psi$ is invariant. The factor group $G slash N$
  is cyclic of order $p$, and for each linear character $omega$ of $G slash N$,
  we have $omega zeta in Irr_K lr((G))$
  #source(411)
  and $omega zeta|_N=a psi$. The characters
  ${omega zeta:omega in Irr_K lr((G slash N))}$ are distinct. In fact, if
  $omega zeta=omega' zeta$ for $omega!=omega'$, then $zeta=0$ off $N$, and we
  have,
  $ a^2=(zeta|_N,zeta|_N)_N=p(zeta,zeta)_G=p, $
  which is impossible. Therefore, by Frobenius Reciprocity,
  $ sum_omega a dot omega zeta in psi^G. $
  Since
  $ (psi^G,psi^G)_G=(psi^G|_N,psi)_N=p $
  because $psi$ is invariant, we conclude that $a=1$, and hence $zeta$ extends
  $psi$, as required.
]

The next result gives a criterion for extensions to exist, which depends on
Brauer's Theorem.

#proposition[
  Let $N ⊴ G$, and let $psi$ be an irreducible invariant character of $N$.
  Suppose that for each intermediate subgroup $H$ for which $H slash N$ is
  elementary, $psi$ can be extended to a character $psi_H$ of $H$. Assume
  further that the extensions ${psi_H}$ satisfy the following two conditions:
  #enum(
    numbering: "(i)",
    [$attach((psi_H), tl: x)=psi_(attach(H, tl: x))$, $forall x in G$,],
    [$psi_(H')=psi_(H'')|_(H')$ if $H'<=H''$.],
  )
  Then $psi$ can be extended to a character of $G$.
] <prop:compatible-elementary-character-extensions>
#proof[
  Let $1_(G slash N)$ denote the trivial character of $G slash N$, lifted to a
  trivial character of $G$. Then by Brauer's Theorem~@th:brauer-induction, we
  may write
  $ 1_(G slash N)=sum a_i lambda_i^G,a_i in ZZ, $
  where ${lambda_i}$ ranges over linear characters of subgroups ${H_i}$, with
  $H_i>=N$, $H_i slash N$ elementary, and $N<=ker lambda_i$. Define
  $ zeta=sum a_i lr((lambda_i psi_(H_i)))^G. $
  Then $zeta in "ch"(K G)$. Moreover, by an easy calculation using
  @eq:induced-character-average, we have
  $
    (lambda_i psi_(H_i))^G lr((n))=lambda_i^G lr((n))psi_(H_i) lr((n)),
    forall n in N,
  $
  and it follows that $zeta|_N=psi$.

  #source(412)
  To complete the proof, we must show that $zeta in Irr_K lr((G))$, and for this
  it suffices to prove that $(zeta,zeta)_G=1$. Indeed, the latter implies that
  $plus.minus zeta in Irr_K lr((G))$, and then $zeta in Irr_K lr((G))$ because
  $zeta(1)=psi(1)>0$. We have
  $
    1=(1_(G slash N),1_(G slash N))_G=
    sum_(i,j) a_i a_j lr((lambda_i^G,lambda_j^G))_G,
  $
  and
  $
    (zeta,zeta)=sum_(i,j) a_i a_j
    lr(((lambda_i psi_(H_i))^G,(lambda_j psi_(H_j))^G))_G.
  $
  In order to prove that $(zeta,zeta)=1$, it is sufficient to show that
  corresponding terms in the sums are equal. We have, by the Intertwining Number
  Theorem,
  $
    ((lambda_i psi_(H_i))^G,(lambda_j psi_(H_j))^G)_G
    =sum_x (attach((lambda_i psi_(H_i)), tl: x),lambda_j psi_(H_j))_(
    attach(H_i, tl: x) inter H_j),
  $
  where the sum is taken over representatives ${x}$ of $(H_i,H_j)$ double cosets
  in $G$. The subgroups $attach(H_i, tl: x) inter H_j$ contain $N$, and the
  factor groups $(attach(H_i, tl: x) inter H_j) slash N$ are elementary. By
  hypotheses~(i) and~(ii) of the proposition, we have
  $
    (attach((lambda_i psi_(H_i)), tl: x),lambda_j psi_(H_j))_(
    attach(H_i, tl: x) inter H_j)
    =(attach(lambda_i, tl: x)psi_(attach(H_i, tl: x) inter H_j),
      lambda_j psi_(attach(H_i, tl: x) inter H_j)).
  $
  From the remarks at the beginning of this section, the above scalar product is
  1 or 0, according as the linear characters $attach(lambda_i, tl: x)$ and
  $lambda_j$ coincide on $attach(H_i, tl: x) inter H_j$ or not. Therefore the
  above product is equal to $(attach(lambda_i, tl: x),lambda_j)_(
  attach(H_i, tl: x) inter H_j)$, and we conclude that $(zeta,zeta)_G=1$, as
  required.
]

In order to state the main result of this section, we recall one more bit of
terminology from finite group theory. A subgroup $H$ of $G$ is called a _Hall
subgroup_#idx("Hall subgroup") if the order $|H|$ and the index $|G:H|$ are
relatively prime. The main result#footnote[The same result holds for
  representations over an arbitrary field; see Isaacs @bib:Isaacs1981.] can then
be stated as follows:

#theorem(title: [Gallagher])[
  Every invariant irreducible character $psi$ of a normal Hall subgroup $N$ of
  $G$ extends to a character of $G$.
] <th:gallagher-normal-hall-character-extension>
#idx(
  "Gallagher's Theorem",
  target: [@th:gallagher-normal-hall-character-extension],
)

The proof depends on one more preliminary result, which is of independent
interest:

#proposition[
  Let $N ⊴ G$ and let $psi$ be an irreducible invariant character of $N$, such
  that the following conditions hold:
  #enum(
    numbering: "(i)",
    [$det psi$ extends to a character $xi$ of $G$;],
    [$deg psi$ is prime to $|G:N|$.],
  )
  #source(413)
  Then there is a unique irreducible character $zeta$ of $G$ such that
  $zeta|_N=psi$ and $det zeta=xi$.
] <prop:coprime-degree-determinant-extension>
#proof[
  We first show that if $psi$ extends to a character of $G$, there is a unique
  extension $zeta$ such that $det zeta=xi$. In fact, from the preliminary
  remarks of this section, all extensions are given by $omega zeta_1$, where
  $zeta_1$ is any one fixed extension, and $omega$ ranges over the linear
  characters of $G slash N$. Since $xi(det zeta_1)^(-1)$ is a linear character
  of $G slash N$ and $deg psi$ is prime to $|G:N|$, there is a unique element of
  the finite abelian group of linear characters of $G slash N$ such that
  $ omega^(deg psi)=xi(det zeta_1)^(-1). $
  For this character $omega$ we have, by @eq:linear-twist-determinant,
  $ det(omega zeta_1)=omega^(deg psi)det zeta_1=xi, $
  as required.

  To prove the existence of an extension, suppose first that $G slash N$ is
  supersolvable (see Exercise~@exc:supersolvable-monomial). If $G=N$, put
  $zeta=psi$. If $G!=N$, let $H slash N$ be a normal subgroup of prime order of
  $G slash N$. Since $psi$ is invariant under $H$,
  Proposition~@prop:prime-index-invariant-character-extension implies that $psi$
  extends to a character of $H$. By the preceding paragraph, $psi$ has a unique
  extension $psi_1$ such that $det psi_1=xi|_H$. For each $x in G$,
  $attach(psi_1, tl: x)$ is an extension of $psi$ to $H$ such that
  $det(attach(psi_1, tl: x))=xi|_H$. Then $attach(psi_1, tl: x)=psi_1$ by
  uniqueness, and $psi_1$ is invariant. By induction, $psi_1$ extends to a
  character of $G$.

  To complete the proof in the general case, we note that elementary groups are
  nilpotent, hence supersolvable. Hence there are unique extensions $psi_H$ of
  $psi$ to the groups $H>=N$ such that $H slash N$ is elementary, and these
  satisfy $det psi_H=xi|_H$. Properties~(i) and~(ii) of
  Proposition~@prop:compatible-elementary-character-extensions follow from the
  uniqueness and the invariance of $xi$ under conjugation. We can then apply
  Proposition~@prop:compatible-elementary-character-extensions to conclude that
  an extension exists, completing the proof of
  Proposition~@prop:coprime-degree-determinant-extension.
]

#proof(head: emph[Proof of
  Theorem~@th:gallagher-normal-hall-character-extension.])[
  Let $psi$ be an invariant character of $N$, as in the Theorem. Then $deg psi$
  divides $|N|$, by Proposition~@prop:character-degree-divides-group-order, and
  hence $deg psi$ and $|G:N|$ are relatively prime since $N$ is a Hall subgroup.
  Moreover, by Schur's Theorem~@th:schur-zassenhaus, there exists a subgroup $H$
  of $G$ such that
  $ G=N H,N inter H={1}. $
  Since $det psi$ is a linear character of $N$, and is invariant because of the
  invariance of $psi$, the construction used in part~(ii) of
  Proposition~@prop:little-groups shows at once that $det psi$ can be extended
  to a character of $G$. We then apply
  Proposition~@prop:coprime-degree-determinant-extension to conclude that $psi$
  extends to a character of $G$, which completes the proof of Gallagher's
  Theorem~@th:gallagher-normal-hall-character-extension.
]

#heading(level: 3)[
  A Criterion for Existence of Normal Complements
] <ss:normal-complement-criterion>
#source(414)

We give one more application of Brauer's Theorem, this time to group theory. We
say that a subgroup $S$ of a finite group $G$ has a _normal complement_#idx(
  "normal complement",
) if there exists a normal subgroup $N$ of $G$ such that $G$ is the semidirect
product, $G=N times.r S$. Burnside's Transfer
Theorem~@th:burnside-normal-p-complement gives a criterion for Sylow
$p$-subgroups to have normal complements. Another criterion for the existence of
normal complements is provided by Frobenius' Theorem~@th:frobenius-kernel. The
main result of this subsection, due to Brauer~@bib:Brauer1964b and
Suzuki~@bib:Suzuki1963, includes both of the above results as special cases. The
proof is based on Brauer's Criterion for Virtual
Characters~@th:brauer-virtual-character-criterion. Our presentation follows
Isaacs~@bib:Isaacs1976 (see also Huppert @bib:Huppert1967, Chapter~5, (19.12)
for a proof of Frobenius' Theorem by the same method).

Before stating the result, we recall from §@ss:extensions-invariant-characters
that a subgroup $S$ of $G$ is a _Hall subgroup_#idx("Hall subgroup") if its
order $|S|$ and index $|G:S|$ are relatively prime.

#theorem[
  Let $S$ be a Hall subgroup of $G$, which satisfies both of the following
  conditions:
  #enum(
    numbering: "(i)",
    [If $x,y in S$ are conjugate in $G$, then they are conjugate in $S$;],
    [Each elementary subgroup $H$ of $G$, whose order divides $|S|$, is
      conjugate to a subgroup of $S$.],
  )
  Then $S$ has a normal complement in $G$.
] <th:hall-subgroup-normal-complement>
#idx("Brauer-Suzuki Theorem", target: [@th:hall-subgroup-normal-complement])
#proof[
  Let $Pi$ be the set of primes which divide $|S|$, and let us adopt the
  terminology “$Pi$-element”, “$Pi$-subgroup”, etc. as in the discussion
  preceding @th:gallagher-character-vanishing. For each $x in G$, we may apply
  the Primary Decomposition Theorem to the cyclic group $chevron.l x chevron.r$,
  and conclude that $x$ is uniquely expressible in the form
  $ x=x_Pi x_(Pi'),"where" x_Pi=Pi "-element",x_(Pi')=Pi' "-element", $
  and where $x_Pi$ commutes with $x_(Pi')$. (Indeed, both $x_Pi$ and $x_(Pi')$
  are suitable powers of $x$.) We now proceed in a series of steps.

  #case-list(
    numbering: "Step 1.",
    [#case[
      Let $phi in "ch" K S$, where $K=CC$. We define a class function
      $tilde(phi)$ on $G$ as follows. Let $x in G$; then
      $chevron.l x_Pi chevron.r$ is an elementary subgroup whose order divides
      $|S|$. By part~(ii) of the hypothesis, $x_Pi$ is conjugate to an element
      $s in S$, and we set
      $ tilde(phi)(x)=phi(s). $
      By part~(i) of the hypothesis, it follows that $tilde(phi)$ is a
      well-defined class function on $G$.

      Now let ${s_1,dots,s_t}$ be representatives of the conjugacy classes of
      $S$, and for each $i$, $1<=i<=t$, let $m_i$ be the number of elements
      $x in G$ such that $x_Pi=_G s_i$.
      #source(415)
      Then for all virtual $K$-characters $phi$ and $psi$ of $S$, we have
      $
        (tilde(phi),tilde(psi))_G=|G|^(-1)sum_(i=1)^t m_i phi(s_i)psi(s_i^(-1)).
      $
      <eq:normal-complement-lift-scalar-product>
    ] <case:normal-complement-class-function-lift>],
    [#case[
      We prove that if $phi in "ch" K S$, then $tilde(phi) in "ch" K G$. By
      @th:brauer-virtual-character-criterion, it suffices to prove that for all
      elementary subgroups $H$ of $G$, we have $tilde(phi)_H in "ch" K H$. The
      elementary subgroup $H$ of $G$ may be written as $H=A times B$, where $A$
      is a $Pi$-subgroup and $B$ a $Pi'$-subgroup. By hypothesis~(ii), we may
      assume that $A<=S$. For all $a in A$, $b in B$, we have $(a b)_Pi=a$, and
      hence $tilde(phi)_H lr((a b))=phi(a)$. Now let $phi_A=sum c_i xi_i$, where
      $xi_i in Irr A$, $c_i in ZZ$. Let $xi_i times.o 1_B$ denote the character
      of $A times B$ which is the product of $xi_i$ and the trivial character
      $1_B$ of $B$. Then for all $a in A$, $b in B$, we have
      $
        tilde(phi)_H lr((a b))=phi(a)=sum c_i xi_i lr((a))
        =sum c_i lr((xi_i times.o 1_B))(a b).
      $
      Thus $tilde(phi)_H=sum c_i lr((xi_i times.o 1_B)) in "ch" K H$, and by
      Brauer's Criterion~@th:brauer-virtual-character-criterion it follows that
      $tilde(phi) in "ch" K G$, as desired.
    ] <case:normal-complement-virtual-character-lift>],
    [#case[
      Next we prove that for all virtual characters $phi,psi in "ch" K S$, we
      have
      $ (tilde(phi),tilde(psi))_G=(phi,psi)_S. $
      We first require some preliminary remarks. Let $R=ZZ[omega]$, where
      $omega$ is a primitive $|G|$-th root of~1. Then $R$ is a ring of algebraic
      integers in the complex field $K$. We set
      $"ch"_R K G=R times.o_ZZ "ch" K G$; since the characters in $Irr G$ are a
      $ZZ$-basis of $"ch" K G$, they are also an $R$-basis of $"ch"_R K G$.
      Therefore, $"ch"_R K G$ can be identified with the set of $R$-linear
      combinations of the elements of $"ch" K G$. Similar remarks apply to
      $"ch"_R K S$. It follows at once from
      @case:normal-complement-virtual-character-lift that if $mu in "ch"_R K S$,
      and $tilde(mu)$ is defined as above, then $tilde(mu) in "ch"_R K G$;
      indeed, if we write $mu=sum a_i phi_i$, with $phi_i in Irr S$, $a_i in R$,
      then $tilde(mu)=sum a_i tilde(phi_i) in "ch"_R K G$.

      Now consider the class functions ${gamma_i:1<=i<=t}$ defined by
      $ gamma_i=sum_(phi in Irr S) phi(s_i^(-1))phi in cf_K lr((S)),1<=i<=t, $
      where ${s_1,dots,s_t}$ are representatives of the conjugacy classes in
      $S$, as in @case:normal-complement-class-function-lift. Using the Second
      Orthogonality Relation~@prop:first-second-character-orthogonality, we have
      $ gamma_i lr((s_j))=cases(|C_S lr((s_i))| & quad j=i, 0 & quad j!=i), $
      where $i$ and $j$ range from~1 to $t$. Since each coefficient
      $phi(s_i^(-1))$ lies in $R$, we have $gamma_i in "ch"_R K S$, and hence
      $tilde(gamma)_i in "ch"_R K G$ by the preceding remarks and
      @case:normal-complement-virtual-character-lift.

      #source(416)
      Let us show that $m_i=|G:C_S lr((s_i))|$ for each $i$, $1<=i<=t$. By
      @eq:normal-complement-lift-scalar-product we have
      $
        (tilde(gamma)_i,1_G)=|G|^(-1)sum_(j=1)^t m_j gamma_i lr((s_j))
        =|G|^(-1) dot m_i dot |C_S lr((s_i))| in R inter QQ,
      $
      and so $|G|^(-1) dot m_i dot |C_S lr((s_i))| in ZZ$, $1<=i<=t$. Therefore
      $m_i>=|G:C_S lr((s_i))|$ for each $i$, and we obtain
      $
        |G|=sum_(i=1)^t m_i>=sum_(i=1)^t |G:C_S lr((s_i))|
        =|G:S| dot sum_(i=1)^t |S:C_S lr((s_i))|.
      $
      But $|S:C_S lr((s_i))|$ is the number of distinct conjugates of $s_i$ in
      $S$, so $sum |S:C_S lr((s_i))|=|S|$, and we have
      $ |G|=sum m_i>=|G:S| dot |S|=|G|. $
      Thus we must have equality, and therefore $m_i=|G:C_S lr((s_i))|$ for each
      $i$. To conclude this step, we use
      @eq:normal-complement-lift-scalar-product once more, to obtain
      $
        (tilde(phi),tilde(psi))_G
        &=|G|^(-1)sum_(i=1)^t |G:C_S lr((s_i))|phi(s_i)psi(s_i^(-1)) \
        &=|S|^(-1)sum_(i=1)^t |S:C_S lr((s_i))|phi(s_i)psi(s_i^(-1))
        =(phi,psi)_S,
      $
      as required.
    ] <case:normal-complement-lift-isometry>],
    [#case[
      We can now complete the proof. Suppose $phi in Irr S$. Then
      $tilde(phi) in "ch" K G$ by
      @case:normal-complement-virtual-character-lift, and
      $(tilde(phi),tilde(phi))_G=(phi,phi)_S=1$ by
      @case:normal-complement-lift-isometry. Therefore
      $plus.minus tilde(phi) in Irr G$, and since $tilde(phi)(1)>0$, we have
      $tilde(phi) in Irr G$ for all $phi in Irr S$. Now define
      $ N=inter.big_(phi in Irr S) ker tilde(phi). $
      Then $N ⊴ G$. If $s in S inter N$, then for all $phi in Irr S$ we have
      $phi(s)=tilde(phi)(s)=tilde(phi)(1)=phi(1)$, so $s=1$ by
      Exercise~@exc:irreducible-character-kernel-intersection. Moreover, let $p$
      be any prime which divides $|G|$ but not $|S|$, and let $P$ be a Sylow
      $p$-subgroup of $G$. Then for all $phi in Irr S$ and all $u in P$ we have
      $ tilde(phi)(u)=tilde(phi)(1)=phi(1), $
      since $u_Pi=1$. Therefore $u in ker tilde(phi)$, and hence $P<=N$. It
      follows that $G=N times.r S$, completing the proof.
    ] <case:normal-complement-kernel>],
  )
]

As a corollary, we give a second proof of Burnside's Transfer
Theorem~@th:burnside-normal-p-complement.

#source(417)
#corollary[
  Let $S$ be a Sylow $p$-subgroup of a finite group $G$, such that $S$ is
  contained in the center of its normalizer. Then $G$ has a normal
  $p$-complement.
] <cor:burnside-normal-p-complement>
#idx("Burnside's Transfer Theorem", target: [@cor:burnside-normal-p-complement])
#proof[
  If $H<=G$ is a $p$-group, then $H$ is conjugate to a subgroup of $S$, by the
  Sylow Theorems, so hypothesis~(ii) of @th:hall-subgroup-normal-complement is
  satisfied. In order to verify hypothesis~(i), we must show that if $s$ and $t$
  are elements of $S$ which are conjugate in $G$, then they are conjugate in $S$
  (and hence equal, because $S$ is abelian). We have $s=t^x$ for some $x in G$.
  Since $S$ is abelian, we obtain $S<=C_G lr((s))$, and
  $S^x<=C_G lr((t^x))=C_G lr((s))$. By Sylow's Theorem, applied to
  $C_G lr((s))$, we have $S^(x z)=S$ for some $z in C_G lr((s))$. Then
  $x z in N_G lr((S))$, and by the hypothesis of the corollary, we have
  $ t=t^(x z)=s^z=s, $
  completing the proof of~(i). The corollary now follows from
  @th:hall-subgroup-normal-complement.
]

=== A Converse to Brauer's Theorem <ss:converse-brauer-induction>

In @th:brauer-elementary-character-ideal we proved that $v(cal(E),G)="ch"(K G)$,
where $cal(E)={H_i}_(i in I)$ is the set of elementary subgroups of $G$. This
equality means that
$ "ch"(K G)=sum_(i in I) {"ch"(K H_i)}^G, $ <eq:brauer-character-ring-induction>
where ${"ch"(K H_i)}^G$ is the set of all virtual characters of $G$ of the form
$phi^G$, with $phi in "ch"(K H_i)$. We shall prove a theorem of
Green~@bib:Green1955a, which asserts that for any family of subgroups
$cal(F)={F_j}_(j in J)$ such that $"ch"(K G)=sum_j {"ch"(K F_j)}^G$, each
elementary subgroup of $G$ is contained in some conjugate of some subgroup
$F_j$. Thus the family of elementary subgroups is, in this sense, the smallest
family for which @eq:brauer-character-ring-induction holds.

#lemma[
  Let $R=ZZ[omega]$, where $omega$ is a primitive $|G|$-th root of~1, and let
  $p$ be prime. Consider the $p$-elementary group $chevron.l x chevron.r P$,
  where $x$ is a $p'$-element of $G$ and $P$ a Sylow $p$-subgroup of
  $C_G lr((x))$. Let $H$ be a subgroup of $G$ which does not contain any
  conjugate of $chevron.l x chevron.r P$, and let $psi in "ch"(K H)$ have values
  in $R$. Then
  $ psi^G lr((x)) in p R. $
] <lem:elementary-subgroup-induced-value-divisibility>
#proof[
  Let $frak(C)$ be the conjugacy class of $G$ containing $x$. From
  Exercise~@exc:induced-character-centralizer, we have
  $ psi^G lr((x))=frac(|C_G lr((x))|, |H|)sum_(y in frak(C) inter H) psi(y). $
  Let ${frak(D)_1,dots,frak(D)_t}$ be the distinct $H$-conjugacy classes
  contained in $frak(C) inter H$ (this
  #source(418)
  intersection may be empty!), and let $h_i in frak(D)_i$, $1<=i<=t$. The number
  of conjugates of $h_i$ in $H$ equals
  $ |frak(D)_i|=|H:H inter C_G lr((h_i))|. $
  Therefore
  $
    psi^G lr((x))=frac(|C_G lr((x))|, |H|)sum_(i=1)^t |frak(D)_i|psi(h_i)
    =sum_(i=1)^t a_i psi(h_i),
  $
  where
  $ a_i=|C_G lr((h_i))| slash |H inter C_G lr((h_i))|,1<=i<=t. $
  (We have used the fact that each $h_i$ is $G$-conjugate to $x$.) Thus each
  $a_i in ZZ$, and we need only show that $p$ divides each $a_i$.

  Suppose that $p divides.not a_i$ for some $i$, and let $x=h_i^z$, $z in G$.
  Since $p divides.not a_i$, $|C_G lr((h_i))|$ and $|H inter C_G lr((h_i))|$
  have the same $p$-part, so a Sylow $p$-subgroup $P_i$ of
  $H inter C_G lr((h_i))$ is also a Sylow $p$-subgroup of $C_G lr((h_i))$. We
  have $chevron.l h_i chevron.r P_i<=H$, and $h_i^z=x$,
  $chevron.l h_i chevron.r^z=chevron.l x chevron.r$; further, $P_i^z$ is a Sylow
  $p$-subgroup of $C_G lr((h_i))^z$, hence of $C_G lr((x))$. But $P$ is also a
  Sylow $p$-subgroup of $C_G lr((x))$, hence is conjugate to $P_i^z$ in
  $C_G lr((x))$. Therefore $chevron.l x chevron.r P_i^z$ and
  $chevron.l x chevron.r P$ are conjugate. But
  $ {chevron.l h_i chevron.r P_i}^z=chevron.l x chevron.r P_i^z, $
  so $H$ contains a conjugate of $chevron.l x chevron.r P$. This is contrary to
  our hypotheses, and so each $a_i$ is a multiple of $p$. Hence
  $psi^G lr((x)) in p R$, as claimed.
]

#theorem(title: [Green])[
  Let $cal(F)$ be a family of subgroups of $G$ such that
  $v(cal(F),G)="ch"(K G)$. Then each elementary subgroup of $G$ is contained in
  some conjugate of some subgroup belonging to $cal(F)$.
] <th:green-elementary-subgroups-necessary>
#idx("Green's Theorem", target: [@th:green-elementary-subgroups-necessary])
#proof[
  Let $chevron.l x chevron.r P$ be a $p$-elementary subgroup of $G$, for a
  $p'$-element $x$ and a $p$-group $P$. If $chevron.l x chevron.r P$ is
  contained in no conjugate of a subgroup belonging to $cal(F)$, then the
  preceding lemma implies that $phi(x) in p R$ for all $phi in v(cal(F),G)$. In
  particular, this would imply $1_G lr((x)) in p R$, which is impossible, and
  the theorem is proved.
]

For further reading, see Lorenz~@bib:Lorenz1975.

=== The Aramata-Brauer Induction Theorem <ss:aramata-brauer-induction>

We prove next the Aramata-Brauer Theorem, discovered originally by
Aramata~@bib:Aramata1931, @bib:Aramata1933, and proved independently at a later
date by Brauer~@bib:Brauer1947a. Both authors used this theorem to prove that if
$E$ is a finite Galois extension
#source(419)
of an algebraic number field $K$, then the Dedekind zeta function
$zeta_K lr((s))$ is a divisor of $zeta_E lr((s))$. Using this result, together
with earlier work by Landau and Siegel, Brauer obtained the following remarkable
consequence:

#quote(block: true)[_Let $K$ range over all algebraic number fields of a fixed
degree $n$. Let $d$ be the discriminant of $K$ (over $QQ$), $h$ the ideal class
number of $K$, and $R$ the regulator of $K$. Then as $|d| -> infinity$,
$ log h R tilde.op frac(1, 2)log|d|. $_]

Let us now prove the Aramata-Brauer Theorem. We shall use the notation in
@def:character-table-data, and work throughout with complex characters.

#theorem[
  Let $G$ be a finite group of order $n$, where $n>1$, and let $rho$ be the
  regular character of $G$. Then there exist nontrivial linear characters
  $omega_i$ of cyclic subgroups of $G$, such that
  $ rho-1=sum_i a_i lr((omega_i))^G $
  with each $a_i$ a positive rational number with denominator $n$.
] <th:aramata-brauer-induction>
#idx("Aramata-Brauer Theorem", target: [@th:aramata-brauer-induction])
#idx("Brauer's Theorem", target: [@th:aramata-brauer-induction])
#idx(
  "Induction Theorems",
  "Aramata-Brauer",
  target: [@th:aramata-brauer-induction],
)

#remark(numbered: false)[
  Artin's Theorem~@th:artin-induction-explicit-coefficients guarantees that
  $rho-1$ is expressible as above with rational coefficients ${a_i}$. The
  significance of the present theorem is the fact that these ${a_i}$ may be
  chosen positive.
]

#proof[
  Let $C$ be a nontrivial cyclic subgroup of $G$ of order $m$, and let $x$ range
  over all $phi(m)$ generators of $C$. Put $Irr(C)={psi^1,dots,psi^m}$, where
  $psi^1=1$, and define
  $ u_i=phi(m)-sum_x psi^i lr((x)),1<=i<=m. $
  Let us write $C=chevron.l c chevron.r$, $psi^i lr((c))=omega=m$-th root of~1.
  Then $x=c^r$, where $r$ ranges between~1 and $m$, and $(r,m)=1$. We have
  $psi^i lr((x))=omega^r$, so $sum_x psi^i lr((x))$ is unchanged by all
  automorphisms of $QQ(omega)$ over $QQ$. Thus each $u_i in QQ$, and since $u_i$
  is an algebraic integer, we have $u_i in ZZ$. Further, $|psi^i lr((x))|=1$ for
  each $x$, so $u_i>0$ for $i!=1$. Clearly $u_1=0$. We obtain at once from the
  orthogonality relations, for $y in C$,
  $
    sum_(i=1)^m u_i overline(psi^i lr((y)))=cases(
      m phi(m) & quad "for" y=1,
      0 & quad "for" y!=1 "and" C!=chevron.l y chevron.r,
      -m & quad "if" C=chevron.l y chevron.r.
    )
  $
  Taking complex conjugates, we obtain exactly the same formulas for
  $sum u_i psi^i lr((y))$.

  #source(420)
  Now let $Irr(G)={zeta^1,dots,zeta^s}$, $zeta^1=1$, $z_i=zeta^i lr((1))$, so
  $rho-1=sum_(i>1) z_i zeta^i$. By §@ss:finite-group-character-orthogonality we
  have for each $i$,
  $
    zeta^i|_C=sum_(j=1)^m h_(i j)psi^j,
    "where" h_(i j)=(psi^j,zeta^i)_C "for" 1<=j<=m.
  $
  The ${h_(i j)}$ are nonnegative integers, and $h_(i j)$ is the multiplicity of
  $psi^j$ in $zeta^i|_C$. By Frobenius Reciprocity, we obtain
  $
    (psi^j)^G=sum_(i=1)^s h_(i j)zeta^i
    =sum_(i=1)^s (psi^j,zeta^i)_C zeta^i.
  $
  For each $C$ as above, set
  $
    S(C) & =sum_(j=1)^m u_j lr((psi^j))^G
           =sum_(i,j) u_j lr((psi^j,zeta^i))_C zeta^i \
         & =sum_i (sum_j u_j psi^j,zeta^i)_C zeta^i.
  $
  Since the values of $sum_j u_j psi^j$ on $C$ have already been calculated
  above, we find easily that
  $ S(C)=sum_(i=2)^s {z_i phi(m)-sum_x zeta^i lr((x))}zeta^i, $
  where $x$ ranges over all generators of $C$.

  We sum the above equality over all nontrivial cyclic subgroups $C$ of $G$.
  Then $x$ ranges over $G-{1}$, so
  $ sum_C sum_x zeta^i lr((x))=-zeta^i lr((1))=-z_i. $
  Further, $sum_C phi(m)=n-1$, and therefore we obtain
  $
    sum_C S(C)=sum_(i=2)^s {z_i lr((n-1))+z_i}zeta^i
    =sum_(i=2)^s n z_i zeta^i=n(rho-1).
  $
  Therefore
  $ rho-1=n^(-1)sum_C S(C)=sum_C sum_j (u_j slash n)(psi^j)^G. $
  This gives the desired result, since for each $C$, the coefficient
  $u_1 slash n$ of $(psi^1)^G$ is zero.
]

#source(421)
#exercises-heading

#exercise[
  Let $H=C times P$ be a $p$-elementary group, where $C$ is a cyclic $p'$-group,
  and $P$ a $p$-group. Prove that $H$ is nilpotent, and that each subgroup of
  $H$ is $p$-elementary. Prove also that $C$ is the set of all $p'$-elements in
  $H$, and that $P$ is the set of all $p$-elements in $H$.
] <exc:elementary-subgroups-primary-parts>

#exercise[
  Prove that subgroups of hyper-elementary groups are hyper-elementary.
] <exc:hyper-elementary-subgroups>

#exercise[
  Let $M$ be a $QQ G$-module, with character $mu$. Let $x,y in G$, and assume
  $chevron.l x chevron.r=_G chevron.l y chevron.r$. Prove that $mu(x)=mu(y)$.
  (See @eq:character-galois-power-values.)
  #hint([@exc:rational-character-conjugate-cyclic-subgroups])[
    Since $mu$ is a class function, we may assume that
    $chevron.l x chevron.r=chevron.l y chevron.r$. Then $y=x^a$, for some
    integer $a$ relatively prime to $n$, where $n$ is the order of $x$. Let
    ${xi_i}$ be the eigenvalues of $upright(bold(M))(x)$; then each ${xi_i}$ is
    an $n$-th root of~1, and we have
    $ mu(x)=sum xi_i,mu(y)=sum xi_i^a. $
    Let $omega$ be a primitive $n$-th root of~1. Show that there exists a
    $QQ$-automorphism $sigma$ of the field $QQ(omega)$ such that
    $sigma(omega)=omega^a$, and deduce that $sigma(mu(x))=mu(y)$. See also
    §@sec:induction-arbitrary-fields.
  ]
] <exc:rational-character-conjugate-cyclic-subgroups>

#exercise[
  Let ${C_1,dots,C_m}$ be a full set of non-conjugate cyclic subgroups of a
  finite group $G$. From the Artin Induction Theorem, it follows that every
  rational character $phi$ of $G$ can be expressed in the form
  $ phi=sum_(i=1)^m frac(a_i, |G|)(1_(C_i))^G,a_i in ZZ. $
  Prove that the number of isomorphism classes of simple $QQ G$-modules is $m$.
  #hint([@exc:rational-simple-modules-cyclic-subgroups])[
    Use Exercise~@exc:rational-character-conjugate-cyclic-subgroups to show that
    each rational character $mu$ is determined by its values on generators of
    $C_1,dots,C_m$, so there are at most $m$ non-isomorphic simple
    $QQ G$-modules. On the other hand, for each cyclic subgroup $C$ of $G$, let
    $ t_C=sum_(C'<=C) frac(1, |C:C'|)mu(|C:C'|)(1_(C'))^C. $
    Using the proof of Artin's Theorem, show that for each $x in C$,
    $
      t_C lr((x))=cases(1 & quad C=chevron.l x chevron.r, 0 & quad "otherwise").
    $
    Then show that ${t_(C_1)^G,dots,t_(C_m)^G}$ are linearly independent. (See
    also Theorem~@th:field-character-conjugacy-classes.)
  ]
] <exc:rational-simple-modules-cyclic-subgroups>

#exercise[
  Let $P(G)$ be the set of $ZZ$-linear combinations of induced characters
  ${1_H^G:H<=G}$. As in §@ss:character-rings-brauer-induction, let $P(cal(H),G)$
  be the set of $ZZ$-linear combinations of induced characters
  ${1_H^G:H in cal(H)}$, where $cal(H)$ is the family of hyper-elementary
  groups. Prove that $P(G)$ is a ring under pointwise addition and
  multiplication. Then prove that $P(G)=P(cal(H),G)$.
  #hint([@exc:solomon-permutation-character-ring])[
    First prove that $P(cal(H),G)$ is an ideal in $P(G)$, and then use
    @th:solomon-permutation-induction.
  ]
] <exc:solomon-permutation-character-ring>

#source(422)
#exercise[
  Let $A$ be any f.d. semisimple $K$-algebra, let $E$ be an extension field of
  $K$, and suppose that
  $ V plus.o X^E tilde.equiv Y^E, $
  where $V$ is an $A^E$-module, and $X,Y$ are $A$-modules finite-dimensional
  over $K$. Show that $V tilde.equiv W^E$ for some $A$-module $W$.
  #hint([@exc:semisimple-scalar-extension-complement])[
    Write $X=X_0 plus.o U$, $Y=Y_0 plus.o U$, where $X_0$ and $Y_0$ have no
    common direct summand. Then
    $ V plus.o X_0^E tilde.equiv Y_0^E,"and" Hom_A lr((Y_0,X_0))=0. $
    Therefore $Hom(Y_0^E, X_0^E)=0$, so $V tilde.equiv Y_0^E$.
  ]
] <exc:semisimple-scalar-extension-complement>

#exercise[
  Keeping the above notation, with $X$ and $Y$ finite-dimensional over $K$,
  assume that $dim_K E$ is finite, but drop the hypothesis that $A$ be
  semisimple. Prove the result in this case.
  #hint([@exc:finite-field-extension-complement-descent])[
    We now have $V plus.o X_0^E tilde.equiv Y_0^E$, where $X_0$ and $Y_0$ have
    no common indecomposable direct summand. If $dim_K E=n$, then
    $ V|_A plus.o X_0^((n)) tilde.equiv Y_0^((n)) $
    which contradicts the K-S-A Theorem unless $X_0=0$.
  ]
] <exc:finite-field-extension-complement-descent>
