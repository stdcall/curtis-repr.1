#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/34-examples-integral-representations.typ": *

== Examples of Integral Representations <sec:examples-integral-representations>

Throughout this section, $Lambda$ denotes an $R$-order in a f.d. separable
$K$-algebra $A$, where $R$ is a Dedekind domain with quotient field $K$. In
@sec:extensions-lattices, we showed how arbitrary $Lambda$-lattices could be
built up as extensions of simpler lattices. In practice, this technique has
yielded many of the results so far obtained about integral representations of
specific groups and orders. This section is devoted to detailed investigations
of a number of special cases.

In @ss:lattice-extension-isomorphism, we show that for a given central
idempotent $e$, each $Lambda$-lattice $M$ can be represented as an extension
$xi$ of a lattice $N$ on which $e$ acts as $1$, by a lattice $L$ on which $e$
acts as $0$. The lattice $M$ is determined up to isomorphism by the isomorphism
classes of $N$ and $L$ and by the orbit of $xi$ in $"Ext"(N,L)$ under the
actions of $Aut N$ and $Aut L$. We show further that, under suitable hypotheses,
these orbits depend only on the genera of $N$ and $L$.

This machinery is applied in @ss:cyclic-p-group-lattices to a discussion of
integral representations of cyclic $p$-groups. Of course, a complete
classification of such representations cannot be expected for cyclic groups $G$
of order $p^k$, $k>=3$, since by Dade's Theorem, $ZZ G$ is of infinite
representation type (see @cor:p-group-infinite-integral-representation-type).
The special case $k=2$ is considered in @ss:cyclic-p-squared-lattices, and here
we obtain a complete list of indecomposable $ZZ G$-lattices.

In @ss:matrix-order-drozd-turcin, we give the Drozd–Turčin example of a
$Lambda$-lattice $M$ whose genus contains more isomorphism classes than does the
genus of $Lambda$ itself.

Finally, in @ss:dihedral-metacyclic-integral-representations, we consider
representations of certain metacyclic and dihedral groups. Here, the results in
@sec:twisted-group-rings on twisted group rings play a
#source(734)
fundamental role, and permit a fairly complete classification of all
indecomposable integral representations of such groups.

=== Extensions of Lattices <ss:lattice-extension-isomorphism>

We shall now consider in more detail the problem of classifying
$Lambda$-lattices by means of extensions, and we shall use the earlier results
of @sec:extensions-lattices freely. Let $M$ be a full $Lambda$-lattice in a f.g.
left $A$-module $V$. Given a submodule $W$ of $V$, we obtain an exact sequence
of $Lambda$-lattices
$ 0->L->M->N->0, quad L=M inter W, quad N=M slash L. $
In particular, let $e$ be a central idempotent of $A$, and let $W=(1-e)V$. Then
the sublattice
$ L={m in M:e m=0} $
is a _characteristic sublattice_ of $M$ (that is, $phi(L) subset.eq L$ for every
$phi in "End"_Lambda M$).#idx("characteristic sublattice") If we put
$
  Lambda_1=Lambda slash (Lambda inter A e), quad
  Lambda_2=Lambda slash (Lambda inter A(1-e)),
$
<eq:central-idempotent-quotient-orders>
then $L$ is a $Lambda_1$-lattice and $N$ is a $Lambda_2$-lattice. Note that
$Lambda_1$ is an $R$-order in the $K$-algebra $A slash A e$, and $Lambda_2$ in
$A slash A(1-e)$. Thus, to find all $Lambda$-lattices $M$, we first classify all
$Lambda_i$-lattices ($i=1,2$), and then find all extensions of a
$Lambda_2$-lattice by a $Lambda_1$-lattice. We remark that in our case,
$Hom_Lambda (L,N)=0$ since $e$ acts as $0$ on $L$ and as $1$ on $N$.

The purpose of the above procedure is to analyze a $Lambda$-lattice $M$, such
that $K M$ involves more than one type of simple $A$-module, as an extension of
$Lambda$-lattices corresponding to single types of simple $A$-modules. In our
first example below, this procedure is carried out in a somewhat disguised form.

#example[
  Let $G=chevron.l x:x^n=1 chevron.r$, $Lambda=R G$, where $char R=0$. We
  identify $Lambda$ with $R[x] slash (x^n-1)$. Suppose that $x^n-1=f(x)g(x)$ in
  $R[x]$. Given a $Lambda$-lattice $M$, put
  $
    L={m in M:f(x)m=0}, quad Lambda_1=R[x] slash (f(x)), quad
    Lambda_2=R[x] slash (g(x)).
  $
  Then $Lambda_1$ and $Lambda_2$ are $R$-orders, $L$ is a $Lambda_1$-lattice,
  and $M slash L$ is a $Lambda_2$-lattice. As above, $Hom_Lambda (L,N)=0$.

  Let us explain how this example fits into the general procedure described
  above. The point here is that $K[x] slash (x^n-1)$ is a separable $K$-algebra,
  so for any factorization $x^n-1=f(x)g(x)$ in $R[x]$, the quotients
  $K[x] slash (f(x))$ and $K[x] slash (g(x))$ correspond to complementary
  Wedderburn components of $K[x] slash (x^n-1)$, and hence to central
  idempotents $e$ and $1-e$, as above.
] <exm:cyclic-factorization-extensions>

#source(735)
Our next example, which will also be needed later, is of a somewhat different
nature.

#example[
  Let $Lambda'=M_2(ZZ)$, $A=M_2(QQ)$, $bold(I)=mat(1, 0; 0, 1)$, and let
  $overline(ZZ)=ZZ slash p ZZ$, where $p$ is a rational prime. Setting
  $ Lambda=ZZ dot bold(I)+p Lambda', $
  we see that $Lambda$ is a $ZZ$-order in $A$, and
  $p Lambda' subset Lambda subset Lambda'$. Given a $Lambda$-lattice $M$, let
  $ M_0=p Lambda' dot M subset M, $
  so $M_0$ is a $Lambda$-sublattice of $M$. For each $phi in "End"_Lambda M$, we
  have
  $ phi(M_0)=phi(p Lambda' dot M)=p Lambda' phi(M) subset.eq M_0, $
  so $M_0$ is a characteristic sublattice of $M$. Then
  $ N=M slash M_0=M slash p Lambda' M $
  is a $(Lambda slash p Lambda')$-module, but of course $N$ is not a lattice in
  this case. Next,
  $
    Lambda slash p Lambda'=(ZZ dot bold(I)+p Lambda') slash p Lambda'
    tilde.equiv ZZ slash p ZZ=overline(ZZ),
  $
  so $N$ is a vector space over $overline(ZZ)$.

  Now $M_0$ is a lattice over the maximal order $Lambda'$. Setting
  $ L={vec(a, b):a,b in ZZ}, $
  we see that $L$ is a left $Lambda'$-lattice, and $QQ L$ is a simple left
  $A$-module. Let us show that $M_0 tilde.equiv L^((r))$ for some $r$. If $L'$
  is any left $Lambda'$-lattice in $QQ L$, then $L'$ is in the same genus as $L$
  by @th:dvr-maximal-orders-completion-lattices, and therefore
  $L' tilde.equiv L$ by @th:absolutely-simple-genus-class-number. (The same
  conclusion can also be obtained from the discussion following the proof of
  @prop:field-representation-integral-form.) Finally, we use
  @th:maximal-orders-are-hereditary to conclude from the above that
  $M_0 tilde.equiv L^((r))$ for some $r$. Further,
  $N tilde.equiv overline(ZZ)^((s))$ for some $s$, and there is a $Lambda$-exact
  sequence
  $ 0->L^((r))->M->overline(ZZ)^((s))->0, $
  in which $L^((r))$ is characteristic in $M$. To find all $M$'s, we must
  therefore classify all extensions of $overline(ZZ)^((s))$ by $L^((r))$. We
  shall return to this problem in @ss:matrix-order-drozd-turcin.
] <exm:matrix-order-characteristic-sublattice>

Now let $L$ and $N$ be arbitrary $Lambda$-lattices, and let $M$ be an extension
of $N$ by $L$, corresponding to an element $xi in "Ext"_Lambda^1(N,L)$. We
indicate this fact by writing an exact sequence
#named-equation(name: [$(xi)$])[$ 0->L->M->N->0, $]
<eq:lattice-extension-sequence>
#source(736)
and using the notation #equation-suffix(
  base: [@exm:matrix-order-characteristic-sublattice],
)[
  $ M=(N,L;xi). $
] <eq:lattice-extension-notation>
Of course, $xi$ determines a family of mutually isomorphic extensions.

We shall now consider the problem as to when two extensions of $N$ by $L$ are
isomorphic. Each $xi in "Ext"_Lambda^1 (N,L)$ determines a family of mutually
isomorphic extensions. It often happens, however, that two different extension
classes $xi$, $xi'$ will yield isomorphic extensions. The following useful
result is due to Heller–Reiner~@bib:Heller1962\:

#proposition[
  Let $L$, $L'$, $N$ and $N'$ be $Lambda$-lattices such that
  $Hom_Lambda (L,N')=Hom_Lambda (L',N)=0$. Let $xi in "Ext"_Lambda^1 (N,L)$
  determine a $Lambda$-lattice $M$ as an extension of $N$ by $L$, and let
  $xi' in "Ext"_Lambda^1 (N',L')$ determine $M'$. Then $M tilde.equiv M'$ if and
  only if: #equation-suffix(base: [@prop:lattice-extension-isomorphism])[
    $
      lambda xi=xi' nu "in" "Ext"_Lambda^1 (N,L') "for some isomorphisms"
      lambda:L tilde.equiv L', nu:N tilde.equiv N'.
    $
  ] <eq:lattice-extension-isomorphism-condition>
] <prop:lattice-extension-isomorphism>
#proof[
  For convenience, write $"Ext"$ and $Hom$ in place of $"Ext"_Lambda^1$ and
  $Hom_Lambda$. Given any isomorphism $phi:M tilde.equiv M'$, consider the
  diagram
  #extension-isomorphism-initial()
  with exact rows, and where $alpha$, $alpha'$ are viewed as inclusions. Since
  $beta' phi alpha in Hom(L, N')=0$, it follows that $phi$ induces
  $Lambda$-homomorphisms $lambda:L->L'$ and $nu:N->N'$, and one obtains a
  commutative diagram. Likewise, $phi^(-1)$ induces maps $lambda':L'->L$ and
  $nu':N'->N$. Since $phi^(-1)phi=1$, we have $lambda'lambda=1$, $nu'nu=1$.
  Analogously we obtain $lambda lambda'=1$, $nu nu'=1$, so $lambda$ and $nu$ are
  isomorphisms. Conversely, given a commutative diagram in which $lambda$ and
  $nu$ are isomorphisms, the map $phi$ is also an isomorphism.

  Suppose now that we have a commutative diagram $(lambda,phi,nu):(xi)->(xi')$.
  By Exercise~@exc:map-factorization-pushout-pullback, there exists a
  commutative diagram with exact rows:
  #extension-isomorphism-factorization()
  #source(737)
  Here, $M_1$ is the pushout of the pair of maps ${alpha,lambda}$, and $M_2$ is
  the pullback of the pair ${beta',nu}$. Since $Hom(L, L')$ acts from the left
  on $"Ext"(N,L)$, and $Hom(N, N')$ acts from the right, the discussion in
  @ss:ext-tor shows that
  $ eta_1=lambda xi, quad eta_2=xi' nu. $
  But the extensions $(eta_1)$, $(eta_2)$ are equivalent, so $eta_1=eta_2$ in
  $"Ext"(N,L')$ and @eq:lattice-extension-isomorphism-condition is established.

  Conversely, if @eq:lattice-extension-isomorphism-condition holds, define
  $eta_1=lambda xi$, $eta_2=xi'nu$, as above. Then the extensions $(eta_1)$ and
  $(eta_2)$ are equivalent, so there exists a map $M_1->M_2$ making the above
  diagram commutative. Composition of maps then yields the desired isomorphism
  $M tilde.equiv M'$, which completes the proof of the proposition.
]

#corollary[
  Let $L$ and $N$ be arbitrary $Lambda$-lattices such that $Hom_Lambda (L,N)=0$,
  and let $M_1$ and $M_2$ be a pair of extensions of $N$ by $L$, corresponding
  to elements $xi_1,xi_2 in "Ext"_Lambda^1 (N,L)$, respectively. Then
  $M_1 tilde.equiv M_2$ if and only if
  $
    lambda xi_1=xi_2 nu "in" "Ext"_Lambda^1 (N,L)
    "for some" lambda in Aut L, nu in Aut N.
  $
  <eq:lattice-extension-automorphism-orbits>
  In other words, the isomorphism classes of extensions of $N$ by $L$ are in
  bijection with the orbits of $"Ext"_Lambda^1 (N,L)$ under the action of
  $(Aut L) times (Aut N)$.
] <cor:extension-isomorphism-automorphism-orbits>

#remark(numbered: true)[
  One procedure for classifying $Lambda$-lattices $M$ is now as follows. Let
  $e in A$ be a central idempotent, and express $M$ as an extension of a
  $Lambda_2$-lattice $N$ by a $Lambda_1$-lattice $L$, using the notation of
  @eq:central-idempotent-quotient-orders. Then $Hom(L, N)=0$, and likewise if
  $M'$ is an extension of $N'$ by $L'$, then also $Hom(L, N')=0$. The hypotheses
  of Proposition~@prop:lattice-extension-isomorphism and its corollary are then
  satisfied, so $M$ determines $L$ and $N$ up to isomorphism. The preceding
  discussion shows that a full set of isomorphism invariants of $M$ consists of:
  #enum(numbering: "(i)", [The isomorphism classes of $L$ and $N$, and], [The
    orbit of the element $(xi)$ in $"Ext"_Lambda^1(N,L)$ under the actions of
    $Aut_Lambda L$ and $Aut_Lambda N$, where $(xi)$ is the class of the
    extension $M$ of $N$ by $L$.])
] <rem:lattice-extension-classification>

Now let $L$ and $N$ be arbitrary $Lambda$-lattices, not necessarily related to
some idempotent $e in A$ as above. As in @sec:genus, we write $L' or.curly L$ to
indicate that the $Lambda$-lattice $L'$ is in the genus $Gamma_L$ of $L$. By
@prop:extension-localization-nonmaximal-primes and
@prop:genus-nonmaximal-primes, there exists an $R$-isomorphism
$
  "Ext"_Lambda^1 (N',L') tilde.equiv "Ext"_Lambda^1 (N,L)
  "for" N' or.curly N, L' or.curly L.
$
It seems reasonable to expect that there should be a bijection between the set
of $(Aut L,Aut N)$-orbits of $"Ext"(N,L)$, and the $(Aut L',Aut N')$-orbits of
$"Ext"(N',L')$. The remainder of this subsection is devoted to establishing this
result under suitable hypotheses. The result is quite useful in later
calculations (see @ss:cyclic-p-group-lattices, @ss:cyclic-p-squared-lattices).

#source(738)
As in @eq:nonmaximal-order-primes, let $S(Lambda)$ denote the set of all maximal
ideals $P$ in $R$ for which the localization $Lambda_P$ is not a maximal order.
If $Lambda$ is a maximal order, then $S(Lambda)=emptyset$, and to avoid
distinguishing this case from the case where $S(Lambda)$ is non-empty, we pick
any maximal ideal $P_0$ of $R$, and define
$
  S_0=cases(
    S(Lambda) & "if" S(Lambda)!=emptyset,
    {P_0} & "if" S(Lambda)=emptyset
  ).
$
<eq:extension-standard-prime-set>
By Roiter's Lemma~@lem:roiter-genus, there exist $Lambda$-exact sequences
$ 0->L arrow.r^f L'->T->0, quad 0->N' arrow.r^g N->U->0, $
where $T$ and $U$ are $R$-torsion $Lambda$-modules such that $T_P=0$ and $U_P=0$
for all $P in S_0$. As we shall see in a moment, the pair $(f,g)$ determines an
$R$-isomorphism
$ t:"Ext"(N,L) tilde.equiv "Ext"(N',L'), $
<eq:standard-extension-isomorphism>
where $"Ext"$ means $"Ext"_Lambda^1$. We shall call $t$ the _standard
isomorphism_ associated with the pair $(f,g)$.#idx("standard isomorphism")

We proceed to describe $t$ explicitly, using the discussion in @ss:ext-tor.
Suppose that $xi in "Ext"(N,L)$ determines a $Lambda$-lattice $M$, so there is
an exact sequence
#named-equation(name: [$(xi)$])[$ 0->L arrow.r^alpha M->N->0. $]
<eq:standard-extension-original-sequence>
Then define $f xi in "Ext"(N,L')$ by the commutative diagram
#extension-standard-pushout()
where $M_0$ is the pushout of the pair of maps ${alpha,f}$. Then
$t(xi)=(f xi)g$, where $(f xi)g$ is defined by the commutative diagram
#extension-standard-pullback()
in which $M'$ is the pullback of the pair ${beta,g}$.

For each $P in S_0$, both $f_P$ and $g_P$ are isomorphisms, and therefore so is
$t_P$. It follows at once from @prop:extension-localization-nonmaximal-primes
that $t$ is an isomorphism, and @eq:standard-extension-isomorphism is
established.
#source(739)
Furthermore, we have $M' or.curly M$ since $(M')_P tilde.equiv M_P$ for each
$P in S_0$. We caution the reader that it is usually possible to find other
isomorphisms of $"Ext"$'s which need not arise from “change of variable” maps.
Nevertheless, we have:

#lemma[
  The inverse of a standard isomorphism is also a standard isomorphism.
] <lem:standard-extension-isomorphism-inverse>
#proof[
  Choose a nonzero ideal $frak(a)$ of $R$, all of whose prime factors lie in
  $S_0$, such that $frak(a) dot "Ext"(N,L)=0$. Then for any $h in "End" N$ such
  that $h equiv 1 mod frak(a)$ (that is, $h-1 in frak(a) dot "End" N$), $h$
  induces the identity map on $"Ext"(N,L)$.

  Now let $t$ be a standard isomorphism as in
  @eq:standard-extension-isomorphism, associated with the pair $(f,g)$, where
  $f:L->L'$, $g:N'->N$. Since $f_P$ is an isomorphism for each $P in S_0$, we
  may form its inverse $f_P^(-1):(L')_P->L_P$ for each such $P$. Then choose
  $h in Hom(L', L)$ such that $h$ approximates $f_P^(-1)$ at each $P in S_0$.
  Specifically, we can choose $h$ so that
  $ h f equiv 1 mod frak(a) dot "End" L. $
  Since $ker h_P=0$ for $P in S_0$, it follows that $h$ is a monomorphism, and
  $h f$ acts as $1$ on $"Ext"(N,L)$. Likewise, there exists a monomorphism
  $j:N->N'$ such that $g j equiv 1 mod frak(a) dot "End" N$, and then $g j$ acts
  as $1$ on $"Ext"(N,L)$. The pair $(h,j)$ induces a standard isomorphism
  $ t':"Ext"(N',L') tilde.equiv "Ext"(N,L), $
  and clearly $t't=1$ on $"Ext"(N,L)$. But then $t'=t^(-1)$, and the lemma is
  proved.
]

Since each $xi in "Ext"(N,L)$ determines a class of equivalent extensions of $N$
by $L$, we obtain (see also Exercises~@exc:genus-exact-sequence-subobjects,
@exc:genus-exact-sequence-overobjects):

#corollary[
  Let $L' or.curly L$, $N' or.curly N$, and let
  $t:"Ext"(N,L) tilde.equiv "Ext"(N',L')$ be a standard isomorphism. Then $t$
  gives a bijection between the set of equivalence classes of extensions of $N$
  by $L$, and the corresponding set for $N'$, $L'$.
] <cor:standard-extension-equivalence-classes>

We have not shown above that there is a bijection between _isomorphism_ classes
of extensions. As we have seen in @rem:lattice-extension-classification, for
instance, a given isomorphism class may be a union of many equivalence classes.
To overcome this difficulty, we shall need to impose the extra hypothesis that
“cancellation” is possible in certain cases. Let us begin with:

#definition[
  We say that _cancellation is valid_ in the genus $Gamma$ of left
  $Lambda$-lattices if for all $L,M,N in Gamma$,
  $ L plus.o M tilde.equiv L plus.o N ==> M tilde.equiv N. $
  #idx("cancellation", target: [@def:genus-cancellation])
] <def:genus-cancellation>

#source(740)
As we shall see in Chapter~11 of Volume~II, cancellation is valid for most
cases, but not for all cases. In order to state Jacobinski's sufficiency
conditions for cancellation, some terminology is needed. Let $M in Gamma$, and
consider the $K$-algebra $B="End"_A K M$. We call $M$ an _Eichler lattice_ if
$B$ satisfies the _Eichler condition_ relative to $R$ (see @bib:Reiner1975[MO]
(38.1)).#idx(
  "Eichler lattice",
)#idx("Eichler condition") In the special case where $K$ is an algebraic number
field and $R="alg. int."{K}$, this condition means that no Wedderburn component
of $B$ is a totally definite quaternion algebra. (If $B$ is a central simple
$K$-algebra, we call $B$ a _totally definite quaternion algebra_ if each
infinite prime $P$ of $K$ is a real prime, and for each such $P$, the $P$-adic
completion of $B$ is isomorphic to the algebra of real quaternions (see
Example~@exm:quaternion-group-algebra-reduced-norm)).#idx(
  "totally definite quaternion algebra",
) Thus, the $K$-algebra $B$ certainly satisfies the Eichler condition whenever
$B$ is a split semisimple algebra; the condition is also satisfied if $K$ has at
least one complex prime.

In Chapter~11 of Volume~II, we shall prove the deep result:

#theorem(name: "Jacobinski Cancellation Theorem")[
  Let $K$ be a global field, and let $M$ be an Eichler $Lambda$-lattice. Then
  cancellation is valid in the genus $Gamma_M$ of $M$. #idx(
    "Jacobinski's Cancellation Theorem",
    target: [@th:jacobinski-genus-cancellation],
  )#idx("cancellation", target: [@th:jacobinski-genus-cancellation])
] <th:jacobinski-genus-cancellation>

We are now ready to resume our discussion of extensions of lattices. Using the
theorem above, we now establish:

#theorem(title: [Reiner~@bib:Reiner1978])[
  Let $L$ and $N$ be left $Lambda$-lattices such that $L plus.o N$ is an Eichler
  lattice, and let $L' or.curly L$, $N' or.curly N$. Let
  $t:"Ext"(N,L) tilde.equiv "Ext"(N',L')$ be a standard isomorphism as in
  @eq:standard-extension-isomorphism. Then $t$ induces a bijection between the
  set of isomorphism classes of extensions of $N$ by $L$, and the set of
  isomorphism classes of extensions of $N'$ by $L'$.
  #idx("Reiner's Theorem", target: [@th:standard-extension-isomorphism-classes])
] <th:standard-extension-isomorphism-classes>
#proof[
  Let $M$ be an extension of $N$ by $L$, corresponding to the element
  $xi in "Ext"(N,L)$; all $M$'s belonging to the same $xi$ are isomorphic to one
  another. Let $xi'=t(xi) in "Ext"(N',L')$, and let $xi'$ determine the
  $Lambda$-lattice $M'$ as an extension of $N'$ by $L'$; then#footnote[
    See the discussion which precedes
    @lem:standard-extension-isomorphism-inverse.
  ] $M' or.curly M$. Now let $xi_1 in "Ext"(N,L)$ determine the extension $M_1$,
  and let $t(xi_1)$ determine $M'_1$. We must prove that $M tilde.equiv M_1$ if
  and only if $M' tilde.equiv M'_1$.

  It suffices to prove the result in one direction, since by
  @lem:standard-extension-isomorphism-inverse, the inverse of a standard
  isomorphism is also standard. Furthermore, every standard isomorphism can be
  expressed as a product of two standard isomorphisms, each of which involves a
  change of only one of the “variables” $L$ and $N$. It is therefore sufficient
  to prove the result when there is a change in only one variable, say $L$.
  Thus, we start with an exact sequence
  $ 0->L arrow.r^f L'->T->0, quad "where" T_P=0 "for" P in S_0. $
  #source(741)
  Given any $xi in "Ext"(N,L)$, we have a commutative diagram with exact rows
  #extension-standard-change-kernel()
  so by the Snake Lemma we obtain an exact sequence
  $ 0->M->M'->"cok" f->0, quad "cok" f=L' slash f(L), $
  with $("cok" f)_P=0$ for $P in S_0$. If $xi_1 in "Ext"(N,L)$ gives rise to
  $M_1$, then in the same way we obtain another exact sequence
  $ 0->M_1->M'_1->"cok" f->0. $
  Comparing these two exact sequences and using @prop:genus-schanuel, we get
  $ M plus.o M'_1 tilde.equiv M_1 plus.o M' $
  (this is just the assertion in @eq:genus-exchange). But now $M or.curly M'$,
  $M_1 or.curly M'_1$. If $M tilde.equiv M_1$, then all of the lattices $M$,
  $M'$, $M_1$, $M'_1$ lie in the same genus. We have
  $K M tilde.equiv K(L plus.o N)$, and since $L plus.o N$ is an Eichler lattice
  by hypothesis, so is $M$. The Jacobinski Cancellation Theorem can now be
  applied, and we conclude that $M'_1 tilde.equiv M'$, as desired. This
  completes the proof.
]

It seems likely that the above theorem holds true without the hypothesis that
$L plus.o N$ be an Eichler lattice. In any case, we have the following
consequence of @cor:extension-isomorphism-automorphism-orbits and
@th:standard-extension-isomorphism-classes\:

#corollary[
  Let $L$ and $N$ be $Lambda$-lattices such that $Hom(L, N)=0$, and such that
  $L plus.o N$ is an Eichler lattice. Let $L' or.curly L$, $N' or.curly N$. Then
  each standard isomorphism $t:"Ext"(N,L) tilde.equiv "Ext"(N',L')$ gives a
  bijection between the set of orbits of $"Ext"(N,L)$ under the actions of
  $Aut L$ and $Aut N$, and the corresponding set of orbits for the pair $N'$,
  $L'$.
] <cor:standard-extension-automorphism-orbits>

=== Cyclic $p$-Groups <ss:cyclic-p-group-lattices>

We shall apply the machinery of @ss:lattice-extension-isomorphism to the problem
of classifying $Lambda$-lattices, where $Lambda$ is the integral group ring
$ZZ G$ of a cyclic group $G=chevron.l x chevron.r$ of order $p^kappa$, with $p$
prime and $kappa>=1$. A complete classification cannot be obtained for
$kappa>2$, so we shall give some partial results in this subsection, and then
use them in @ss:cyclic-p-squared-lattices to handle the case when $kappa=2$.

#source(742)
Throughout this subsection, we fix the following notation:
#table(
  columns: (auto, auto),
  stroke: none,
  [$R^dot$], [group of units of a ring $R$],
  [$Lambda_kappa=ZZ[x] slash (x^(p^kappa)-1)$], [],
  [$hat(QQ),hat(ZZ),"etc."$], [$p$-adic completions],
  [$Phi_i (x)$],
  [cyclotomic polynomial#footnote[
      See @bib:CurtisReiner1962[CR] (21.9) or
      Exercise~@exc:rational-cyclic-group-wedderburn.
    ] of order $p^i$ and degree $phi(p^i)$],

  [$Phi_i (x)=sum_(j=0)^(p-1)x^(j p^(i-1))$],
  [if $i>=1$,
    $Phi_0(x)=x-1$],

  [$omega_i$], [primitive $p^i$-th root of $1$ over $QQ$],
  [$K_i=QQ(omega_i)$],
  [$R_i="alg. int."{K_i}=ZZ[omega_i]
  tilde.equiv ZZ[x] slash (Phi_i (x))$],

  [$hat(K)_i=hat(QQ)(omega_i)$],
  [$hat(R)_i=hat(ZZ)[omega_i]
  tilde.equiv hat(ZZ)[x] slash (Phi_i (x))$],
)
In the above, $i$ ranges from $0$ to $kappa$. For $i>=1$, $P_i=(1-omega_i)R_i$
is the unique maximal ideal of $R_i$ containing $p$, and $p$ is completely
ramified in $K_i$. We have
$
  p R_i=P_i^(phi(p^i)), quad
  R_i slash P_i tilde.equiv ZZ slash p ZZ=overline(ZZ).
$
Further, the $P_i$-adic completion $hat(K)_i$ of $K_i$ coincides with its
$p$-adic completion, and $Phi_i (x)$ is irreducible in $ZZ[x]$ and in
$hat(ZZ)[x]$. The unique maximal ideal of $hat(R)_i$ is
$hat(P)_i=(1-omega_i)hat(R)_i$.

We identify $ZZ G$ with $Lambda_kappa$, and omit the subscript $kappa$ when
there is no danger of confusion. Since $G$ is a $p$-group, two $Lambda$-lattices
$M_1$ and $M_2$ lie in the same genus if and only if
$hat(M)_1 tilde.equiv hat(M)_2$.

#lemma[
  Let $M$ be a $Lambda$-lattice. Then $M$ is indecomposable if and only if
  $hat(M)$ is indecomposable.
] <lem:cyclic-p-lattice-completion-indecomposable>
#proof[
  By Exercise~@exc:rational-cyclic-group-wedderburn, we have
  $
    QQ G tilde.equiv QQ[x] slash (x^(p^kappa)-1)
    tilde.equiv product.co_(i=0)^kappa K_i, quad
    hat(QQ)G tilde.equiv product.co_(i=0)^kappa hat(K)_i.
  $
  Since the completion $hat(K)_i$ of $K_i$ is a field, each simple left
  $QQ G$-module remains simple under passage to the $p$-adic completion. It
  follows from Heller's
  #source(743)
  Theorem~@th:heller-completion-krull-schmidt that every $hat(Lambda)$-lattice
  is the completion of some $tilde(Lambda)$-lattice, where $tilde(Lambda)$ is
  the localization of $Lambda$ at $p$. But every $tilde(Lambda)$-lattice is the
  localization of some $Lambda$-lattice, by @prop:localized-module-finite-model.
  Therefore every $hat(Lambda)$-lattice is the completion of a $Lambda$-lattice.
  Hence if $hat(M)$ is decomposable, so is $M$, by
  @cor:genus-direct-sum-decomposition. This completes the proof.
]
(The proof of @th:krull-schmidt-odd-p-group-lattices shows that the result holds
for every $p$-group, not necessarily cyclic, when $p>2$.)

Now let $M$ be a $Lambda$-lattice, and set
$ L={m in M:(x^(p^(kappa-1))-1)m=0}. $
By @exm:cyclic-factorization-extensions, $L$ is a characteristic sublattice of
$M$, and there is an exact sequence of $Lambda$-lattices
$ 0->L->M->N->0, quad N=M slash L, $
in which $L$ is a $Lambda_(kappa-1)$-lattice, and $N$ is an $R_kappa$-lattice.
(Technically, $N$ is a f.g. left $R_kappa$-module which is $ZZ$-torsionfree. It
follows at once from Exercise~@exc:lattices-integral-base-change that $N$ is
also $R_kappa$-torsionfree, and is therefore an $R_kappa$-lattice.) Analogously,
every $hat(Lambda)$-lattice is an extension of an $hat(R)_kappa$-lattice by a
$hat(Lambda)_(kappa-1)$-lattice.

The problem of classifying all $Lambda_kappa$-lattices is thus reduced to the
following:
#enum(
  numbering: "(i)",
  [Classify all $Lambda_(kappa-1)$-lattices $L$ and all $R_kappa$-lattices
    $N$.],
  [Classify the isomorphism classes of extensions of $N$ by $L$.],
)
Since $R_kappa$ is a Dedekind domain, it follows that we may write
$
  N tilde.equiv product.co_(k=1)^s frak(c)_k, quad
  "so" N or.curly R_kappa^((s)),
$
where the ${frak(c)_k}$ are $R_kappa$-ideals in $K_kappa$. The isomorphism
invariants of $N$ are its rank $s$, and its Steinitz class (see @th:steinitz).
Of course, the problem of finding all $Lambda_(kappa-1)$-lattices is the same as
our original problem, except that $kappa$ has decreased by $1$. Further, by
@rem:lattice-extension-classification, problem (ii) is equivalent to determining
the $(Aut N,Aut L)$-orbits of $"Ext"(N,L)$. By
@cor:standard-extension-automorphism-orbits, in this determination we may
replace $L$ by $L'$, $N$ by $N'$, where $L' or.curly L$ and $N' or.curly N$.

The same discussion shows that the genus of $M$ is completely determined by the
genus of $L$, the rank $s$ of $N$, and an $(Aut hat(N),Aut hat(L))$-orbit in
$"Ext"(hat(N),hat(L))$.

In the special case where $kappa=1$, we have $Lambda_(kappa-1)=ZZ$, and $L$ is
just a $ZZ$-lattice. We may treat a slightly more general version of this
situation, as follows. Let $kappa>=1$, and let $E=ZZ[x] slash (h(x))$, where
$h(x)$ is a non-constant monic factor of $x^(p^(kappa-1))-1$ in $ZZ[x]$. Then
$E$ is an indecomposable $ZZ$-order which is a factor ring of $Lambda_(kappa-1)$
(see Exercise~@exc:cyclotomic-factor-order-indecomposable). We shall treat the
case in which $L$ is a locally free $E$-lattice, that is, $L or.curly E^((r))$
for some $r$. Our aim is to classify all $Lambda$-lattices $M$ which are
extensions of an $R_kappa$-lattice $N$ by a locally free $E$-lattice $L$.

#source(744)
Suppose now that $L$ and $N$ are given as above. Since $L or.curly E^((r))$ and
$N or.curly R_kappa^((s))$ for some $s$, we have
$ "Ext"(N,L) tilde.equiv {"Ext"(R_kappa,E)}^(r times s), $
where ${Omega}^(r times s)$ means the set of $r times s$ matrices with entries
in $Omega$. Since $(x^(p^(kappa-1))-1)E=0$, Step~3 of the proof of
@th:diederichsen-cyclotomic-extensions shows that
$
  "Ext"(R_kappa,E) tilde.equiv E slash Phi_kappa (x)E
  =E slash p E=overline(E),
$
where bar denotes reduction mod $p$. Thus
$
  "Ext"(N,L) tilde.equiv overline(E)^(r times s), quad
  overline(E)=overline(ZZ)[x] slash (h(x))
  =overline(ZZ)[x] slash (x-1)^d overline(ZZ)[x],
$
where $d$ is the degree of the polynomial $h(x)$. Since $Lambda$ is commutative,
$"Ext"(N,L)$ is naturally a $Lambda$-module, by virtue of the action of $Lambda$
on either $N$ or $L$. The above isomorphisms are easily seen to be
$Lambda$-isomorphisms.

In addition, when $N=R_kappa^((s))$ and $L=E^((r))$, we have
$
  Aut_Lambda N=Aut_(R_kappa)N="GL"_s (R_kappa), quad
  Aut_Lambda L=Aut_E L="GL"_r (E).
$
We therefore obtain:

#proposition[
  Let $N$ be an $R_kappa$-lattice of rank $s$, and $L$ a locally free
  $E$-lattice such that $L or.curly E^((r))$. Then there is a bijection between
  the set of orbits of $"Ext"_Lambda^1 (N,L)$ under the actions of $Aut(N)$ and
  $Aut(L)$, and the set of orbits of $(overline(E))^(r times s)$ under the
  actions of $"GL"_r (E)$ and $"GL"_s (R_kappa)$.
] <prop:cyclic-p-extension-matrix-orbits>

We note that there is a surjection $E->E slash p E=overline(E)$, and also
surjections
$
  R_kappa->R_kappa slash p R_kappa
  tilde.equiv overline(ZZ)[x] slash ((x-1)^(phi(p^kappa)))->overline(E),
$
since $d=deg h(x)<=p^(kappa-1)<=phi(p^kappa)$. By virtue of these surjections,
$"GL"_r (E)$ and $"GL"_s (R_kappa)$ act on $(overline(E))^(r times s)$, and this
agrees with the action arising from their actions on $L$ and $N$, respectively.
Furthermore, we observe that $overline(E)$ is a local principal ideal ring,
whose ideals are powers of $(x-1)overline(E)$. In this situation we can describe
the orbits of $overline(E)^(r times s)$ explicitly, following the treatment in
Reiner~@bib:Reiner1978.

Changing notation, let $Gamma$ and $Delta$ be a pair of commutative rings, and
let $phi:Gamma->overline(Gamma)$, $psi:Delta->overline(Gamma)$, be a pair of
ring surjections. We assume that $overline(Gamma)$ is a local principal ideal
ring, whose distinct ideals are given by
$ {lambda^k overline(Gamma):0<=k<=e}, quad "where" lambda^e overline(Gamma)=0. $
Let $overline(Gamma)^(r times s)$ be the $overline(Gamma)$-module consisting of
all $r times s$ matrices over $overline(Gamma)$. We shall find
#source(745)
the $("GL"_r (Gamma),"GL"_s (Delta))$-orbits of $overline(Gamma)^(r times s)$.
Given $xi_1,xi_2 in overline(Gamma)^(r times s)$, we write $xi_1 approx xi_2$,
and call them _globally equivalent_, if
$
  xi_2=alpha xi_1 beta "for some" alpha in "GL"_r (Gamma),
  beta in "GL"_s (Delta).
$
Note that $alpha$ acts as $phi_* lr((alpha))$, where $phi$ induces the group
homomorphism $phi_*:"GL"(Gamma)->"GL"(overline(Gamma))$; likewise, $beta$ acts
as $psi_* lr((beta))$, where $psi_*:"GL"(Delta)->"GL"(overline(Gamma))$. If
$xi_2 approx xi_1$, then of course $xi_2=mu xi_1 nu$ for some
$mu,nu in "GL"(overline(Gamma))$, so the matrices $xi_1$ and $xi_2$ are
equivalent in the usual (weaker) sense. We can then use the machinery of
elementary divisors over $overline(Gamma)$; each elementary divisor may be
chosen to be a power of the prime element $lambda$ of $overline(Gamma)$. We put
$ "el. div."(xi)="set of elementary divisors of" xi, $
where $xi in overline(Gamma)^(r times s)$. Clearly, for
$xi_1,xi_2 in overline(Gamma)^(r times s)$,
$ xi_1 approx xi_2 ==> "el. div."(xi_1)="el. div."(xi_2). $
<eq:global-equivalence-elementary-divisors>
We need some easy facts about global equivalence of matrices over
$overline(Gamma)$. Letting $overline(Gamma)^dot$ denote the group of units of
$overline(Gamma)$, we have:

#lemma[
  For $u in overline(Gamma)^dot$, let $bold(D)_u$ denote a diagonal matrix in
  $"GL"_r (overline(Gamma))$ with diagonal entries $u,u^(-1),1,dots,1$, arranged
  in any order. Let $bold(D)_u^*$ denote an analogous matrix in
  $"GL"_s (overline(Gamma))$. Then for any $xi in overline(Gamma)^(r times s)$,
  we have
  $ xi approx bold(D)_u xi approx xi bold(D)_u^*. $
] <lem:global-equivalence-balanced-units>
#proof[
  In $"GL"_2(overline(Gamma))$, there is an identity
  $
    mat(u, 0; 0, u^(-1))=mat(1, u-1; 0, 1)mat(1, 0; 1, 1)
    mat(1, u^(-1)-1; 0, 1)mat(1, 0; -u, 1).
  $
  <eq:balanced-units-elementary-factorization>
  Hence $bold(D)_u$ is expressible as a product of elementary#footnote[
    An elementary matrix is one obtained from the identity matrix by replacing
    exactly one off-diagonal zero entry by some element of the ring.
  ] matrices in $"GL"_r (overline(Gamma))$. But each factor is the image of an
  elementary matrix over $Gamma$, and therefore $xi approx bold(D)_u xi$.
  Likewise we obtain $xi approx xi bold(D)_u^*$.
]

#proposition[
  #enum(
    numbering: "(i)",
    [If $r<s$, then each $xi in overline(Gamma)^(r times s)$ is globally
      equivalent to a matrix $[bold(D) 0]$, where
      $
        bold(D)="diag"(lambda^(k_1)u_1,dots,lambda^(k_r)u_r), quad
        0<=k_1<=dots<=k_r<=e, quad u_i in overline(Gamma)^dot.
      $
      <eq:global-equivalence-diagonal-form>],
    [If $r>s$, then $xi approx vec(bold(D)^*, 0, delim: "[")$, where $bold(D)^*$
      is a diagonal $s times s$ matrix of the above type.],
    [Let $xi_1,xi_2 in overline(Gamma)^(r times s)$, where $r!=s$. Then
      $xi_1 approx xi_2$ if and only if $"el. div."(xi_1)="el. div."(xi_2)$.],
  )
] <prop:rectangular-global-equivalence>
#source(746)
#proof[
  For (i), let $xi in overline(Gamma)^(r times s)$, where $r<s$. Since
  $overline(Gamma)$ is a local principal ideal ring, we can bring $xi$ into the
  form $[bold(D) 0]$, with $bold(D)$ as in @eq:global-equivalence-diagonal-form,
  by a sequence of left and right multiplications by elementary matrices over
  $overline(Gamma)$. Each such elementary matrix is the image of a corresponding
  elementary matrix over $Gamma$ or $Delta$, and therefore
  $xi approx [bold(D) 0]$ as claimed. An analogous argument gives (ii).

  Suppose now that $xi approx [bold(D) 0]$, with $bold(D)$ as in
  @eq:global-equivalence-diagonal-form. Then
  $ "el. div."(xi)={lambda^(k_1),dots,lambda^(k_r)}. $
  We have already shown that $"el. div."(xi)$ is an invariant of the global
  equivalence class of $xi$. Hence, to prove (iii), we may assume that $r<s$ and
  that $"el. div."(xi_1)="el. div."(xi_2)$; we need to show that
  $xi_1 approx xi_2$ in this case. Since $xi_1 approx [bold(D) 0]$ for some
  $bold(D)$ as above, we have by @lem:global-equivalence-balanced-units
  $
    xi_1 approx [bold(D) 0] "diag"(u_1^(-1),u_2^(-1),dots,u_r^(-1),
      underbrace(u_1 dots u_r comma 1 comma dots comma 1, s-r)) \
    approx [bold(D)_1 0], quad "where"
    bold(D)_1="diag"(lambda^(k_1),dots,lambda^(k_r)).
  $
  Since $"el. div."(xi_1)="el. div."(xi_2)$, we obtain $xi_1 approx xi_2$, which
  completes the proof of the proposition.
]

The preceding result shows that when $r!=s$, the set $"el. div."(xi)$ completely
determines the global equivalence class of an element
$xi in overline(Gamma)^(r times s)$. The case where $r=s$ is considerably more
interesting and difficult, and some additional notation is required in order to
state the main result.

Suppose that $xi in overline(Gamma)^(r times r)$ has elementary divisors
$lambda^(k_1),dots,lambda^(k_r)$, and let
$ xi approx bold(D)="diag"(lambda^(k_1)u_1,dots,lambda^(k_r)u_r), $
as in @eq:global-equivalence-diagonal-form. Let
$
  Omega_xi=(Gamma')^dot slash (Gamma^* Delta^*), quad
  "where" Gamma'=overline(Gamma) slash lambda^(e-k_r)overline(Gamma),
$
<eq:global-equivalence-unit-quotient>
and where $Gamma^*$ and $Delta^*$ denote the images of $Gamma^dot$ and
$Delta^dot$, respectively, in the group of units $(Gamma')^dot$. Note that the
ring $Gamma'$ and the group $Omega_xi$ depend only upon $"el. div."(xi)$. We now
set
$ w(xi)="image of" u_1 u_2 dots u_r "in" Omega_xi, $
assuming $xi approx bold(D)$ as above. Our main result, due to
Reiner~@bib:Reiner1978, is as follows:

#source(747)
#theorem[
  Let $xi_1,xi_2 in overline(Gamma)^(r times r)$. Then $xi_1 approx xi_2$ if and
  only if
  $
    "el. div."(xi_1)="el. div."(xi_2), quad "and"
    w(xi_1)=w(xi_2) "in" Omega_xi.
  $
] <th:square-global-equivalence>
#proof[
  _Step 1._ Supposing the conditions satisfied, let $xi_1 approx bold(D)$ as
  above, and let
  $
    xi_2 approx "diag"(lambda^(k_1)u'_1,dots,lambda^(k_r)u'_r), quad
    u'_i in overline(Gamma)^dot.
  $
  Setting $u=u_1 dots u_r$ and $u'=u'_1 dots u'_r$, it follows from
  @lem:global-equivalence-balanced-units that
  $
    xi_1 approx "diag"(lambda^(k_1),dots,lambda^(k_(r-1)),lambda^(k_r)u),
    quad xi_2 approx
    "diag"(lambda^(k_1),dots,lambda^(k_(r-1)),lambda^(k_r)u').
  $
  <eq:square-global-equivalence-unit-product>
  The condition $w(xi_1)=w(xi_2)$ means that $u'=gamma u delta$ in $Gamma'$ for
  some $gamma in Gamma^dot$, $delta in Delta^dot$. But then
  $lambda^(k_r)u'=gamma lambda^(k_r)u dot delta$ in $overline(Gamma)$, and
  therefore
  $
    "diag"(1,dots,1,gamma) dot
    "diag"(lambda^(k_1),dots,lambda^(k_r)u) dot
    "diag"(1,dots,1,delta)
    ="diag"(lambda^(k_1),dots,lambda^(k_r)u').
  $
  This implies that $xi_1 approx xi_2$, as desired.

  _Step 2._ Assume conversely that $xi_1 approx xi_2$, so then
  $"el. div."(xi_1)="el. div."(xi_2)$, and we may assume that $xi_1$ and $xi_2$
  are equal to the diagonal matrices given in
  @eq:square-global-equivalence-unit-product. The hypotheses imply that
  $gamma xi_1=xi_2 delta$ for some $gamma in "GL"_r (Gamma)$,
  $delta in "GL"_r (Delta)$. Our aim is to use determinants to show that
  $(det gamma)u=u'(det delta)$ in the ring $Gamma'$ defined in
  @eq:global-equivalence-unit-quotient. Set
  $bold(D)_0="diag"(lambda^(k_1),dots,lambda^(k_r))$. The equality
  $gamma xi_1=xi_2 delta$ can be rewritten as
  $
    mu bold(D)_0=bold(D)_0 nu, quad "where" mu=gamma "diag"(1,dots,1,u),
    quad nu="diag"(1,dots,1,u') dot delta.
  $
  As we shall show in our next step, the above implies that
  $
    (det mu) dot lambda^(k_r)=(det nu) dot lambda^(k_r)
    "in" overline(Gamma).
  $
  Since
  $
    det mu=u dot det gamma in u dot Gamma^*, quad
    det nu=u' dot det delta in u' dot Delta^*,
  $
  this implies that the images of $u$ and $u'$ in $(Gamma')^dot$ differ by
  factors from $Gamma^*$ and $Delta^*$. Hence $w(xi_1)=w(xi_2)$, as claimed.

  _Step 3._ To complete the proof, it suffices to establish the following
  interesting result about determinants:
]

#lemma[
  Let $R$ be an arbitrary commutative ring, and let
  $bold(D)="diag"(d_1,dots,d_m)$ be a matrix with entries in $R$, such that
  $ r_1 d_1=dots=r_(m-1)d_(m-1)=d_m $
  #source(748)
  for some elements $r_i in R$. Let $bold(X)$ and $bold(Y)$ be $m times m$
  matrices over $R$ such that $bold(X) bold(D)=bold(D) bold(Y)$. Then
  $ (det bold(X))d_m=(det bold(Y))d_m "in" R. $
] <lem:determinant-divisible-diagonal-intertwining>
#proof[
  Write $bold(X)=(x_(i j))$, $bold(Y)=(y_(i j))$. From
  $bold(X) bold(D)=bold(D) bold(Y)$ we obtain
  $ x_(i j)d_j=d_i y_(i j), quad "for" 1<=i,j<=m. $
  Let $pi:{1,dots,m}->{i_1,dots,i_m}$ be any permutation of the symbols
  $1,dots,m$. A typical term in the expansion of $det bold(X)$ is of the form
  $ plus.minus x_(1 i_1) dots x_(m i_m), $
  so we need only verify that for each $pi$, we have
  $ x_(1 i_1) dots x_(m i_m)d_m=y_(1 i_1) dots y_(m i_m)d_m. $
  <eq:determinant-cycle-products>
  Write $pi$ as a product of disjoint cycles, and suppose (by way of
  illustration) that $(a,b,c)$ is a $3$-cycle occurring as a factor of $pi$.
  Then
  $
    x_(a b)x_(b c)x_(c a)d_m
    =r_a x_(a b)x_(b c)x_(c a)d_a
    =r_a x_(a b)x_(b c)d_c y_(c a) \
    =r_a x_(a b)d_b y_(b c) dot y_(c a)
    =r_a d_a y_(a b)y_(b c)y_(c a)
    =d_m dot y_(a b)y_(b c)y_(c a).
  $
  The same procedure applies to each of the cycles occurring as a factor of
  $pi$. This establishes @eq:determinant-cycle-products, and completes the proof
  of the lemma, as well as the proof of Theorem~@th:square-global-equivalence.
]

We now return to the situation described in
Proposition~@prop:cyclic-p-extension-matrix-orbits, since we can use the results
of Theorem~@th:square-global-equivalence to classify the orbits of
$overline(E)^(r times s)$ under the actions of $"GL"_r (E)$ and
$"GL"_s (R_kappa)$. Since each orbit contains a diagonalized matrix, it follows
that there are exactly three kinds of indecomposable $Lambda$-lattices $M$ which
are extensions of an $R_kappa$-lattice $N$ by a locally free $E$-lattice $L$.
Furthermore, all extensions $M$ can be completely classified, up to isomorphism.
We summarize our results in the following:

#theorem(title: [Reiner~@bib:Reiner1978])[
  Let $kappa>=1$, and set
  $
    Lambda=ZZ[x] slash (x^(p^kappa)-1), quad E=ZZ[x] slash (h(x)), quad
    R_kappa=ZZ[x] slash (Phi_kappa (x)),
  $
  where $h(x)$ is a monic factor of $x^(p^(kappa-1))-1$ in $ZZ[x]$ of degree
  $d$, and $Phi_kappa (x)$ is the cyclotomic polynomial of order $p^kappa$ and
  degree $phi(p^kappa)$. Let
  $
    overline(E)=E slash p E=overline(ZZ)[lambda] slash (lambda^d), quad
    "where" lambda=x-1.
  $
  Let $frak(b)$ range over the $R_kappa$-ideals in the cyclotomic field
  $K_kappa=QQ[x] slash (Phi_kappa (x))$, and let
  #source(749)
  $frak(c)$ range over all locally free ideals of $E$ (that is, all ideals in
  the genus of $E$). There is an isomorphism of $Lambda$-modules
  $ "Ext"_Lambda^1(frak(b),frak(c)) tilde.equiv overline(E), $
  which we treat as an identification.
  #enum(
    numbering: "(i)",
    [Let $M$ be an indecomposable $Lambda$-lattice which is an extension of an
      $R_kappa$-lattice by a locally free $E$-lattice. Then $M$ is isomorphic to
      exactly one of the following: $frak(b)$, $frak(c)$, and
      $(frak(b),frak(c);lambda^k u)$, where $frak(b)$ ranges over a full set of
      ideal class representatives of $R_kappa$, $frak(c)$ ranges over a full set
      of isomorphism class representatives of locally free ideals of $E$, and
      where $(frak(b),frak(c);lambda^k u)$ denotes a non-split extension of
      $frak(b)$ by $frak(c)$, corresponding to the extension class
      $lambda^k u in overline(E)="Ext"(frak(b),frak(c))$. Here, $0<=k<d$ and
      $u in overline(E)^dot$. Further, the isomorphism class of
      $(frak(b),frak(c);lambda^k u)$ is completely determined by the classes of
      $frak(b)$ and $frak(c)$, the integer $k$, and the image of $u$ in the
      group
      $
        Omega_k=(E')^dot slash (E^* R_kappa^*), quad "where"
        E'=overline(E) slash (lambda^(d-k))
        tilde.equiv overline(ZZ)[lambda] slash (lambda^(d-k)).
      $
      Here, $E^*$ and $R_kappa^*$ denote the images of $E^dot$ and
      $R_kappa^dot$, respectively, in $(E')^dot$.],
    [Let $M$ be an arbitrary $Lambda$-lattice which is an extension of an
      $R_kappa$-lattice $N$ by a locally free $E$-lattice $L$. Then we may
      express $M$ as a direct sum of indecomposable $Lambda$-lattices:
      $
        M tilde.equiv product.co_(i=1)^a
        (frak(b)_i,frak(c)_i;lambda^(k_i)u_i)
        plus.o product.co_(j=a+1)^(a+b)frak(b)_j
        plus.o product.co_(k=a+1)^(a+c)frak(c)_k,
      $
      <eq:cyclic-p-extension-direct-sum>
      where $0<=k_i<d$, $u_i in overline(E)^dot$ for each $i$. For this $M$, we
      have
      $
        N tilde.equiv product.co_(i=1)^(a+b)frak(b)_i, quad
        L tilde.equiv product.co_(j=1)^(a+c)frak(c)_j.
      $],
    [The genus of the lattice $M$ in @eq:cyclic-p-extension-direct-sum is
      completely determined by the following invariants:
      $ a+b=R_kappa"-rank of" N; quad a+c=E"-rank of" L; $
      the set of exponents $k_1,dots,k_a$.],
    [For $M$ as in @eq:cyclic-p-extension-direct-sum, the additional invariants
      of the isomorphism class of $M$, needed to determine this isomorphism
      class, once the genus invariants are given as in (iii), are as follows:
      #enum(
        numbering: "(I)",
        [The isomorphism class of $product_(i=1)^(a+b)frak(b)_i$, that is, the
          Steinitz class of $N$.#idx("Steinitz class")],
        [The isomorphism class of $product_(j=1)^(a+c)frak(c)_j$, that is, the
          “Steinitz class” of $L$.],
        [#source(750)
          Only for the case where $b=c=0$, the image of $u_1 dots u_a$ in the
          multiplicative group $W=W_M$, defined by
          $ W=(E')^dot slash (E^* R_kappa^*), $
          where
          $
            m=max(k_1, dots, k_a), quad E'=overline(E) slash (lambda^(d-m))
            tilde.equiv overline(ZZ)[lambda] slash (lambda^(d-m)).
          $],
      )],
  )
] <th:cyclic-p-locally-free-extension-classification>
#proof[
  Let $M$ be an extension of $N$ by $L$, corresponding to an extension class
  $xi in "Ext"_Lambda^1(N,L)$. We identify $"Ext"_Lambda^1(N,L)$ with
  $overline(E)^(r times s)$, as in the discussion preceding
  @prop:cyclic-p-extension-matrix-orbits. The lattice $M$ is then determined up
  to isomorphism by the isomorphism classes of $N$ and $L$, and the
  $("GL"_r (E),"GL"_s (R_kappa))$-orbit of $xi$ in $overline(E)^(r times s)$.
  Since the orbit of $xi$ contains a diagonalized matrix, with diagonal entries
  of the form $lambda^k u$, $0<=k<d$, $u in overline(E)^dot$, the only possible
  indecomposable $M$'s are those given in (i). The assertion in (i), as to the
  isomorphism invariants of $(frak(b),frak(c);lambda^k u)$, is a direct
  consequence of @th:square-global-equivalence.

  Now let $M$ be expressed as in @eq:cyclic-p-extension-direct-sum, in which
  case the expressions given for $N$ and $L$ are obvious. The extension class
  $xi$ determined by $M$ is given by the matrix
  $
    xi=mat(
      delim: "[", lambda^(k_1)u_1, , , , 0;
      , dots.down, , , dots.v;
      , , lambda^(k_a)u_a, , dots.v;
      , , , dots.down, dots.v;
      0, dots.h, dots.h, dots.h, 0
    )^((a+c)times(a+b)).
  $
  Since ${k_1,dots,k_a}$ are the genus invariants associated with $xi$,
  assertion (iii) follows at once from our earlier remarks.

  It remains for us to list the isomorphism invariants of $M$. By Steinitz's
  Theorem, $N$ is determined by its $R_kappa$-rank and Steinitz class. We shall
  show below that a corresponding statement is true for $L$. The only remaining
  invariant is that needed to characterize the orbit of $xi$, once the exponents
  ${k_i}$ are specified. But by @prop:rectangular-global-equivalence, there is
  no additional invariant needed except when $b=c=0$, and in that case we obtain
  the asserted result by use of @th:square-global-equivalence. This completes
  the proof of the theorem, except for the assertion about the classification of
  locally free $E$-lattices. This assertion is a consequence of a result which
  is of independent interest:
]

#proposition[
  Let $E$ be a commutative order, and let $L=product.co_(i=1)^r frak(c)_i$ where
  the ${frak(c)_i}$ are locally free ideals of $E$. A full set of isomorphism
  invariants of $L$ consists of its $E$-rank $r$, and the $E$-isomorphism class
  of the product $product_(i=1)^r frak(c)_i$ (called the Steinitz class of
  $L$).#idx(
    "Steinitz class",
    target: [@prop:commutative-order-steinitz-invariants],
  )
] <prop:commutative-order-steinitz-invariants>
#source(751)
#proof[
  Since each $frak(c)_i$ lies in the genus of $E$, by
  @cor:genus-multiple-decomposition we obtain
  $ L=product.co_(i=1)^r frak(c)_i tilde.equiv E^((r-1)) plus.o frak(c)' $
  for some $frak(c)' or.curly E$. We shall prove that
  $frak(c)' tilde.equiv product_(i=1)^r frak(c)_i$. Let $and.big^k (L)$ denote
  the $k$-th exterior power of the $E$-module $L$ over the commutative ring $E$
  (see @ss:tensor-symmetric-exterior-algebras). It is easily verified that
  $
    and.big^r lr((product.co_(i=1)^r frak(c)_i))
    tilde.equiv product_(i=1)^r frak(c)_i, quad
    and.big^r (E^((r-1)) plus.o frak(c)') tilde.equiv frak(c)',
  $
  which establishes the proposition. This also completes the proof of
  Theorem~@th:cyclic-p-locally-free-extension-classification.
]

Let us apply this machinery to the special case where $kappa=1$, so $G$ is a
cyclic group of order $p$, and $Lambda_(kappa-1)=ZZ$. As we have seen earlier,
every $Lambda$-lattice $M$ is an extension of an $R$-lattice $N$ by a
$ZZ$-lattice $L$, where
$ R=ZZ[omega], quad omega="primitive" p"-th root of" 1 "over" QQ. $
Keeping this notation, we obtain the result of
Diederichsen~@bib:Diederichsen1940, as extended by Reiner~@bib:Reiner1957\:

#theorem[
  Let $frak(b)$ range over a full set of representatives of the $R$-ideal
  classes in the cyclotomic field $QQ(omega)$. Then every $ZZ G$-lattice $M$ is
  expressible as a direct sum of indecomposable lattices
  $
    M tilde.equiv product.co_(i=1)^a (frak(b)_i,ZZ;1)
    plus.o product.co_(j=a+1)^(a+b)frak(b)_j plus.o ZZ^((c)),
  $
  where $(frak(b)_i,ZZ;1)$ is a non-split extension of $frak(b)_i$ by $ZZ$.

  The genus invariants of $M$ are the integers $a$, $b$, and $c$. The only
  additional invariant needed to determine the isomorphism class of $M$ is the
  ideal class of the product $product_(i=1)^(a+b)frak(b)_i$.
  #idx(
    "Diederichsen's Theorem",
    target: [@th:prime-cyclic-integral-lattice-classification],
  )
] <th:prime-cyclic-integral-lattice-classification>
#proof[
  We use @th:cyclic-p-locally-free-extension-classification with $kappa=1$,
  $E=ZZ=ZZ[x] slash (x-1)$, $d=1$, $overline(E)=overline(ZZ)=ZZ slash p ZZ$,
  $R_kappa=R$. Each $frak(c)_i$ in
  @th:cyclic-p-locally-free-extension-classification may be replaced by $ZZ$,
  and since $d=1$, the non-split extensions $(frak(b),frak(c);lambda^k u)$
  mentioned above are just $(frak(b),ZZ;u)$, with $u in overline(ZZ)^dot$. To
  complete the proof, it suffices to show that
  $ (frak(b),ZZ;u) tilde.equiv (frak(b),ZZ;1) "for" u in overline(ZZ)^dot. $
  But this follows at once from
  @th:cyclic-p-locally-free-extension-classification(i), as soon as we show that
  the surjection
  $ R->R slash (1-omega)R tilde.equiv overline(ZZ) $
  gives a surjection $R^dot->overline(ZZ)^dot$.
  #source(752)
  To prove this last assertion, let $n in ZZ$ be relatively prime to $p$. Then
  $omega$ is expressible as a power of $omega^n$, and so
  $
    (1-omega^n) slash (1-omega) in R "and"
    (1-omega) slash (1-omega^n) in R.
  $
  Thus $u=(1-omega^n) slash (1-omega) in R^dot$, and we shall show that the
  image of $u$ in $overline(ZZ)^dot$ is precisely $overline(n)$. Indeed, setting
  $lambda=1-omega$, we have
  $ u=(1-(1-lambda)^n) slash lambda equiv n mod lambda, $
  so $overline(u)=overline(n)$ in $overline(ZZ)$. This completes the proof of
  the theorem. For a more direct proof, see @bib:CurtisReiner1962[CR] (74.3).
]

We remark finally that
Theorem~@th:cyclic-p-locally-free-extension-classification can be used to
classify all $ZZ[x] slash ((x-1)Phi_kappa (x))$-lattices, for $kappa>=1$. In
fact, each such lattice is an extension of an $R_kappa$-lattice by a free
$ZZ$-lattice.

As another application of the theorem, let $Delta=ZZ H$, where $H$ is a cyclic
group of order $g$. Let $zeta_m$ denote a primitive $m$-th root of $1$ over
$QQ$, and set $S_m=ZZ[zeta_m]$. If $m$ and $n$ are divisors of $g$, then $S_m$
and $S_n$ are $Delta$-modules. Diederichsen's formula
@th:diederichsen-cyclotomic-extensions gives
$ "Ext"_Delta^1(S_n,S_m) tilde.equiv S_m slash p S_m=overline(S)_m, $
if $n=p^t m$ for some prime $p$ and some $t>=1$. Then $overline(S)_m$ is a
semilocal ring, and the proofs of @prop:rectangular-global-equivalence and
@th:cyclic-p-locally-free-extension-classification carry over readily to this
case. We can then classify all $Delta$-lattices which are extensions of an
$S_n$-lattice by an $S_m$-lattice. For details, see Reiner~@bib:Reiner1979b.
Some partial results of this nature are also to be found in
Berman~@bib:Berman1964.

=== Cyclic Groups of Order $p^2$ <ss:cyclic-p-squared-lattices>

Keeping the notation of @ss:cyclic-p-group-lattices, we concentrate here on the
case where $G$ is cyclic of order $p^2$, in which case we can completely
classify all $ZZ G$-lattices. Let $Lambda=ZZ G$, and let $hat(Lambda)=hat(ZZ)G$
be its $p$-adic completion. By @lem:cyclic-p-lattice-completion-indecomposable,
a $Lambda$-lattice $M$ is indecomposable if and only if the
$hat(Lambda)$-lattice $hat(M)$ is indecomposable. We shall first find all
indecomposable $hat(Lambda)$-lattices $hat(M)$ (of which there are only finite
many isomorphism classes; see
Exercise~@exc:prime-square-cyclic-finite-type-criterion). Then we shall
determine all $M$'s which correspond to a given $hat(M)$, and shall list a full
set of isomorphism invariants for a direct sum of indecomposable
$Lambda$-lattices.

A historical account may be of interest. In his fundamental work on integral
representations of cyclic groups, Diederichsen~@bib:Diederichsen1940 considered
the question as to whether $hat(Lambda)$ has finite representation type, and
gave an example to show that $hat(Lambda)$ is of infinite type when $p=2$. This
example was incorrect, however, as pointed out independently by
Roiter~@bib:Roiter1960 and Troy~@bib:Troy1961. Both of them gave a full list of
indecomposable $hat(Lambda)$-lattices for this case, and indeed the
#source(753)
number $n(hat(Lambda))$ of isomorphism classes of such lattices turned out to be
$9$. Soon after, Heller–Reiner~@bib:Heller1962 and
Berman–Gudivok~@bib:Berman1964a independently proved that for arbitrary $p$,
$n(hat(Lambda))=4p+1$, and therefore $n(Lambda)<infinity$ by
@lem:cyclic-p-lattice-completion-indecomposable and the Jordan–Zassenhaus
Theorem. (The earlier announcement by Berman–Gudivok~@bib:Berman1962 contains
some errors.)

We shall follow the Heller–Reiner proof that $n(hat(Lambda))=4p+1$; a completely
different approach has recently been given by Butler~@bib:Butler1975 (see also
Wiedemann~@bib:Wiedemann1980). We shall set
$ E=ZZ[x] slash (x^p-1), $
a factor ring of $Lambda$, so every $E$-lattice is also a $Lambda$-lattice.
Theorem~@th:prime-cyclic-integral-lattice-classification gives a complete
classification of $E$-lattices. Now let $M$ be any $Lambda$-lattice, and set
$ L={m in M:(x^p-1)m=0}. $
The discussion at the beginning of @ss:cyclic-p-group-lattices shows that there
is an exact sequence of $Lambda$-lattices
#named-equation(name: [$(xi)$])[$ 0->L->M->N->0 $]
<eq:prime-square-extension-sequence>
in which $N$ is an $R_2$-lattice, $L$ an $E$-lattice, and for which
$Hom_Lambda (L,N)=0$. A full set of isomorphism invariants of $M$ consists of
the isomorphism class invariants of $N$ and $L$, together with the invariants
describing the $(Aut N,Aut L)$-orbit of $xi$ in $"Ext"(N,L)$. As in
@eq:lattice-extension-notation, we shall write $M=(N,L;xi)$.

Let us first determine all indecomposable $hat(Lambda)$-lattices $hat(M)$; each
such $hat(M)$ is an extension of an $hat(R)_2$-lattice $hat(N)$ by an
$hat(E)$-lattice $hat(L)$. By @th:prime-cyclic-integral-lattice-classification,
we may write $hat(N)=hat(R)_2^((s))$ and
$ hat(L)=hat(ZZ)^((a)) plus.o hat(R)_1^((b)) plus.o hat(E)^((c)). $
The integer $s$ determines $hat(N)$ up to isomorphism, while the triple
${a,b,c}$ is a full set of isomorphism invariants of $hat(L)$. If bars denote
reduction mod $p$, then, as shown in @ss:cyclic-p-group-lattices,
$
  "Ext"_(hat(Lambda))^1(hat(N),hat(L))
  tilde.equiv {"Ext"(hat(R)_2,hat(L))}^((s))
  tilde.equiv overline(ZZ)^(a times s) plus.o overline(R)_1^(b times s)
  plus.o overline(E)^(c times s).
$
We have
$
  overline(R)_1=overline(ZZ)[lambda] slash (lambda^(p-1)), quad
  overline(E)=overline(ZZ)[lambda] slash (lambda^p), quad "where" lambda=1-x.
$
Clearly $Aut hat(N) tilde.equiv "GL"_s (hat(R)_2)$, which acts on the expression
for $"Ext"(hat(N),hat(L))$ by means of the ring surjections of $hat(R)_2$ onto
$overline(ZZ)$, $overline(R)_1$ and $overline(E)$. These surjections induce
surjections of groups of units $(hat(R)_2)^dot->overline(ZZ)^dot$, etc.

#source(754)
Each $hat(Lambda)$-lattice $hat(M)$, indecomposable or not, is thus completely
determined by the non-negative integers $s$, $a$, $b$, and $c$, and by the
matrix
$
  xi=vec(bold(F)_0, bold(F)_1, bold(F)_2, delim: "["), quad bold(F)_0 in
  overline(ZZ)^(a times s), quad
  bold(F)_1 in overline(R)_1^(b times s), quad bold(F)_2 in overline(E)^(c times
  s).
$
If $hat(M)$ is indecomposable, and if $s=0$, then the choices for $hat(M)$ are
precisely $hat(ZZ)$, $hat(R)_1$ or $hat(E)$. For the remainder of this argument,
let us assume that $s>0$ and that $hat(M)$ is indecomposable.

To proceed, we need to calculate $"End"_(hat(Lambda))hat(L)$. We have
$
  Hom(hat(ZZ), hat(R)_1)=Hom(hat(R)_1, hat(ZZ))=0, quad
  "End" hat(ZZ)=hat(ZZ), quad "End" hat(R)_1=hat(R)_1,
  quad "End" hat(E)=hat(E),
$
$
  Hom(hat(ZZ), hat(E)) tilde.equiv Phi_1(x)hat(E), quad
  Hom(hat(R)_1, hat(E)) tilde.equiv lambda hat(E), quad
  Hom(hat(E), hat(ZZ)) tilde.equiv hat(ZZ), quad
  Hom(hat(E), hat(R)_1) tilde.equiv hat(R)_1.
$
(Note that each $phi in Hom(hat(E), hat(ZZ))$ is given by $phi(u)=u r$,
$u in hat(E)$, where $r in hat(ZZ)$ is arbitrary, and where the action of $u$ on
$r$ arises from the surjection $hat(E)->hat(ZZ)$. On the other hand, each
$psi in Hom(hat(ZZ), hat(E))$ is given by $psi(v)=v s$, $v in hat(ZZ)$, where
$s in hat(E)$ is subject to the restriction that $(1-x)s=0$, or equivalently,
that $s in Phi_1(x)hat(E)$. Analogous remarks hold for the other cases.)

It follows that $"End"_(hat(Lambda))hat(L)$ consists of all matrices
$
  f=mat(
    delim: "[", bold(A)_0, 0, bold(A)_(02); 0, bold(A)_1, bold(A)_(12);
    Phi_1(x)bold(A)_(20), lambda bold(A)_(21), bold(A)_2
  ),
  quad bold(A)_0 in hat(ZZ)^(a times a), quad bold(A)_1 in hat(R)_1^(b times b),
  quad bold(A)_2 in hat(E)^(c times c),
$
where the rows have entries in $hat(ZZ)$, $hat(R)_1$ and $hat(E)$, respectively.
The orbit of $xi$ in $"Ext"(hat(N),hat(L))$ thus consists of all matrices
$f xi g$, with $f$ an invertible matrix, and with $g in "GL"_s (hat(R)_2)$. We
write $xi approx f xi g$, and call $xi$ equivalent to $f xi g$. Thus we have
$
  vec(bold(F)_0, bold(F)_1, bold(F)_2, delim: "[") approx
  mat(
    delim: "[", bold(A)_0, 0, bold(A)_(02); 0, bold(A)_1, bold(A)_(12);
    Phi_1(x)bold(A)_(20), lambda bold(A)_(21), bold(A)_2
  )
  vec(bold(F)_0, bold(F)_1, bold(F)_2, delim: "[")bold(T),
$
with $bold(A)_0$, $bold(A)_1$, $bold(A)_2$ and $bold(T)$ invertible over
$hat(ZZ)$, $hat(R)_1$, $hat(E)$ and $hat(R)_2$, respectively.

This equivalence allows us to replace $bold(F)_0$ by
$bold(A)_0 bold(F)_0 bold(T)$. Since there are ring surjections
$hat(ZZ)->overline(ZZ)$, $hat(R)_2->overline(ZZ)$, which induce surjections of
groups of units, we can diagonalize $bold(F)_0$ and can bring it into the form
$ bold(F)_0=mat(bold(I), 0; 0, 0)^(a times s), $
where $bold(I)$ is a $w times w$ identity matrix for some $w$, $0<=w<=a$. If
$w<a$, then the last
#source(755)
$a-w$ copies of $hat(ZZ)$ split off as a direct summand of $hat(M)$,
contradicting our assumption that $s>0$ and $hat(M)$ is indecomposable.
Therefore $w=a<=s$, and we may write
#cyclic-extension-partition()
where the letters $a$, $b$, etc., show the number of rows or columns in the
various blocks of $bold(F)_0$, $bold(F)_1$ and $bold(F)_2$.

If $b>0$ and $bold(F)_1=0$, then $hat(R)_1^((b))$ is a summand of $hat(M)$, and
thus $hat(M)=hat(R)_1$, contradicting our assumption that $s>0$. Likewise,
$bold(F)_2!=0$ when $c>0$. If $b=c=0$, reduction of $bold(F)_0$ gives only
$hat(R)_2$ and $(hat(R)_2,hat(ZZ);1)$ as indecomposable possibilities, both
already included in the list below. We may therefore assume $b+c>0$. Each entry
of $bold(F)_1$ and $bold(F)_2$ may be written in the form $u lambda^k$, with $u$
a unit and $k>=0$; call $k$ the _exponent_ of the element $u lambda^k$. The
remainder of the discussion splits into four cases, depending on the location of
an element of smallest exponent among all of the entries of the matrices
$bold(F)_(11)$, $bold(F)_(12)$, $bold(F)_(21)$ and $bold(F)_(22)$.

_Case 1._ Suppose the smallest exponent $k$ occurs for an entry in
$bold(F)_(22)$. We may partition $bold(T)$ as
$
  bold(T)=mat(delim: "[", bold(T)_1, 0; bold(T)_(21), bold(T)_2), quad bold(T)_1
  in "GL"_a (hat(R)_2), quad
  bold(T)_2 in "GL"_(s-a)(hat(R)_2),
$
and thus after equivalence we may replace $bold(F)_(22)$ by
$bold(A)_2 bold(F)_(22)bold(T)_2$. Choosing $bold(A)_2$ and $bold(T)_2$
suitably, we may then assume that
$ bold(F)_(22)=mat(delim: "[", lambda^k, 0; 0, ast), $
with $k$ minimal as above.

In the equivalence $xi approx f xi$, we choose $f$ to be the matrix
$ mat(delim: "[", bold(I), 0, 0; 0, bold(I), bold(A)_(12); 0, 0, bold(I)). $
Since every entry of $bold(F)_(12)$ has exponent $>=k$, further equivalence
allows us to eliminate all entries of $bold(F)_(12)$ in its first column, by
choosing $bold(A)_(12)$ properly. Likewise, using
$ bold(T)=mat(delim: "[", bold(I), 0; bold(T)_(21), bold(I)) $
with suitable $bold(T)_(21)$, we can eliminate all entries in the first row of
$bold(F)_(21)$. Thus, we
#source(756)
obtain
$
  xi approx mat(
    delim: "[", augment: #(hline: (1, 2), vline: 1, stroke: (dash: "dashed")),
    bold(I), 0, 0; bold(F)_(11), 0, ast; 0, lambda^k, 0; ast, 0, ast
  ),
$
so $hat(M)$ decomposes, and the extension of $hat(R)_2$ by $hat(E)$
corresponding to the extension class $lambda^k in "Ext"(hat(R)_2,hat(E))$ splits
off as a summand of $hat(M)$. Denoting this extension by
$(hat(R)_2,hat(E);lambda^k)$, we see that it coincides with $hat(M)$, since
$hat(M)$ is indecomposable. Since $lambda^k$ is an element of $overline(E)$ in
this step, the exponent $k$ has the range $0<=k<p$, and each such $k$ gives an
indecomposable extension. We obtain $p$ non-isomorphic indecomposable extensions
in this way.

_Case 2._ Suppose that the smallest exponent $k$ occurs for an entry in
$bold(F)_(21)$, but not in $bold(F)_(22)$. Since
$
  xi approx mat(
    delim: "[", bold(A)_0 bold(T)_1, 0; ast, ast; bold(A)_2
    bold(F)_(21)bold(T)_1, ast
  ),
$
we may choose invertible matrices $bold(A)_0$, $bold(A)_2$ and $bold(T)_1$ so
that $bold(A)_0 bold(T)_1=bold(I)$ over $overline(ZZ)$, and $bold(F)_(21)$ has
the form
$ bold(F)_(21)=mat(delim: "[", lambda^k, 0; 0, ast). $
The entries of the first row of $bold(F)_(22)$ have exponent $>k$, so right
multiplication by
$ bold(T)=mat(delim: "[", bold(I), lambda bold(T)_(12); 0, bold(I)), $
with suitably chosen $bold(T)_(12)$, can be used to eliminate the first row of
$bold(F)_(22)$. Note that this procedure does not affect the top rows
$[bold(I) 0]$ of $xi$, since $bold(I) dot lambda bold(T)_(12)=0$ over
$overline(ZZ)$. This gives
$
  xi approx mat(
    delim: "[", augment: #(hline: (2, 3), vline: 2, stroke: (dash: "dashed")),
    1, 0, 0; 0, bold(I), 0; 0, ast, ast; lambda^k, 0, 0; 0, ast, ast
  ),
$
so again $hat(M)$ decomposes, and we obtain
$
  hat(M)=(hat(R)_2,hat(ZZ) plus.o hat(E);1 plus.o lambda^k),
  quad "where" 0<=k<=p-1.
$
#source(757)
However, the extension for which $k=p-1$ is decomposable. Indeed, we may write
$Phi_1(x)=lambda^(p-1)$ in $overline(E)$. Upon subtracting a suitable
$Phi_1(x)$-multiple of the first row of $bold(F)_0$ from the first row of
$bold(F)_2$ (which is permitted under our definition of equivalence), the corner
entry of $bold(F)_(21)$ becomes $0$. In other words, we have
$
  (hat(R)_2,hat(ZZ) plus.o hat(E);1 plus.o lambda^(p-1))
  tilde.equiv (hat(R)_2,hat(ZZ);1) plus.o hat(E).
$
Analogously, we obtain
$
  (hat(R)_2,hat(ZZ) plus.o hat(E);1 plus.o 1)
  tilde.equiv hat(ZZ) plus.o (hat(R)_2,hat(E);1).
$
It is easily verified that for $0<k<p-1$, the classes
$ xi=vec(1, lambda^k) in "Ext"(hat(R)_2,hat(ZZ) plus.o hat(E)) $
yield indecomposable $hat(Lambda)$-lattices, no two of which are isomorphic.
This can be shown by considering
$
  mat(delim: "[", a_0, b_0; Phi_1(x)b_2, a_2)vec(1, lambda^k) dot alpha,
  quad "where" a_0 in hat(ZZ)^dot, a_2 in hat(E)^dot,
  alpha in (hat(R)_2)^dot,
$
which can never be of the forms $vec(1, 0)$, $vec(0, 1)$, or $vec(1, lambda^l)$
with $l!=k$.

_Case 3._ Suppose the smallest $k$ occurs in $bold(F)_(12)$, and not in
$bold(F)_(21)$ or $bold(F)_(22)$. Subtracting suitable multiples of the columns
of $bold(F)_(12)$ from those of $bold(F)_(11)$, and suitable $lambda$-multiples
of the rows of $bold(F)_(12)$ from those of $bold(F)_(22)$, we eventually obtain
$ hat(M)=(hat(R)_2,hat(R)_1;lambda^k), quad 0<=k<=p-2, $
which is indecomposable. (Since $lambda^(p-1)=0$ in $overline(R)_1$, the upper
limit for $k$ must be $p-2$.)

_Case 4._ Suppose the smallest $k$ occurs in $bold(F)_(11)$, and not in
$bold(F)_(12)$, $bold(F)_(21)$ or $bold(F)_(22)$. As in Case~2, we may bring
$bold(F)_(11)$ into the form
$ bold(F)_(11)=mat(delim: "[", lambda^k, 0; 0, ast). $
We may then subtract $lambda$-multiples of the first row of $bold(F)_(11)$ from
the rows of $bold(F)_(21)$, under our equivalence procedure. We may also
subtract $lambda$-multiples of the first column of $bold(F)_(11)$ from the
columns of $bold(F)_(12)$, noting that the top rows of $xi$ are not affected by
this procedure because $lambda bold(I)=0$ over $overline(ZZ)$. The matrix $xi$
then decomposes, and we obtain
$
  hat(M) tilde.equiv (hat(R)_2,hat(ZZ) plus.o hat(R)_1;1 plus.o lambda^k),
  quad 0<=k<=p-2.
$

#source(758)
We collect our results in the following:

#theorem[
  There are precisely $4p+1$ non-isomorphic indecomposable $hat(ZZ)G$-lattices,
  where $hat(ZZ)$ is the ring of $p$-adic integers, and $G$ is cyclic of order
  $p^2$. These are given by#footnote[
    We follow the notation described in @eq:lattice-extension-notation, which
    differs from that in Reiner~@bib:Reiner1978.
  ]
  $ hat(ZZ),hat(R)_1,hat(E),hat(R)_2,(hat(R)_2,hat(ZZ);1), $
  $ (hat(R)_2,hat(E);lambda^k), quad 0<=k<=p-1, $
  $ (hat(R)_2,hat(ZZ) plus.o hat(E);1 plus.o lambda^k), quad 1<=k<=p-2, $
  $ (hat(R)_2,hat(R)_1;lambda^k), quad 0<=k<=p-2, $
  $ (hat(R)_2,hat(ZZ) plus.o hat(R)_1;1 plus.o lambda^k), quad 0<=k<=p-2. $
  #idx(
    "Berman-Gudivok Theorem",
    target: [@th:prime-square-cyclic-complete-lattice-classification],
  )#idx(
    "Heller-Reiner Theorem",
    target: [@th:prime-square-cyclic-complete-lattice-classification],
  )
] <th:prime-square-cyclic-complete-lattice-classification>

We may remark that all of these lattices can be embedded as ideals in
$hat(Lambda)$, except for the lattices of the form
$(hat(R)_2,hat(ZZ) plus.o hat(E);1 plus.o lambda^k)$. The $hat(ZZ)$-rank of
these last-named extensions is $p^2+1$, so they cannot be ideals in the group
ring $hat(ZZ)G$. Berman–Gudivok~@bib:Berman1964a give explicit matrix
representations of $G$ afforded by these $4p+1$ indecomposable lattices.
Butler~@bib:Butler1975 gives a completely different description of these
lattices (see also Wiedemann~@bib:Wiedemann1980). Berman~@bib:Berman1963,
@bib:Berman1966 classifies all groups $H$ whose indecomposable
$hat(ZZ)H$-lattices are isomorphic to ideals of $hat(ZZ)H$.
Berman–Gudivok~@bib:Berman1964a also treat the case where $G$ is cyclic of order
$p^kappa$, $kappa>=2$, and classify all indecomposable $hat(ZZ)G$-lattices which
are annihilated by $(x-1)Phi_i (x)Phi_kappa (x)$ for some fixed $i$,
$0<i<kappa$. There are finitely many such indecomposable lattices.

Let us turn now to a consideration of $ZZ G$-lattices. The results given below
are due to Reiner~@bib:Reiner1978. If $M$ is an indecomposable $ZZ G$-lattice,
then $hat(M)$ must be one of the indecomposable $hat(ZZ)G$-lattices listed
above. Given $hat(M)$, we can find all possible $M$'s by replacing extension
classes $lambda^k$ or $1 plus.o lambda^k$ by expressions such as $lambda^k u$,
$u_0 plus.o lambda^k u_1$, etc., where the $u$'s are units in rings such as
$overline(ZZ)$, $overline(R)_1$, and $overline(E)$. We then have the problem,
already encountered in
Theorem~@th:cyclic-p-locally-free-extension-classification, of deciding when two
indecomposable $M$'s are isomorphic, and of giving a full list of isomorphism
invariants of a direct sum of indecomposable $Lambda$-lattices.

Let us treat in detail the problem of finding all indecomposable $M$'s with
given $hat(M)$, for the most difficult case, that in which
$hat(M)=(hat(R)_2,hat(ZZ) plus.o hat(E);1 plus.o lambda^k)$, where $1<=k<=p-2$.
Let $frak(b)$ range over a full set of representatives of the $h_1$ ideal
classes of $R_1$, and $frak(c)$ over a corresponding set for the $h_2$ ideal
classes of $R_2$. For each $frak(b)$, let $E(frak(b))$ denote the locally free
$E$-lattice which is a non-split extension of $frak(b)$ by $ZZ$; in
@th:prime-cyclic-integral-lattice-classification, we denoted $E(frak(b))$ by
$(frak(b),ZZ;1)$. The discussion in @ss:cyclic-p-group-lattices, and at the
beginning of this subsection, shows at once that $M$ must
#source(759)
be (isomorphic to) an extension of $frak(c)$ by $ZZ plus.o E(frak(b))$, for some
$frak(b)$ and $frak(c)$, with extension class
$xi in "Ext"(frak(c),ZZ plus.o E(frak(b)))$. Further, choosing some standard
isomorphism
$
  "Ext"(frak(c),ZZ plus.o E(frak(b)))
  tilde.equiv "Ext"(R_2,ZZ plus.o E)
  tilde.equiv overline(ZZ) plus.o overline(E),
$
where bars denote reduction mod $p$, we can represent $xi$ as a column vector
$
  vec(m, lambda^k u), quad m in overline(ZZ)^dot, quad u in overline(E)^dot,
  quad 1<=k<=p-2.
$
A full set of isomorphism invariants of $M$ consists of the ideal classes of
$frak(b)$ and $frak(c)$, and the orbit of $xi$ under the actions of
$Aut(ZZ plus.o E)$ and $Aut R_2$.

The orbit of $xi$ consists of all column vectors $f xi s$, with
$f in Aut(ZZ plus.o E)$, $s in R_2^dot$. As shown in the proof of
@th:prime-cyclic-integral-lattice-classification, $R_2^dot$ maps onto
$overline(ZZ)^dot$, so we may find a new $xi$ in the same orbit for which $m=1$.
Thus we may take
$ xi=vec(1, lambda^k u) $
from now on, and we must decide when two different $xi$'s lie in the same orbit.
The complete solution to this question is given by:

#proposition[
  Let $xi=vec(1, lambda^k u)$, $xi'=vec(1, lambda^(k')u')$, where $1<=k,k'<=p-2$
  and $u,u' in overline(E)^dot$. Then $xi$ and $xi'$ lie in the same orbit if
  and only if
  #enum(
    numbering: "(i)",
    [$k=k'$,],
    [$u$ and $u'$ have the same image in $Omega_k$, where
      $
        Omega_k=(R')^dot slash "image of" R_1^dot, quad
        "with" R'=overline(ZZ)[lambda] slash (lambda^(p-1-k)),
      $],
    [For the case where $p equiv 1 mod 4$, the image of $u slash u'$ in
      $overline(ZZ)$ is a square.],
  )
] <prop:prime-square-complex-extension-orbits>
#proof[
  There is a fibre product diagram
  #extension-fibre-square()
  in which $mu_0$, $mu_1$ are canonical surjections. One important consequence
  of this
  #source(760)
  fact is the obvious result:
  $ mu_1{E^dot}={r in R_1^dot:r equiv plus.minus 1 mod lambda}, $
  where $lambda=1-omega_1$. We shall also need the fact (see
  Exercise~@exc:cyclotomic-unit-reduction-norm) that under the canonical
  surjection $theta:R_2->overline(R)_1$, the image of $R_2^dot$ is contained in
  the image of $R_1^dot$ in $(overline(R)_1)^dot$.

  As a special case of the discussion at the start of this subsection, we have
  $
    "End"(ZZ plus.o E)={f:f=mat(a, b; Phi_1(x)c, d),
      a,b in ZZ,c,d in E}.
  $
  By Exercise~@exc:cyclic-order-fibre-product-endomorphisms, $f$ induces the
  maps
  $
    f_0=mat(a, b; p mu_0(c), mu_0(d)) in "End"(ZZ plus.o ZZ), quad
    f_1=mu_1(d) in "End" R_1,
  $
  and $f in Aut(ZZ plus.o E)$ if and only if $f_0 in "GL"_2(ZZ)$ and
  $mu_1(d) in R_1^dot$. The condition that $xi$ and $xi'$ lie in the same orbit
  becomes
  $
    vec(1, lambda^(k')u')=mat(a, b; Phi_1(x)c, d)vec(1, lambda^k u)
    dot s
  $
  for some $f in Aut(ZZ plus.o E)$ and $s in R_2^dot$. This can be written as
  $
    a s=1 "in" overline(ZZ), quad
    lambda^(k')u'=(lambda^(p-1)c+d lambda^k u)s "in" overline(E),
  $
  <eq:complex-extension-orbit-equations>
  using the facts that $b lambda^k=0$ in $overline(ZZ)$ because $k>=1$, and that
  $Phi_1(x)=lambda^(p-1)$ in $overline(E)$. Since $k'<=p-2$, the second equation
  in @eq:complex-extension-orbit-equations cannot hold true if $k!=k'$, so for
  the rest of the proof we may assume that $k=k'$.

  Suppose now that @eq:complex-extension-orbit-equations holds for some
  $f in Aut(ZZ plus.o E)$ and some $s in R_2^dot$. Then in $overline(E)$ we have
  $ a d=a mu_0(d) equiv plus.minus 1 mod lambda, quad a s equiv 1 mod lambda, $
  and so
  $ u' equiv d u s equiv plus.minus a^(-2)u mod lambda. $
  If $p equiv 1 mod 4$, then for each $a in ZZ$ prime to $p$,
  $plus.minus a^(-2)$ is always a square mod $p$, which shows that $u slash u'$
  is a square in $overline(ZZ)$. Furthermore,
  $ lambda^k u'=mu_1(d)lambda^k u s "in" overline(R)_1. $
  Since $s=r$ in $overline(R)_1$ for some $r in R_1^dot$ by
  Exercise~@exc:cyclotomic-unit-reduction-norm, this shows that $u'$ and $u$
  have the same image in the group $Omega_k$ defined above. Therefore, if
  $xi approx xi'$, then conditions (i)–(iii) are satisfied.
  #source(761)
  Assume conversely that these conditions hold. We may write
  $u' equiv epsilon q^2 u mod lambda$ for some $q in ZZ$ prime to $p$ and
  $epsilon=plus.minus 1$, taking $epsilon=1$ when $p equiv 1 mod 4$. As in the
  proof of @th:prime-cyclic-integral-lattice-classification, we can then find
  $r in R_1^dot$, $s in R_2^dot$, such that $r equiv s equiv q mod lambda$. But
  then we can choose $f in Aut(ZZ plus.o E)$ such that $det f_0=epsilon$ and
  $mu_1(d)=epsilon r$. We then obtain $xi approx xi''$, where
  $
    xi''=vec(a s, lambda^k u''), quad "and"
    lambda^k u'' equiv lambda^k dot d u s mod lambda^(p-1).
  $
  Then
  $ a s equiv a q equiv epsilon d^(-1)q equiv r^(-1)q equiv 1 mod lambda, $
  so $a s=1$ in $overline(ZZ)$. Further,
  $ u'' equiv d u s equiv epsilon q^2 u equiv u' mod lambda, $
  and $u''$ and $u'$ have the same image in $Omega_k$. It remains for us to
  prove that
  $ xi'' approx xi'. $
  Since $u''$ and $u'$ have the same image in $Omega_k$, it follows that
  $ lambda^k u'' equiv lambda^k u' r mod lambda^(p-1)E $
  for some $r in R_1^dot$. But $r equiv 1 mod lambda$ because
  $u'' equiv u' mod lambda$, and thus by our earlier comments, $r=mu_1(d)$ for
  some $d in E^dot$. But then we can find $c in E$ such that
  $ lambda^k u''=Phi_1(x)c+lambda^k u'd "in" overline(E), $
  so now
  $
    xi'=vec(1, lambda^k u') approx
    mat(1, 0; Phi_1(x)c, d)vec(1, lambda^k u')=vec(
      1, lambda^k
      u''
    )=xi'',
  $
  which completes the proof that $xi approx xi'$, and establishes the
  proposition.
]

A similar discussion, considerably less complicated, can be carried out for each
of the other choices of $hat(M)$ in
@th:prime-square-cyclic-complete-lattice-classification. Indeed, in most of the
cases the desired information is obtained as a special case of
Theorem~@th:cyclic-p-locally-free-extension-classification; for details, see
Reiner~@bib:Reiner1978. The final result is as follows#footnote[
  We use the notation of @eq:lattice-extension-notation rather than that in
  Reiner~@bib:Reiner1978.
]:

#theorem[
  Let $R_i=ZZ[omega_i]$, $i=1,2$, where $omega_i$ is a primitive $p^i$-th root
  of unity over $QQ$. Let $frak(b)$ range over a full set of representatives of
  the $h_1$ ideal classes of $R_1$, and $frak(c)$ over the $h_2$ ideal classes
  of $R_2$. For each $frak(b)$, let $E(frak(b))$ be the non-split
  #source(762)
  extension of $frak(b)$ by $ZZ$. Let $n_0$ be some fixed quadratic non-residue
  (mod $p$), when $p equiv 1 mod 4$.

  Let
  $
    cases(
      U_m=(overline(ZZ)[lambda] slash (lambda^m))^dot
      slash "image of" R_1^dot quad 1<=m<=p-1,
      U_p=overline(E)^dot slash lr((("image of" E^dot)("image of" R_2^dot)))
    ).
  $
  <eq:cyclic-prime-square-unit-obstructions>
  For each $m$, $1<=m<=p$, let $tilde(U)_m$ denote a full set of representatives
  $u$, in $(overline(R)_1)^dot$ or $overline(E)^dot$, of the elements of the
  factor group $U_m$, where these $u$'s are chosen so that
  $u equiv 1 mod lambda$.

  Let $(frak(c),ZZ;1)$ denote an extension of $frak(c)$ by $ZZ$ with extension
  class $1$, and $(frak(c),ZZ plus.o E(frak(b));1 plus.o lambda^k u)$ an
  extension of $frak(c)$ by $ZZ plus.o E(frak(b))$ with extension class
  $1 plus.o lambda^k u$, and so on.

  Then a full list of non-isomorphic indecomposable $ZZ G$-lattices is as
  follows:
  #enum(
    numbering: "(a)",
    [$ZZ,frak(b),E(frak(b)),frak(c),(frak(c),ZZ;1)$.],
    [$(frak(c),E(frak(b));lambda^k u)$, $u in tilde(U)_(p-k)$, $0<=k<=p-1$.],
    [$(frak(c),ZZ plus.o E(frak(b));1 plus.o lambda^k u)$,
      $u in tilde(U)_(p-1-k)$, $1<=k<=p-2$.],
    [If $p equiv 1 mod 4$,
      $(frak(c),ZZ plus.o E(frak(b));1 plus.o lambda^k u n_0)$,
      $u in tilde(U)_(p-1-k)$, $1<=k<=p-2$.],
    [$(frak(c),frak(b);lambda^k u)$, $u in tilde(U)_(p-1-k)$, $0<=k<=p-2$.],
    [$(frak(c),ZZ plus.o frak(b);1 plus.o lambda^k u)$, $u in tilde(U)_(p-1-k)$,
      $0<=k<=p-2$.],
  )
  #idx(
    "Reiner's Theorem",
    target: [@th:prime-square-cyclic-integral-lattice-classification],
  )
] <th:prime-square-cyclic-integral-lattice-classification>

The groups $U_m$ defined in @eq:cyclic-prime-square-unit-obstructions are
extremely interesting, and measure obstructions to lifting units in the local
ring $overline(ZZ)[lambda] slash (lambda^m)$ to the global units occurring in
their definitions. This same question arises in the determination of the locally
free class group $"Cl"(ZZ G)$, where $G$ is a cyclic $p$-group (see Chapter~11
of Volume~II). We have $U_1={1}$, since the proof of
@th:prime-cyclic-integral-lattice-classification shows that $R_1^dot$ maps onto
$overline(ZZ)^dot$. Further, since $1-lambda=x in E^dot$, it follows at once
that $U_2={1}$.

If we put
$ E'=overline(ZZ)[lambda] slash (lambda^m), quad "where" 1<=m<=p, $
then the group $(E')^dot$ can be written as a direct product
$
  (E')^dot=overline(ZZ)^dot times chevron.l 1+lambda chevron.r times
  chevron.l 1+lambda^2 chevron.r times dots times
  chevron.l 1+lambda^(m-1) chevron.r.
$
The preceding discussion shows that the image of $R_2^dot$ covers the factor
$overline(ZZ)^dot$, so $U_m$ is always an elementary abelian $p$-group. This
group has been studied in detail by Galovich~@bib:Galovich1974,
Kervaire–Murthy~@bib:Kervaire1977, and Ullom~@bib:Ullom1977,
#source(763)
especially for the case where $p$ is a regular odd prime. Let us summarize their
results:

An odd prime $p$ is _regular_ if $p divides.not h_1$, where $h_1$ is the ideal
class number of $R_1$ (see Borevich–Shafarevich~@bib:Borevich1966). #idx(
  "regular prime",
) If $p$ is regular and $1<=m<=p-1$, then the image $R_1^*$ of $R_1^dot$ in
$(E')^dot$ is given by
$
  R_1^*=overline(ZZ)^dot times chevron.l 1+lambda chevron.r times
  product_(i=1)^(floor((m-1)/2))
  chevron.l 1+lambda^(2i)+alpha_i lambda^(2i+1) chevron.r
$
for some $alpha$'s in $E'$.#ed-note[
  The ordinary polynomial reduction from $R_1$ is not defined when $m=p$:
  $Phi_1(1-lambda)=lambda^(p-1)!=0$ in $overline(ZZ)[lambda] slash (lambda^p)$.
  For $U_p$, use the earlier definition through the unit images of $E$ and
  $R_2$. Its order formula at this endpoint requires the cited arithmetic
  results.
] The cited results give $U_m$ elementary abelian of order $p^(f(m))$, where
$ f(m)=floor((m-2)/2) quad ("interpreted as" 0 "if" m<2). $
To test for regularity of $p$, one considers the Bernoulli numbers
$B_1,B_2,dots$. Let $delta(k)$ be the number of $B$'s among $B_1,dots,B_k$ whose
numerator is divisible by $p$. Then $p$ is regular if and only if
$delta((p-3)/2)=0$. On the other hand, we call $p$ _properly irregular_ if
$p divides h_1$ but $p$ does not divide the ideal class number of
$ZZ[omega_1+overline(omega)_1]$.#idx("properly irregular prime") For such $p$,
one must omit from the formula for $R_1^*$ all those factors for which $2i<=p-3$
and the numerator of $B_i$ is a multiple of $p$. For each properly irregular
$p$, the cited results give $U_m$ as an elementary abelian $p$-group of order
$p^(g(m))$, where
$
  g(m)=cases(
    floor((m-2)/2)+delta(floor((m-1)/2)) comma & quad 0<=m<=p-2,
    (p-3)/2+delta((p-3)/2) comma & quad m=p-1 comma p
  ).
$
As far as is now known, every odd prime is either regular or properly irregular.
Thus, the groups $U_m$ occurring in
@th:prime-square-cyclic-integral-lattice-classification may be regarded as
known.

Let us conclude this subsection with some observations about direct sums of
indecomposable $ZZ G$-lattices. Suppose that $1<=k<=p-2$, and let $u in E$ have
image $overline(u) in overline(E)^dot$. We consider the exact sequences with
indicated extension classes:
#extension-unit-change()
The commutativity of the diagram gives rise to an exact sequence
$
  0->(R_2,ZZ plus.o E;1 plus.o lambda^k)
  ->(R_2,ZZ plus.o E;1 plus.o lambda^k overline(u))->E slash u E->0.
$
But also
$ 0->E arrow.r^u E->E slash u E->0 $
#source(764)
is exact, so by @prop:genus-schanuel we obtain
$
  (R_2,ZZ plus.o E;1 plus.o lambda^k overline(u)) plus.o E
  tilde.equiv (R_2,ZZ plus.o E;1 plus.o lambda^k) plus.o E.
$
(Other formulas of this nature are given in @eq:genus-absorption and
@eq:genus-exchange.)

A systematic use of this procedure enables us to reduce a direct sum of
indecomposable lattices to some sort of canonical form. In this manipulation,
all of the ideals ${frak(b)}$ can be concentrated into a single summand, being
replaced by $R_1$ in all other summands. The same holds for the $frak(c)$'s and
the $E(frak(b))$'s. Further, all of the units ${u}$ can be eliminated, except
possibly for a single summand. The end result, too complicated to state here,
gives a full list of invariants for the isomorphism class of a direct sum of
indecomposable $ZZ G$-lattices. For details, see Reiner~@bib:Reiner1978. This
procedure has been generalized somewhat by Jones~@bib:Jones1980.

For the case where $G$ is cyclic of order $p^kappa$, $kappa>=2$,
Berman–Gudivok~@bib:Berman1964a obtained all indecomposable $hat(ZZ)G$-lattices
$hat(M)$ for which $hat(QQ)hat(M)$ has only three types of simple summands,
namely $hat(QQ)$, $hat(QQ)(omega_i)$ and $hat(QQ)(omega_j)$, with
$1<=i<j<=kappa$.

=== An Order in a Matrix Algebra <ss:matrix-order-drozd-turcin>

We devote this subsection to the Drozd–Turčin~@bib:Drozd1967d example considered
in @exm:matrix-order-characteristic-sublattice above, and keep the notation
introduced there. We shall classify all indecomposable genera of
$Lambda$-lattices, and shall exhibit a $Lambda$-lattice $M$ such that
$g(M)>g(Lambda)$, where $g(M)$ denotes the number of isomorphism classes of
$Lambda$-lattices in the genus of $M$. This provides a negative answer to a
question of Roiter (see @rem:genus-bounds-nonseparable-algebras(ii)).#idx(
  "Drozd-Turčin Theorem",
  target: [@ss:matrix-order-drozd-turcin],
)

Starting with a prime $p$, we set
$
  Lambda=ZZ dot bold(I)+p Lambda', quad Lambda'=M_2(ZZ), quad
  L={vec(a, b):a,b in ZZ},
$
so $L$ is a left $Lambda'$-lattice for which $QQ L$ is a simple
$M_2(QQ)$-module. The ring isomorphism
$Lambda slash p Lambda' tilde.equiv overline(ZZ)=ZZ slash p ZZ$ is given by
$
  mat(a, b; c, d)+p Lambda' |->a "in" overline(ZZ), quad
  "for all" mat(a, b; c, d) in Lambda.
$
We showed in @exm:matrix-order-characteristic-sublattice that every
$Lambda$-lattice $M$ is an extension
#named-equation(name: [$(xi)$])[$ 0->L^((r))->M->overline(ZZ)^((s))->0, $]
<eq:matrix-order-extension-sequence>
and the isomorphism invariants of $M$ are the integers $r$ and $s$, and the
orbit of $xi$ in $"Ext"(overline(ZZ)^((s)),L^((r)))$ under the actions of
$Aut L^((r))$ and $Aut overline(ZZ)^((s))$. We note also that the genus of $M$
is completely determined by the $hat(Lambda)$-lattice $hat(M)$, by
@prop:genus-nonmaximal-primes, and that just as in
@lem:cyclic-p-lattice-completion-indecomposable, $M$ is indecomposable if and
only if $hat(M)$ is indecomposable.

#source(765)
Let us calculate $"Ext"(overline(ZZ),L)$, where $"Ext"$ means $"Ext"_Lambda^1$.
The exact sequence $0->p Lambda'->Lambda->overline(ZZ)->0$ gives
$
  "Ext"(overline(ZZ),L) tilde.equiv Hom_Lambda (p Lambda',L)
  slash "image of" Hom_Lambda (Lambda,L).
$
But by Exercise~@exc:overorder-lattice-homomorphisms,
$ Hom_Lambda (p Lambda',L)=Hom_(Lambda')(p Lambda',L) tilde.equiv L, $
and under this isomorphism, the image of $Hom_Lambda (Lambda,L)$ is equal to
$p L$. Therefore
$
  "Ext"(overline(ZZ),L) tilde.equiv L slash p L
  tilde.equiv overline(ZZ) plus.o overline(ZZ).
$
It follows at once that
$
  "Ext"(overline(ZZ)^((s)),L^((r)))
  tilde.equiv (overline(ZZ) plus.o overline(ZZ))^(r times s),
$
the $overline(ZZ)$-vector space consisting of all $r times s$ matrices over
$overline(ZZ) plus.o overline(ZZ)$. Each
$xi in "Ext"(overline(ZZ)^((s)),L^((r)))$ is therefore expressible as
$xi=(bold(F)_1,bold(F)_2)$, where $bold(F)_1,bold(F)_2$ are a pair of
$r times s$ matrices over $overline(ZZ)$. In order to describe the actions of
$Aut overline(ZZ)^((s))$ and $Aut L^((r))$ on $xi$, we note that
$
  Aut_Lambda overline(ZZ)^((s))=Aut_(overline(ZZ))overline(ZZ)^((s))
  tilde.equiv "GL"_s (overline(ZZ)),
$
$ Aut_Lambda L^((r))=Aut_(Lambda')L^((r))="GL"_r (ZZ). $
If $xi'=(bold(F)'_1,bold(F)'_2)$, then $xi$ and $xi'$ lie in the same orbit
(notation: $xi approx xi'$) if and only if $xi'=bold(X) xi bold(Y)$ for some
$bold(X) in "GL"_r (ZZ)$, $bold(Y) in "GL"_s (overline(ZZ))$, that is,
$
  bold(F)'_1=bold(X) bold(F)_1 bold(Y), quad bold(F)'_2=bold(X) bold(F)_2
  bold(Y) "for some"
  bold(X) in "GL"_r (ZZ), bold(Y) in "GL"_s (overline(ZZ)).
$
<eq:matrix-order-global-pair-equivalence>
The lattice $M$ corresponding to $xi$ is decomposable if and only if we can
write $xi approx xi_1 plus.o xi_2$ for some $xi_1=(bold(G)_1,bold(G)_2)$,
$xi_2=(bold(H)_1,bold(H)_2)$, that is
$
  (bold(F)_1,bold(F)_2) approx lr(
    (mat(
        bold(G)_1, 0; 0,
        bold(H)_1
      ),mat(bold(G)_2, 0; 0, bold(H)_2))
  ).
$
<eq:matrix-pair-direct-sum>
The genus of $M$ is determined by an analogous argument, the only difference
being that in @eq:matrix-order-global-pair-equivalence, we let
$bold(X) in "GL"_r (hat(ZZ))$. Since the map
$"GL"_j (hat(ZZ))->"GL"_j (overline(ZZ))$ is surjective for each $j$, it follows
that the genus of $M$ is determined by the orbit of
$xi in (overline(ZZ) plus.o overline(ZZ))^(r times s)$ under the actions of
$"GL"_r (overline(ZZ))$ and $"GL"_s (overline(ZZ))$.

We are thus led to the well-known problem of classifying matrix pairs
$(bold(F)_1,bold(F)_2)$ over a field $overline(ZZ)$, under the equivalence
relation
$
  (bold(F)_1,bold(F)_2) approx (bold(X) bold(F)_1 bold(Y),bold(X) bold(F)_2
    bold(Y)) "for"
  bold(X) in "GL"_r (overline(ZZ)), bold(Y) in "GL"_s (overline(ZZ)).
$
<eq:matrix-pair-field-equivalence>
#source(766)
The indecomposable genera of $Lambda$-lattices are in bijective correspondence
with the indecomposable matrix pairs, where decomposability of a matrix pair is
defined as in @eq:matrix-pair-direct-sum.

We shall now state the Kronecker–Weierstrass Theorem, which gives a complete
list of inequivalent indecomposable matrix pairs over an arbitrary field $K$.
Proofs may be found in Dieudonné~@bib:Dieudonne1946 or
Gantmacher~@bib:Gantmacher1960, Chapter~XII.

#theorem(name: "Kronecker–Weierstrass Theorem")[
  Let $bold(F)_1,bold(F)_2$ be a pair of $r times s$ matrices over a field $K$.
  Equivalence of pairs is defined by @eq:matrix-pair-field-equivalence, and
  decomposability by @eq:matrix-pair-direct-sum. The following is a full list of
  inequivalent indecomposable pairs:
  #enum(
    numbering: "(i)",
    [$bold(F)_1=bold(I)$, $bold(F)_2="companion matrix of" (h(x))^m$, where
      $h(x)$ ranges over all irreducible polynomials in $K[x]$, and $m$ over all
      positive integers.],
    [For each $m>=1$,
      $
        bold(F)_1=mat(
          delim: "[",
          0, 1, 0, dots.h, 0; 0, 0, 1, dots.h, 0;
          dots.h, dots.h, dots.h, dots.h, dots.h;
          0, 0, 0, dots.h, 1; 0, 0, 0, dots.h, 0
        )^(m times m), quad bold(F)_2=bold(I)^(m times m).
      $],
    [For each $m>=1$,
      $
        bold(F)_1=[bold(I) 0]^(m times (m+1)), quad bold(F)_2=[0 bold(I)]^(m
        times (m+1)),
      $
      where $0$ is an $m times 1$ column vector of $0$'s.],
    [For each $m>=1$,
      $
        bold(F)_1=vec(bold(I), 0, delim: "[")^((m+1)times m),
        quad bold(F)_2=vec(
          0,
          bold(I), delim: "["
        )^((m+1)times m),
      $
      where $0$ is a $1 times m$ row vector of $0$'s.],
  )
  #idx(
    "Kronecker-Weierstrass Theorem",
    target: [@th:kronecker-weierstrass-matrix-pairs],
  )
] <th:kronecker-weierstrass-matrix-pairs>

Let us apply this theorem to the classification of $Lambda$-lattices. Since
$p Lambda' tilde.equiv L^((2))$, the exactness of the sequence
$ 0->p Lambda'->Lambda->overline(ZZ)->0 $
shows that the extension class of $Lambda$ corresponds to a pair of $2 times 1$
matrices over $overline(ZZ)$. But $hat(Lambda)$ is indecomposable, since
$hat(Lambda) slash "rad" hat(Lambda)
=hat(Lambda) slash p hat(Lambda)' tilde.equiv overline(ZZ)$. The genus of
$Lambda$ thus corresponds to the pair
$ xi_0=lr((vec(1, 0),vec(0, 1))) $
#source(767)
in the above list. Each $Lambda$-lattice $M$ in the genus of $Lambda$ thus
yields a pair
$ xi=lr((vec(a, b),vec(c, d))) $
with entries in $overline(ZZ)$, such that $xi$ is equivalent to $xi_0$ over
$overline(ZZ)$. (This occurs if and only if $a d-b c!=0$ in $overline(ZZ)$.) If
$M' or.curly Lambda$ yields the pair
$ xi'=lr((vec(a', b'),vec(c', d'))), $
then $M tilde.equiv M'$ if and only if $xi approx xi'$, that is
$
  vec(a', b')=bold(X) vec(a, b)y, quad vec(c', d')=bold(X) vec(c, d)y
  "for some" bold(X) in "GL"_2(ZZ), y in overline(ZZ)^dot.
$
Hence $xi approx xi'$ if and only if
$
  mat(a', c'; b', d')=bold(X) mat(a, c; b, d)y
  "for some" bold(X) in "GL"_2(ZZ), y in overline(ZZ)^dot.
$
<eq:matrix-order-principal-genus-equivalence>
This equation yields
$
  abs(mat(delim: #none, a', c'; b', d'))=plus.minus y^2
  abs(mat(delim: #none, a, c; b, d)).
$
<eq:matrix-order-principal-genus-determinants>
Conversely, it is easily verified that if
@eq:matrix-order-principal-genus-determinants holds for some
$y in overline(ZZ)^dot$, then @eq:matrix-order-principal-genus-equivalence holds
for some $bold(X)$. It follows at once that the number $g(Lambda)$ of
isomorphism classes in the principal genus (that is, the genus of $Lambda$) is
given by the index
$ g(Lambda)=|overline(ZZ)^dot:{plus.minus q^2:q in overline(ZZ)^dot}|. $
Therefore
$ g(Lambda)=cases(2 comma & quad p equiv 1 mod 4, 1 comma & quad "otherwise"). $

We shall now choose a $Lambda$-lattice $M$ for which $g(Lambda)<g(M)$. Let
$h(x) in overline(ZZ)[x]$ be irreducible, and let $bold(F)_2$ be the companion
matrix of $(h(x))^m$. Let us write $n=m d$, where $d$ is the degree of $h(x)$.
Then $bold(F)_2$ is an $n times n$ matrix over $overline(ZZ)$. Choose $M$ to be
the $Lambda$-lattice corresponding to the extension class
$xi=(bold(I),bold(F)_2)$. Each $M'$ in the genus of $M$ determines a class
$xi'=(bold(G)_1,bold(G)_2)$, and under the equivalence in
@eq:matrix-order-global-pair-equivalence (which does not affect the isomorphism
class of $M'$), we may assume that $bold(G)_1=bold(I)$. The condition that
$M' or.curly M$ then is equivalent to the assertion that $bold(G)_2$ is similar
to $bold(F)_2$ over the field $overline(ZZ)$. Thus, the $Lambda$-lattices $M'$
in the genus of $M$ determine extension classes $xi'=(bold(I),bold(G))$, with
$bold(G)$ similar to $bold(F)_2$ over $overline(ZZ)$.

#source(768)
In order to calculate $g(M)$, we must decide when
$(bold(I),bold(G)) approx (bold(I),bold(G)')$ where both $bold(G),bold(G)'$ are
similar to $bold(F)_2$ over $overline(ZZ)$. The reader will easily verify that
the image of $"GL"_n (ZZ)$ in $"GL"_n (overline(ZZ))$ is precisely the subgroup
${bold(T) in "GL"_n (overline(ZZ)):det bold(T)=plus.minus 1}$. It follows from
@eq:matrix-order-global-pair-equivalence that
$
  (bold(I),bold(G)) approx (bold(I),bold(G)') <==> bold(G)'=bold(T) bold(G)
  bold(T)^(-1) "for some"
  bold(T) in "GL"_n (overline(ZZ)) "such that" det bold(T)=plus.minus 1.
$
Now we may write
$
  bold(G)=bold(B) bold(F)_2 bold(B)^(-1), quad bold(G)'=bold(B)'bold(F)_2
  bold(B)'^(-1), quad
  "with" bold(B),bold(B)' in "GL"_n (overline(ZZ)).
$
The equation $bold(G)'=bold(T) bold(G) bold(T)^(-1)$ is equivalent to
$
  bold(T) bold(B)=bold(B)'bold(S) "for some" bold(S) "which commutes with"
  bold(F)_2.
$
Let $Gamma$ be the subgroup of $"GL"_n (overline(ZZ))$ generated by
${bold(T):det bold(T)=plus.minus 1}$ and all $bold(S) in "GL"_n (overline(ZZ))$
which commute with $bold(F)_2$. Since the first of these groups is normal in
$"GL"_n (overline(ZZ))$, we conclude at once that
$
  (bold(I),bold(G)) approx (bold(I),bold(G)') "if and only if" bold(B)' in
  bold(B) Gamma.
$
Therefore we obtain
$ g(M)=|"GL"_n (overline(ZZ)):Gamma|, $
and since $Gamma$ contains $"SL"_n (overline(ZZ))$, this gives
$
  g(M)=|overline(ZZ)^dot:det Gamma|, quad "where"
  det Gamma=chevron.l {det gamma:gamma in Gamma} chevron.r.
$
We now calculate $det Gamma$, and for this purpose we must compute $det bold(S)$
for each $bold(S) in "GL"_n (overline(ZZ))$ which commutes with $bold(F)_2$.
Since $bold(F)_2$ is the companion matrix of $(h(x))^m$ with $h(x)$ irreducible,
it follows from linear algebra that $bold(S)=theta(bold(F)_2)$ for some
polynomial $theta(x) in overline(ZZ)[x]$. If ${alpha_1,dots,alpha_d}$ are the
zeros of $h(x)$ in some splitting field $E$ over $overline(ZZ)$, then the
eigenvalues of $bold(S)$ are the ${theta(alpha_i)}$, each with multiplicity $m$.
Therefore
$
  det bold(S)=lr({product_(i=1)^d theta(alpha_i)})^m
  ={N(theta(alpha_1))}^m,
$
where $N:E->overline(ZZ)$ is the norm map (see @sec:dedekind-domains). But this
norm map $N$ is surjective (see @bib:Reiner1975[MO], proof of Theorem 14.1, for
example). Consequently
$ det Gamma={plus.minus u^m:u in overline(ZZ)^dot}. $
For odd $p$, the cyclicity of $overline(ZZ)^dot$ gives
$ g(M)=gcd(m, (p-1) slash 2). $
Thus $g(M)$ depends only upon $m$, and not upon the choice of $h(x)$.

We may now choose $p$ and $m$ so that $g(M)$ is large. For example, let $p$ be a
#source(769)
large prime, and let $m$ be some divisor of $(p-1) slash 2$. Then $-1$ is an
$m$-th power in $overline(ZZ)^dot$, since $-1$ is always a $(p-1) slash 2$-th
power. Therefore
$ g(M)=|overline(ZZ)^dot:{u^m:u in overline(ZZ)^dot}|=m $
in this case. In particular, $g(M)>g(Lambda)$ in most circumstances. For
instance, if $p=17$ and $m=8$, then $g(M)=8$ while $g(Lambda)=2$.

To conclude this discussion, we remark that for odd $p$, $g(M)<=(p-1) slash 2$
for all $m>=1$. Further, $g(M)=1$ for $p=2$ and all $m>=1$. The same statements
also hold for indecomposable $Lambda$-lattices which correspond to other choices
of indecomposable matrix pairs listed in the Kronecker–Weierstrass Theorem. For
further reading on this topic, see Drozd–Kirichenko~@bib:Drozd1967a and
Kirichenko~@bib:Kirichenko1970, as well as the original article by
Drozd–Turčin~@bib:Drozd1967d.

=== Dihedral and Metacyclic Groups
<ss:dihedral-metacyclic-integral-representations>

Let $G$ be the metacyclic group defined by
$ G=chevron.l x,y:x^p=1,y^q=1,y x y^(-1)=x^r chevron.r, $
where $p$ and $q$ are distinct primes, $p$ odd, and where $r$ is a primitive
$q$-th root of $1$ mod $p$. Clearly $q divides (p-1)$, and for the special case
where $q=2$, $G$ is the dihedral group of order $2p$. We shall find all
indecomposable $ZZ G$-lattices, apart from questions involving units in rings of
algebraic integers. The results are due to Pu~@bib:Pu1965; the special case
$q=2$ was treated earlier by Lee~@bib:Lee1964. #idx(
  "metacyclic group",
  target: [@ss:dihedral-metacyclic-integral-representations],
)#idx(
  "group",
  "metacyclic",
)

Let $R=ZZ[zeta]$, $K=QQ(zeta)$, where $zeta$ is a primitive $p$-th root of $1$
over $QQ$. Define $sigma in Aut_QQ K$ by $sigma(zeta)=zeta^r$, and let $K_0$ be
the subfield of $K$ fixed by $sigma$. Then $K$ is a Galois extension of $K_0$ of
degree $q$, with Galois group $chevron.l sigma chevron.r$. We set
$R_0=R inter K_0="alg. int."{K_0}$. Now let $H=chevron.l y chevron.r$ be cyclic
of order $q$, and form the twisted group algebra $K compose H$, with $y$ acting
as $sigma$ on $K$. By @exm:galois-twisted-group-algebra,
$K compose H tilde.equiv M_q (K_0)$. The rational prime $p$ is completely
ramified in $K$ (see @prop:prime-power-cyclotomic-ramification), and we have
$
  p R=P^(p-1), quad P=(1-zeta)R, quad
  p R_0=P_0^((p-1)/q), quad P_0 R=P^q,
$
where $P_0$ and $P$ are prime ideals of $R_0$ and $R$, respectively. Thus $P_0$
is the _only_ prime ideal of $R_0$ ramified in $R$ (by
@prop:cyclotomic-unramified-primes), and
$ R slash P tilde.equiv R_0 slash P_0 tilde.equiv ZZ slash p ZZ=overline(ZZ). $
Since $dim_(K_0)K=q$, it follows that $R$ is tamely ramified over $R_0$ (see
Exercise~@exc:tame-ramification-trace), so by @th:twisted-group-ring-heredity
and the discussion following it, $R compose H$ is a hereditary $R_0$-order in
$K compose H$.

#source(770)
Let the subscripts $p$ and $q$ denote _localization_. From the fibre product
diagram
#numbered-block[#metacyclic-fibre-square()]
<eq:metacyclic-integral-fibre-product>
we have $ZZ_q G tilde.equiv R_q compose H plus.o ZZ_q H$. Since $R_q$ is
unramified over $(R_0)_q$, it follows from @sec:twisted-group-rings that the
order $R_q compose H$ is maximal, and hence#footnote[
  This follows readily from @prop:genus-nonmaximal-primes and the fact that
  $(R_0)_q$ is semilocal (see proof of @prop:genus-semilocal-isomorphism, for
  example).
] there is (up to isomorphism) a unique indecomposable
$(R_q compose H)$-lattice, namely $R_q$ itself. (Note that $K$ is a simple
$(K compose H)$-module.) Furthermore, $ZZ_q H$ is a local ring, and by
@th:prime-cyclic-integral-lattice-classification its indecomposable lattices are
$ZZ_q$, $S_q$ and $ZZ_q H$, where $S=ZZ[theta]$ and $theta$ is a primitive
$q$-th root of $1$ over $QQ$. A full list of indecomposable $(ZZ_q G)$-lattices
is therefore given by
$ ZZ_q, quad S_q, quad ZZ_q H, quad R_q. $
<eq:metacyclic-localized-indecomposable-lattices>

The study of $ZZ_p G$-lattices#footnote[
  The analogous problem of finding all $overline(ZZ)G$-modules was treated in
  @prop:cyclic-normal-sylow-indecomposables and
  @prop:cyclic-kernel-frobenius-indecomposables.
] is somewhat more difficult, and here we will find it more convenient to
consider $hat(ZZ)G$-lattices, where $hat(ZZ)$ is the $p$-adic completion of
$ZZ$. Since $chevron.l x chevron.r$ is a Sylow $p$-subgroup of $G$, the proof of
@prop:finite-type-sylow-reduction shows that every indecomposable
$hat(ZZ)G$-lattice is a summand of $X^G$, for some indecomposable
$hat(ZZ)[x]$-lattice $X$. By @th:prime-cyclic-integral-lattice-classification,
there are just three choices for $X$: $X=hat(ZZ)$ on which $x$ acts as $1$;
$X=hat(R)=hat(ZZ)[zeta]$ on which $x$ acts as multiplication by $zeta$; and
$X=hat(ZZ)[x]$ itself. Now
$ hat(ZZ)^G=hat(ZZ)G times.o_(hat(ZZ)[x])hat(ZZ) tilde.equiv hat(ZZ)H, $
where $x$ acts as $1$ on $hat(ZZ)H$. Since $x^(p-1)-1$ splits into distinct
linear factors over $overline(ZZ)$, it follows from Hensel's Lemma
(Exercise~@exc:hensel-factorization) that $hat(ZZ)$ contains the $(p-1)$-st
roots of $1$. Thus $theta in hat(ZZ)$, and since $|H|=q in (hat(ZZ))^dot$, we
obtain a $hat(ZZ)G$-isomorphism
$ hat(ZZ)H tilde.equiv product.co_(i=0)^(q-1)hat(ZZ)_i. $
Here, $x$ acts as $1$ on each summand, while $y$ acts as $theta^i$ on
$hat(ZZ)_i$. Furthermore, we may assume that $theta$ was chosen originally to be
that (unique) primitive $q$-th root of $1$ for which
$theta equiv r mod p hat(ZZ)$. In this case, we have
$overline(theta)=overline(r)$ in $overline(ZZ)$, a fact needed in the discussion
below.

#source(771)
Turning next to the case where $X=hat(R)$, we have
$hat(R)^G tilde.equiv hat(R) compose H$ as $hat(ZZ)G$-modules, with $hat(ZZ)G$
acting on $hat(R) compose H$ by means of the surjection in
@eq:metacyclic-integral-fibre-product. Now
$
  (hat(R) compose H) slash "rad"(hat(R) compose H)
  tilde.equiv (hat(R) compose H) slash (hat(P) compose H)
  tilde.equiv overline(ZZ)H,
$
since $hat(R) slash hat(P) tilde.equiv overline(ZZ)$ on which $H$ acts
trivially. However,
$overline(ZZ)H tilde.equiv product.co_(i=0)^(q-1)overline(ZZ)_i$, with
$overline(ZZ)_i=overline(ZZ)$ and $y$ acting as $overline(theta)^i$ on
$overline(ZZ)_i$. It follows that the ring $hat(R) compose H$ must decompose
into a direct sum of $q$ non-isomorphic indecomposable projective modules. By
the discussion in @sec:twisted-group-rings following the proof of
@exm:prime-cyclotomic-twisted-hereditary-order, the ambiguous ideals
${hat(P)^k:0<=k<=q-1}$ are such a set of projective
$(hat(R) compose H)$-modules, and so we obtain
$ hat(R) compose H tilde.equiv product.co_(i=0)^(q-1)hat(P)^i. $
Note that for each $i$, $hat(P)^i$ is a $hat(ZZ)G$-lattice on which $x$ acts as
multiplication by $zeta$, and $y$ acts as the automorphism $sigma$. Further, it
easily is verified that
$hat(P)^i slash (1-x)hat(P)^i tilde.equiv overline(ZZ)_i$ as
$overline(ZZ)H$-modules. (This uses the fact that $overline(theta)=overline(r)$
in $overline(ZZ)$.)

Finally we treat the case where $X=hat(ZZ)[x]$, so
$
  X^G=hat(ZZ)G=hat(ZZ)G times.o_(hat(ZZ)H)hat(ZZ)H
  tilde.equiv product.co_(i=0)^(q-1)hat(ZZ)_i^G.
$
Let us show that for each $i$, $0<=i<=q-1$, the $hat(ZZ)G$-module $hat(ZZ)_i^G$
is indecomposable, and is a non-split extension of the $hat(ZZ)G$-lattice
$hat(ZZ)_i$ by the $hat(ZZ)G$-lattice $hat(P)^(i+1)$. We start with the exact
sequence of $hat(ZZ)G$-lattices
$ 0->(x-1)hat(ZZ)[x]->hat(ZZ)[x]->hat(ZZ)->0, $
where $y$ acts by conjugation on the first two lattices, and acts as $1$ on
$hat(ZZ)$. Now the cyclotomic polynomial $x^(p-1)+dots+x+1$ annihilates
$(x-1)hat(ZZ)[x]$, so $x$ acts as $zeta$ on this lattice. Further, if we put
$L=(x-1)hat(ZZ)[x]$, then $y$ acts as $overline(theta)$ on $L slash (x-1)L$. It
follows that $L tilde.equiv hat(P)$ as $hat(ZZ)G$-lattices, and $L$ is
indecomposable. The above sequence can now be written as
$ 0->hat(P)->hat(ZZ)[x]->hat(ZZ)->0, $
<eq:metacyclic-augmentation-extension>
and the sequence is non-split by @cor:p-group-ring-local-base. We now apply
$ast times.o_(hat(ZZ))hat(ZZ)_i$ to the above, obtaining a new exact sequence of
inner tensor products of $hat(ZZ)G$-lattices
$
  0->hat(P) times.o hat(ZZ)_i->hat(ZZ)[x] times.o hat(ZZ)_i
  ->hat(ZZ)_i->0, quad 0<=i<=q-1.
$
It is easily verified that $hat(P) times.o hat(ZZ)_i tilde.equiv hat(P)^(i+1)$
as $hat(ZZ)G$-modules; this follows from checking the action of $y$ on both
sides. The sequence is non-split, since we can recover
@eq:metacyclic-augmentation-extension from it by tensoring with $hat(ZZ)_(q-i)$.
Further, $hat(ZZ)[x] times.o hat(ZZ)_i
tilde.equiv hat(ZZ)_i^G$ by
#source(772)
Frobenius Reciprocity, so we obtain non-split exact sequences of
$hat(ZZ)G$-lattices
$ 0->hat(P)^(i+1)->hat(ZZ)_i^G->hat(ZZ)_i->0, quad 0<=i<=q-1. $
<eq:metacyclic-complete-induced-extension>
The above remarks show that there are exactly $3q$ non-isomorphic indecomposable
$hat(ZZ)G$-lattices, namely the following:
$ hat(ZZ)_i, quad hat(P)^i, quad hat(ZZ)_i^G, quad 0<=i<=q-1. $
<eq:metacyclic-complete-indecomposable-list>

We are now ready to consider $ZZ G$-lattices $M$. For each $M$, let
$L={m in M:Phi(x)m=0}$, where $Phi(x)$ is the cyclotomic polynomial of order
$p$. There is then an exact sequence of $ZZ G$-lattices
#named-equation(name: [$(xi)$])[$ 0->L->M->N->0 $]
<eq:metacyclic-global-extension-sequence>
in which $L$ is an $(R compose H)$-lattice and $N$ is a $ZZ H$-lattice. The
isomorphism class of $M$ is completely determined by those of $L$ and $N$, and
by the orbit of $xi$ in $"Ext"(N,L)$ under the actions of $Aut L$ and $Aut N$.

The lattice $N$ is completely known by
@th:prime-cyclic-integral-lattice-classification, namely, $N$ is a direct sum of
modules $ZZ$, $frak(a)$, and non-split extensions of $frak(a)$ by $ZZ$, with
$frak(a)$ ranging over a full set of representatives of the $h_S$ ideal classes
of $S$, where $S=ZZ[theta]$ and $theta$ is a primitive $q$-th root of $1$ over
$QQ$. The discussion in @sec:twisted-group-rings, leading to the formula
@eq:ambiguous-ideal-steinitz-transfer and its list of isomorphism invariants,
shows that the $(R compose H)$-lattice $L$ may be expressed as
$ L tilde.equiv product.co_(i=0)^(q-1)P^i X_i, $
with $X_i$ an $R_0$-lattice of rank $r_i$. The isomorphism invariants of $L$ are
the ranks ${r_0,dots,r_(q-1)}$ and the Steinitz class of the $R_0$-lattice
$product.co X_i$. In calculating orbits in $"Ext"(N,L)$, we may replace $N$ and
$L$ by lattices in their respective genera, by virtue of
@cor:standard-extension-automorphism-orbits. (The reader will easily verify that
the Eichler condition holds for the lattices involved here.) Thus, we may take
$N$ to be a sum of copies of $ZZ$, $S$ and $ZZ H$ with various multiplicities,
and we may assume that $L$ is a direct sum of $P^i$'s.

Let us now determine which $ZZ G$-lattices $M$ are indecomposable, for the cases
where $L$ and $N$ are nonzero. The sequence $0->L_q->M_q->N_q->0$ must split,
since the only indecomposable $ZZ_q G$-lattices are those listed in
@eq:metacyclic-localized-indecomposable-lattices. Therefore
$M_q tilde.equiv L_q plus.o N_q$, and the decomposition of $M_q$ into
indecomposable summands is obtained by decomposing $L_q$ and $N_q$. On the other
hand, in considering decompositions after localizing at $p$, we may instead work
with $p$-adic completions, by @sec:local-theory. By looking at the list
@eq:metacyclic-complete-indecomposable-list and the non-split sequences
@eq:metacyclic-complete-induced-extension, and taking into account the formulas
$
  hat(ZZ)H tilde.equiv product.co_(i=0)^(q-1)hat(ZZ)_i, quad
  hat(S) tilde.equiv product.co_(i=1)^(q-1)hat(ZZ)_i,
$
#source(773)
the reader will be convinced that the genera of indecomposable $ZZ G$-lattices
are represented by the middle terms in the following three types of non-split
exact sequences:
$
  cases(
    ("a") & quad 0->P->V->ZZ->0,
    ("b") & quad 0->L_T->X_T->S->0,
    ("c") & quad 0->L_T->Y_T->ZZ H->0
  ).
$
<eq:metacyclic-indecomposable-genus-extensions>
Here, $T$ is any non-empty subset of ${0,1,dots,q-1}$, and
$L_T=product.co_(t in T)P^t$. However, in (b) we must always omit the summand
$P$, since there is no non-split extension of $hat(ZZ)_j$ by $hat(P)$ for
$j=1,dots,q-1$.

The preceding discussion shows that the indecomposable genera of $ZZ G$-lattices
are represented by
$ P^i (0<=i<=q-1), ZZ,S,ZZ H; quad {X_T},{Y_T},V. $
Further, there is only one genus of each of these types, since the genus of $M$
is determined by the isomorphism classes of $M_q$ and $hat(M)$, and we have
$
  hat(V) tilde.equiv (hat(ZZ)_0)^G, quad
  hat(X)_T tilde.equiv product.co_(t in T)(hat(ZZ)_(t-1))^G
  plus.o product.co_(t in.not T)hat(ZZ)_(t-1),
$
<eq:metacyclic-genus-completion-formulas>
with an analogous formula for each $Y_T$. The complementary indices range over
${0,1,dots,q-1} without {1}$ for $X_T$ and over ${0,1,dots,q-1}$ for $Y_T$. As
$T$ varies, we obtain $2^(q-1)-1$ choices for $X_T$, and $2^q-1$ choices for
$Y_T$. Thus there are
$ 2^q+2^(q-1)+q+2 $
indecomposable genera of $ZZ G$-lattices.#idx(
  "Pu's Theorem",
  target: [@eq:metacyclic-indecomposable-genus-extensions],
)

It should be noted that a genus need not decompose uniquely into indecomposable
genera. For example, let $T_1,dots,T_4$ be non-empty subsets of
${0,2,3,dots,q-1}$, such that
$ T_1 union T_2=T_3 union T_4 quad ("counting multiplicities"). $
Then we have
$ (X_(T_1) plus.o X_(T_2)) or.curly (X_(T_3) plus.o X_(T_4)) $
by virtue of @eq:metacyclic-genus-completion-formulas.

We remark finally that the question of finding all $ZZ G$-lattices in a given
indecomposable genus reduces to a problem in units, of the same nature as the
questions on units in @ss:cyclic-p-squared-lattices.

Let us apply the above discussion to the special case in which $G$ is a dihedral
group of order $2p$, where $p$ is an odd prime. We thus take $q=2$,
#source(774)
$r=-1$ in the preceding calculations. Here,
$
  K_0=QQ(zeta+zeta^(-1)), quad R_0=ZZ[zeta+zeta^(-1)], quad
  theta=-1, quad S=ZZ.
$
There are then $10$ indecomposable genera of $ZZ G$-lattices, represented by the
following list:
#enum(
  numbering: "(i)",
  [$R=ZZ[zeta]$, $P=(1-zeta)R$, on which $x$ acts as multiplication by $zeta$,
    and $y$ acts as complex conjugation.],
  [$ZZ,ZZ',ZZ H$, on which $x$ acts trivially, while $y$ acts as $+1$ and $-1$
    on $ZZ$ and $ZZ'$, respectively.],
  [$V="non-split extension of" ZZ "by" P$, so $V tilde.equiv "ind"_H^G ZZ$.],
  [$X="non-split extension of" ZZ' "by" R$, so $X tilde.equiv "ind"_H^G ZZ'$.],
  [$Y_0$, $Y_1$, and $Y_2$, non-split extensions as shown:
    $ 0->R->Y_0->ZZ H->0, quad 0->P->Y_1->ZZ H->0, $
    $ 0->R plus.o P->Y_2->ZZ H->0. $],
)
We have $hat(ZZ)G$-isomorphisms
$
  hat(Y)_0 tilde.equiv hat(X) plus.o hat(ZZ), quad
  hat(Y)_1 tilde.equiv hat(V) plus.o hat(ZZ)', quad
  hat(Y)_2 tilde.equiv hat(X) plus.o hat(V),
$
and therefore
$ (Y_0 plus.o Y_1) or.curly (Y_2 plus.o ZZ H). $
<eq:dihedral-integral-genus-relation>
Since $"Ext"(ZZ,P) tilde.equiv overline(ZZ)$ (see
Exercise~@exc:metacyclic-completed-extension-groups), and $Aut P$ maps onto
$(overline(ZZ))^dot$, there is only one orbit of $"Ext"(ZZ,P)$, under the action
of $(Aut ZZ,Aut P)$, which contains the extension class of $V$. Similar remarks
hold for $X$ and each $Y_i$. Consequently we obtain:

#theorem[
  Let $frak(a)$ range over a full set of representatives of the $h_0$ ideal
  classes of $R_0$, where $R_0=ZZ[zeta+zeta^(-1)]$. Then there are precisely
  $7h_0+3$ isomorphism classes of indecomposable $ZZ G$-lattices, and these are
  represented by:
  $ R frak(a), P frak(a); quad ZZ,ZZ',ZZ H; $
  and nonsplit extensions (compare with the list (i)–(v) above):
  $
    0->P frak(a)->V_(frak(a))->ZZ->0, quad
    0->R frak(a)->X_(frak(a))->ZZ'->0,
  $
  $
    0->R frak(a)->(Y_0)_(frak(a))->ZZ H->0, quad
    0->P frak(a)->(Y_1)_(frak(a))->ZZ H->0,
  $
  $ 0->R frak(a) plus.o P->(Y_2)_(frak(a))->ZZ H->0. $
  #idx("Lee's Theorem", target: [@th:dihedral-integral-indecomposable-lattices])
] <th:dihedral-integral-indecomposable-lattices>

#source(775)
Using @eq:dihedral-integral-genus-relation, it is not difficult to find all
relations connecting direct sums of indecomposable $ZZ G$-lattices. For details,
see Lee~@bib:Lee1964.

_Notes._ Some additional cases where integral representations have been
calculated are as follows:
#enum(
  numbering: "(i)",
  [$G$ cyclic of squarefree order: Knee~@bib:Knee1962,
    Oppenheim~@bib:Oppenheim1962.],
  [Cubic $ZZ$-rings (that is, $ZZ$-orders in semisimple $QQ$-algebras $A$ with
    $dim_QQ A=3$): Faddeev~@bib:Faddeev1965b, Drozd~@bib:Drozd1967.],
  [$G$ an abelian $(2,2)$-group: Nazarova~@bib:Nazarova1961, @bib:Nazarova1967;
    see also Nazarova–Roiter~@bib:Nazarova1969.],
  [$G=A_4$ (alternating group): Nazarova~@bib:Nazarova1963.],
  [$G=S_n$ (symmetric group): Craig~@bib:Craig1976 finds all full
    $ZZ G$-lattices in a simple $QQ G$-lattice of $QQ$-dimension $n-1$.],
)

#exercises-heading

#exercise[
  Keep the notation of @exm:matrix-order-characteristic-sublattice, and let
  $M,M'$ be $Lambda$-lattices. There are exact sequences
  $
    0->L^((r))->M->overline(ZZ)^((s))->0, quad
    0->L^((t))->M'->overline(ZZ)^((u))->0,
  $
  in which $L^((r))$ is a characteristic submodule of $M$, and $L^((t))$ of
  $M'$. Show that $M tilde.equiv M'$ if and only if $r=t$, $s=u$, and there
  exists a commutative diagram
  #extension-exercise-isomorphism()
  in which $lambda$ and $nu$ are isomorphisms.

  #hint([@exc:matrix-order-extension-isomorphism])[
    An isomorphism $mu$ induces maps $lambda:L^((r))->L^((t))$,
    $nu:overline(ZZ)^((s))->overline(ZZ)^((u))$, with $lambda$ injective, $nu$
    surjective. Thus $r<=t$, $s>=u$. Now use $mu^(-1)$.
  ]
] <exc:matrix-order-extension-isomorphism>

#exercise[
  Keep the notation of @prop:prime-square-complex-extension-orbits and the
  discussion which follows it. Show that there is a fibre product diagram
  #extension-fibre-square()
  and an exact sequence of $E$-modules
  $ 0->ZZ plus.o ZZ arrow.r^(1 plus.o Phi_1(x)) ZZ plus.o E->R_1->0. $
  #source(776)
  Show that each $f in "End"(ZZ plus.o E)$, given as in
  @prop:prime-square-complex-extension-orbits, induces maps $f_0$, $f_1$ as in
  @eq:complex-extension-orbit-equations, and that $f$ is an automorphism if and
  only if both $f_0$ and $f_1$ are automorphisms.
] <exc:cyclic-order-fibre-product-endomorphisms>

#exercise[
  Using the above notation, show
  #enum(
    numbering: "(i)",
    [For each $alpha in R_1^dot$, there exists an $f in Aut(ZZ plus.o E)$ for
      which $mu_1(d)=alpha$.],
    [For each matrix $beta in "GL"_2(ZZ)$ whose $(2,1)$-entry is a multiple of
      $p$, there exists an $f in Aut(ZZ plus.o E)$ for which $f_0=beta$.],
  )
] <exc:cyclic-order-automorphism-lifting>

#exercise[
  Keep the notation of the preceding two exercises, and let
  $overline(R)_1=R_1 slash p R_1$. There is a ring surjection
  $theta:R_2->overline(R)_1$, defined by composition of maps:
  $
    R_2->R_2 slash p R_2
    tilde.equiv overline(ZZ)[lambda] slash (lambda^(p(p-1)))
    ->overline(ZZ)[lambda] slash (lambda^(p-1)) tilde.equiv overline(R)_1,
  $
  where $lambda=1-omega_2$. Show that for each $s in R_2^dot$, there exists an
  $r in R_1^dot$ such that $theta(s)=overline(r)$ in $overline(R)_1$.

  #hint([@exc:cyclotomic-unit-reduction-norm])[
    The result is trivial when $p=2$, so assume $p$ odd. Write $s=f(omega_2)$,
    where $f(X) in ZZ[X]$, and let $f(X)=product_(j=1)^n (X-alpha_j)$ in some
    splitting field for $f(X)$ over $QQ(omega_2)$. We choose $r=N(s) in R_1$,
    where $N:R_2->R_1$ is the relative norm map. Then $r in R_1^dot$ since $N$
    is multiplicative. Further
    $
      r=N(f(omega_2))=product_(i=0)^(p-1)f(omega_1^i omega_2)
      =lr([product_i f(omega_1^i X)])|_(X=omega_2).
    $
    But
    $
      product_i f(omega_1^i X)
      =product_(i=0)^(p-1) product_(j=1)^n (omega_1^i X-alpha_j)
      =product_j (X^p-alpha_j^p)
    $
    $ equiv lr({product_j (X-alpha_j)})^p={f(X)}^p equiv f(X^p) mod p. $
    Therefore
    $ r equiv f(omega_2^p)=f(omega_1)=theta(s) mod p R_1, $
    as desired.
  ]
] <exc:cyclotomic-unit-reduction-norm>

#exercise[
  Keep the notation of @th:cyclic-p-locally-free-extension-classification. Show
  that $E$ does not decompose into a direct sum of ideals.

  #hint([@exc:cyclotomic-factor-order-indecomposable])[
    If $E$ decomposes, so does $overline(E)$, where bars denote reduction mod
    $p$. But $overline(E) tilde.equiv overline(ZZ)[lambda] slash (lambda^d)$.
  ]
] <exc:cyclotomic-factor-order-indecomposable>

#exercise[
  Let $overline(ZZ)=ZZ slash p ZZ$. Show that the image of $"GL"_n (ZZ)$ in
  $"GL"_n (overline(ZZ))$ consists of all matrices in $"GL"_n (overline(ZZ))$ of
  determinant $plus.minus 1$.
] <exc:integral-general-linear-reduction-image>

#source(777)
#exercise[
  Using the notation in @ss:dihedral-metacyclic-integral-representations, prove
  that
  $
    "Ext"_(hat(ZZ)G)^1(hat(ZZ)_i,hat(P)^(i+1)) tilde.equiv overline(ZZ),
    quad 0<=i<=q-1,
  $
  and that $hat(P)^q tilde.equiv hat(R)$ as $hat(ZZ)G$-modules.
] <exc:metacyclic-completed-extension-groups>

#exercise[
  For $n>=2$, let $omega$ be a primitive $2^n$-th root of $1$, and let
  $R=ZZ[omega]$. Let $Lambda=R compose H$ be the twisted group ring, where
  $H=chevron.l x:x^2=1 chevron.r$, and where $x alpha=overline(alpha)x$,
  $alpha in R$, with $overline(alpha)$ the complex conjugate of $alpha$. Show
  that $K=QQ(omega)$ is the unique simple $(K compose H)$-module, where $x$ acts
  as complex conjugation on $K$. Let $frak(a)_i$ range over the $h_0$
  representatives of the ideal classes of $R_0$, where
  $R_0=ZZ[omega+overline(omega)]$.
  #enum(
    numbering: "(i)",
    [Prove that a full set of non-isomorphic full $Lambda$-lattices in $K$ is
      given by
      $
        {R frak(a)_i:1<=i<=h_0} union
        {(1-omega)R frak(a)_i:1<=i<=h_0}.
      $],
    [Show that for $1<=i,j<=h_0$,
      $
        "Ext"_Lambda^1(R frak(a)_i,(1-omega)R frak(a)_j)=0
        ="Ext"_Lambda^1((1-omega)R frak(a)_i,R frak(a)_j),
      $
      $
        "Ext"_Lambda^1(R frak(a)_i,R frak(a)_j) tilde.equiv overline(ZZ)
        tilde.equiv "Ext"_Lambda^1((1-omega)R frak(a)_i,(1-omega)R frak(a)_j),
      $
      where $overline(ZZ)=ZZ slash 2 ZZ$.],
    [Show that there exist nonsplit exact sequences of $Lambda$-lattices:
      $
        0->R->Lambda->R->0, quad
        0->(1-omega)R->Lambda->(1-omega)R->0.
      $],
    [Find all indecomposable $Lambda$-lattices.],
  )

  #hint([@exc:dyadic-cyclotomic-conjugation-order-lattices])[
    See Theohari–Apostilidi~@bib:TheohariApostilidi1982.
  ]
] <exc:dyadic-cyclotomic-conjugation-order-lattices>
