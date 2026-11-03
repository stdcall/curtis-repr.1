#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/35-invertible-ideals.typ": *

== Invertible Ideals <sec:invertible-ideals>

In this section we shall be concerned mainly with the theory of invertible
ideals in commutative rings. However, we begin our discussion with the more
general concept of invertible bimodules over a pair of rings $Lambda,Delta$, not
necessarily commutative. This extra generality will be needed for our discussion
of Picard groups in Chapter~11 of Volume~II.

A $(Lambda,Delta)$-bimodule $attach(M, bl: Lambda, br: Delta)$ is called
_invertible_ if $M$ gives rise to a Morita equivalence between the categories of
$Lambda$-modules and $Delta$-modules, according to Theorem~@th:morita.#idx(
  "invertible bimodule",
) This occurs if all of the following conditions are satisfied:
#enum(
  numbering: "(i)",
  [$M in cal(P)(Lambda)$, the category of f.g. projective $Lambda$-modules,],
  [$M$ is a generator for the category of left $Lambda$-modules,],
  [$Delta tilde.equiv {End_Lambda M}^circle.small$.],
)

#source(778)
On the other hand, given a left $Lambda$-module $M$, define $Delta$ as in (iii).
Then there are bimodule maps
$
  ( , ):M times.o_Delta Hom(M, Lambda)->Lambda, quad
  [ , ]:Hom(M, Lambda) times.o_Lambda M->Delta.
$ <eq:invertible-bimodule-evaluations>
We showed that $( , )$ is surjective if and only if $M$ is a generator for the
category of left $Lambda$-modules, and that $[ , ]$ is surjective if and only if
$M in cal(P)(Lambda)$. In particular, if both maps are surjective, then both are
isomorphisms.

We may restate @th:morita as follows: a bimodule
$attach(M, bl: Lambda, br: Delta)$ is invertible if and only if there exists a
bimodule $attach(N, bl: Delta, br: Lambda)$ and bimodule surjections
$
  M times.o_Delta N->Lambda, quad N times.o_Lambda M->Delta,
$ <eq:invertible-bimodule-inverse-maps>
for which the following diagrams commute:
#numbered-block[#invertible-associativity()]
<eq:invertible-bimodule-associativity>
When this occurs, the maps in @eq:invertible-bimodule-inverse-maps are
isomorphisms.

For example, let $A$ be a simple artinian ring, and let
$attach(X, bl: A, br: A)$ be an invertible bimodule. We claim that
$X tilde.equiv A$ as left $A$-modules. Suppose that $V$ is a simple left
$A$-module, and set $D=End_A V$, so $A tilde.equiv End_D V$. Since $X$ is
invertible, we have $A tilde.equiv {End_A lr((attach(X, bl: A)))}^circle.small$.
Now $X tilde.equiv V^((n))$ for some $n$ (as left $A$-modules), so
$
  A^circle.small tilde.equiv End_A lr((V^((n)))) tilde.equiv M_n lr((D)).
$
But then $n=dim_D V$ and $X tilde.equiv V^((n)) tilde.equiv A$ as left
$A$-modules, as claimed. (We note, however, that $X$ need not be isomorphic to
$A$ as $(A,A)$-bimodule; see
Exercise~@exc:automorphism-twisted-invertible-bimodules.)

We show next that invertibility is a “local” property:

#proposition[
  Let $R$ be a commutative noetherian ring, and let $Lambda$ and $Delta$ be
  $R$-algebras, f.g./$R$ as modules. Let $attach(M, bl: Lambda, br: Delta)$ be a
  bimodule f.g./$R$. Let $P$ range over all maximal ideals of $R$, and let
  $M_P,Lambda_P$, etc., denote localizations at $P$. Then $M$ is an invertible
  $(Lambda,Delta)$-bimodule if and only if for each $P$, the
  $(Lambda_P,Delta_P)$-bimodule $M_P$ is invertible.
] <prop:invertible-bimodule-localization>
#proof[
  For each $P$, we have maps
  $
    M_P times.o Hom_(Lambda_P) lr((M_P,Lambda_P))->Lambda_P, quad
    Hom_(Lambda_P) lr((M_P,Lambda_P)) times.o M_P->Delta_P,
  $
  obtained by localizing the maps in @eq:invertible-bimodule-evaluations. The
  desired result follows at once from @prop:localization-criteria. Note that
  $ {End_Lambda M}_P tilde.equiv End_(Lambda_P) M_P quad "for all" P. $
]

#source(779)
Suppose now that $Lambda$ is a commutative ring, and let us agree to make each
one-sided $Lambda$-module $M$ into a $(Lambda,Lambda)$-bimodule by setting
$m lambda=lambda m$ for all $m in M,lambda in Lambda$. We shall call $M$ an
_invertible_ $Lambda$-_module_ if $M$ is invertible as bimodule.#idx(
  "invertible module",
) The discussion preceding @prop:invertible-bimodule-localization shows that if
$Lambda$ is a direct sum of fields, then a $Lambda$-module $M$ is invertible if
and only if $M tilde.equiv Lambda$. We shall use this fact in proving that
invertible modules are locally free:

#theorem[
  Let $Lambda$ be a commutative $R$-algebra, f.g./$R$ as module, where $R$ is a
  commutative noetherian ring. Let $M$ be any f.g. $Lambda$-module. Then $M$ is
  invertible if and only if $M_P tilde.equiv Lambda_P$ for each maximal ideal
  $P$ of $R$.
] <th:invertible-module-locally-free>
#proof[
  If $M$ is invertible, so is $M_P$, and we must show that
  $M_P tilde.equiv Lambda_P$. Replacing $R$ by $R_P$ and changing notation, we
  may now assume that $R$ is a local noetherian ring. Let $J="rad" Lambda$, and
  let bars denote reduction mod~$J$. Since $M$ is invertible, there exists a
  $Lambda$-module $N$ and maps as in @eq:invertible-bimodule-inverse-maps and
  @eq:invertible-bimodule-associativity, with $Delta$ replaced by $Lambda$. The
  corresponding situation then occurs for the $overline(Lambda)$-modules
  $overline(M)$ and $overline(N)$, which shows that $overline(M)$ is an
  invertible $overline(Lambda)$-module. But $overline(Lambda)$ is a commutative
  semisimple ring by @prop:finite-algebra-local-base-radical, and is therefore a
  direct sum of fields. Our previous discussion shows that
  $overline(M) tilde.equiv overline(Lambda)$. Since $M in cal(P)(Lambda)$, we
  obtain $M tilde.equiv Lambda$ by @prop:projective-isomorphism-modulo-radical.

  Conversely, suppose that $M_P tilde.equiv Lambda_P$ for each $P$, and let
  $Delta=End_Lambda lr((M))$. Then $Lambda subset.eq Delta$, and
  $Lambda_P=Delta_P$ for each $P$, whence $Lambda=Delta$ by
  @prop:localization-criteria. But then in the situation of
  @eq:invertible-bimodule-evaluations with $Delta$ replaced by $Lambda$, both
  maps are surjective at each $P$, whence they are surjective by
  @prop:localization-criteria. Hence $M$ is an invertible $Lambda$-module, as
  desired.
]

As a corollary, we obtain the following result of Faddeev @bib:Faddeev1965a:

#corollary[
  Let $Lambda$ be a commutative $R$-order, where $R$ is a Dedekind domain, and
  let $M$ be a $Lambda$-lattice. Then $M$ is invertible if and only if $M$ lies
  in the genus of $Lambda$. Each such $M$ is isomorphic to a locally free ideal
  of $Lambda$.
] <cor:invertible-order-module-genus>

A more general result of this nature, needed for our later discussion, is as
follows:

#proposition[
  Let $Lambda$ be an $R$-order in a f.d. commutative $K$-algebra $A$, where $R$
  is a Dedekind domain with quotient field $K$, and let $M$ be a
  $Lambda$-lattice. Then we have an equivalence:
  $
    cases(reverse: #true, M "is" Lambda "-projective", K M tilde.equiv A^((n)))
    <=> M or.curly Lambda^((n)).
  $
] <prop:commutative-order-projective-free-genus>
#proof[
  If $M or.curly Lambda^((n))$, then $M$ is $Lambda$-projective and
  $K M tilde.equiv A^((n))$, so we need only prove the converse. Replacing $R$
  by its $P$-adic completion, where $P$ is an arbitrary maximal ideal of $R$,
  and changing notation, we must now show that if $M in cal(P)(Lambda)$ and
  $K M tilde.equiv A^((n))$, then $M tilde.equiv Lambda^((n))$.

  #source(780)
  Let $J="rad" Lambda$, so $Lambda slash J$ is a direct sum of fields. Then we
  may write $Lambda=plus.o_(i=1)^r Lambda e_i$, where the ${e_i}$ are primitive
  orthogonal idempotents in $Lambda$, and each $Lambda e_i slash J e_i$ is one
  of the fields occurring as a summand of $Lambda slash J$. Then
  $Lambda e_i tilde.equiv Lambda e_j$ if and only if $i=j$, and furthermore, the
  $Lambda$-modules $A e_i$ and $A e_j$ have no common direct summand if $i!=j$.

  Now we may write
  $ M tilde.equiv product.co_(i=1)^r (Lambda e_i)^((m_i)), $
  whence
  $
    K M tilde.equiv product.co (A e_i)^((m_i)), quad
    A^((n)) tilde.equiv product.co (A e_i)^((n)).
  $
  Thus each $m_i=n$, so $M tilde.equiv Lambda^((n))$ as claimed.
]

_Note._ The same argument shows that if $M,N in cal(P)(Lambda)$ and
$K M tilde.equiv K N$, then $M or.curly N$. See
Exercise~@exc:commutative-order-projective-generic-isomorphism.

We now wish to relate the above concept of invertibility with the intuitively
more appealing concept of invertibility of fractional ideals relative to some
ring. Suppose from now on that $R$ is a Dedekind domain with quotient field $K$,
and let $A$ be a f.d. _commutative_ $K$-algebra, which we shall later assume to
be separable over $K$. Let $M$ be a full $R$-lattice in $A$, that is, $M$ is a
f.g. projective $R$-module such that $K M=A$. We may think of $M$ as a
“fractional ideal” in $A$. Let $Lambda$ be the (left) order of $M$ as defined in
@def:left-right-order, that is,
$ Lambda={x in A:x M subset.eq M}=O(M). $
Then $Lambda$ is an $R$-order in $A$, and $M$ is a $Lambda$-lattice. We define
$ M^(-1)={y in A:y M subset.eq Lambda}, $
as in @eq:inverse-order-lattice. Then $M^(-1)$ is also a full $R$-lattice in
$A$, and obviously $M^(-1) tilde.equiv Hom_Lambda lr((M,Lambda))$. If $M$ is
invertible, then the obvious map $M times.o_Lambda M^(-1)->Lambda$ is
surjective, and therefore $M dot M^(-1)=Lambda$.

Let $M$ be a full $R$-lattice in $A$. We may observe that if $M$ is an
invertible $Delta$-module, where $Delta$ is some $R$-order in $A$, then
$M dot N=Delta$ for some $Delta$-module $N$ in $A$. (Indeed, if $M N=Delta$ for
some full $R$-lattice $N$ in $A$, then also $M dot Delta N=Delta$, and $Delta N$
is a $Delta$-module.) From the equality $M dot N=Delta$, we find at once that
$Delta=O(M)$. Thus, the only case in which $M$ can be an invertible
$Delta$-module is that where $Delta=O(M)$, and where $M$ is invertible when
considered as $O(M)$-module. This motivates the following definition.

#definition[
  A full $R$-lattice $M$ in $A$ is called _invertible_ if $M$ is an invertible
  $Lambda$-module, where $Lambda$ is the order of $M$, defined above.
] <def:invertible-fractional-ideal>
#idx("ideal", "invertible")#idx("invertible ideal")

#source(781)
Let $M$ be a full $R$-lattice in a commutative separable $K$-algebra $A$. The
powers $M,M^2,dots$ are also full lattices in $A$. If $M$ is invertible, then
obviously so is each power of $M$; for if $M N=Lambda$, where $Lambda$ is the
order of $M$, then $M^r N^r=Lambda$, which readily implies that $Lambda$ is the
order of $M^r$ and that $M^r$ is invertible. It may happen, however, that some
power of $M$ is invertible even though $M$ itself is not. In this section we
shall prove the beautiful Dade-Taussky-Zassenhaus Theorem, which states that
when $A$ is an algebraic number field of degree $n$ over the rational field
$QQ$, then $M^(n-1)$ is invertible for every full $ZZ$-lattice $M$ in $A$. Our
proof will be based on the treatment given by Singer @bib:Singer1973, which in
turn depends on his simplified proof of a theorem of Fröhlich, interesting in
its own right.

For the rest of this section, let $A$ be a commutative f.d. separable
$K$-algebra. Then $A$ is just a finite direct sum of finite separable field
extensions of $K$, by §@sec:separable-algebras-splitting-fields. Let $Lambda_0$
be the integral closure of $R$ in $A$, so by
@prop:commutative-separable-unique-maximal-order, $Lambda_0$ is the unique
maximal $R$-order in $A$. Let $M$ and $N$ be a pair of full $R$-lattices in an
$A$-module $V$. We shall write $M tilde.equiv N$ if $M$ and $N$ are isomorphic
$Gamma$-lattices for some $R$-order $Gamma$ in $A$ contained in both the order
of $M$ and the order of $N$; by Exercise~@exc:overorder-lattice-homomorphisms,
this definition does not depend on the choice of $Gamma$. Likewise, we say that
$M$ and $N$ are in the same genus, and write $M or.curly N$, if
$M_P tilde.equiv N_P$ as $Gamma_P$-lattices for each maximal ideal $P$ of $R$.
As pointed out in §@sec:local-theory, $M_P tilde.equiv N_P$ if and only if
$hat(M)_P tilde.equiv hat(N)_P$, where $hat("")$ indicates $P$-adic completion.

Now let $J$ be a “fractional ideal” in $A$, that is, a full $R$-lattice in $A$.
We have seen that $J$ is invertible if and only if $J$ is locally free (as
$O(J)$-lattice, where $O(J)$ is the order of $J$). We shall prove below the
somewhat surprising result due to Fröhlich, which shows that $J$ is invertible
if and only if
$ "ord"_R lr((Lambda_0 J slash J))="ord"_R lr((Lambda_0 slash O(J))), $
where $"ord"_R$ is the $R$-order ideal defined in §@ss:modules-dedekind-domains.
In fact, we shall establish a more general result due to Fröhlich
@bib:Frohlich1965, as follows:

#theorem[
  Let $A$ be a commutative separable $K$-algebra, $Lambda_0$ its maximal
  $R$-order, and $Lambda$ any $R$-order in $A$. Let $M$ be a full
  $Lambda$-lattice in a free $A$-module $A^((n))$. Then
  $
    "ord"_R lr((Lambda_0 M slash M)) "divides"
    {"ord"_R lr((Lambda_0 slash Lambda))}^n,
  $ <eq:frohlich-order-ideal-bound>
  and equality holds if and only if $M$ is in the genus of $Lambda^((n))$, or
  equivalently, if and only if $M$ is $Lambda$-projective.
] <th:frohlich-order-ideal-bound>
#idx("Fröhlich’s Theorem", target: [@th:frohlich-order-ideal-bound])
#proof[
  We follow Dade's approach, as described in Fröhlich @bib:Frohlich1965,
  Appendix~B. For each maximal ideal $P$ of $R$, order ideals behave properly
  under passage to $P$-adic completions (see §@ss:modules-dedekind-domains). The
  hypotheses of the theorem carry over to the completions; since the conclusion
  of the theorem (that
  #source(782)
  $M or.curly Lambda^((n))$) is a local statement, it suffices to prove the
  result#footnote[
    Of course, we will prove that $M tilde.equiv Lambda^((n))$ rather than
    $M or.curly Lambda^((n))$.
  ] when $R$ is replaced by its completion. Changing notation, we assume for the
  rest of the proof that $R$ is a complete d.v.r. with residue class field
  $overline(R)=R slash P$.

  We suppose first that $overline(R)$ is an infinite field, and prove the
  theorem for this case. We may write
  $
    A tilde.equiv product.co_(i=1)^t K_i, quad
    Lambda_0 tilde.equiv product.co_(i=1)^t R_i, quad
    R_i="integral closure of" R "in" K_i.
  $
  Here, each $K_i$ is a finite separable extension field of $K$, and $R_i$ is a
  d.v.r. with quotient field $K_i$. Let $e_1,dots,e_t$ be the primitive
  idempotents of $A$ corresponding to the above decomposition, so
  $A e_i tilde.equiv K_i$, $Lambda_0 e_i tilde.equiv R_i$. Let
  $J_0="rad" Lambda_0$; if $P_i$ is the maximal ideal of $R_i$, then
  $J_0 tilde.equiv product.co P_i$, and
  $
    overline(Lambda)_0=Lambda_0 slash J_0
    =plus.o Lambda_0 e_i slash J_0 e_i
    tilde.equiv product.co_(i=1)^t overline(R)_i,
  $
  where $overline(R)_i=R_i slash P_i$ is a finite extension of the field
  $overline(R)$.

  Since $K M tilde.equiv A^((n))$, it is clear from
  @th:maximal-orders-are-hereditary(ii), and the proof of
  @prop:commutative-order-projective-free-genus, that the $Lambda_0$-lattice
  $Lambda_0 M$ must be a free $Lambda_0$-module on $n$ generators. (This also
  follows as a special case of
  Exercise~@exc:dvr-maximal-order-lattice-isomorphism.) We shall show that there
  exist elements $m_1,dots,m_n in M$ which form a free $Lambda_0$-basis for
  $Lambda_0 M$, and we proceed to construct them inductively. We may write
  $Lambda_0 M=plus.o_(l=1)^n Lambda_0 a_l$, where the ${a_l}$ are a
  $Lambda_0$-basis for $Lambda_0 M$. Then
  $
    Lambda_0 M slash J_0 M
    =(plus.o Lambda_0 a_l) slash (plus.o J_0 a_l)
    =plus.o overline(Lambda)_0 overline(a)_l
    =plus.o_(l=1)^n plus.o_(i=1)^t overline(R)_i overline(a)_l
    =plus.o_(i=1)^t X_i,
  $
  where
  $
    X_i=plus.o_(l=1)^n overline(R)_i overline(a)_l
    tilde.equiv e_i Lambda_0 M slash e_i J_0 M, quad 1<=i<=t.
  $
  Thus, each $X_i$ is an $n$-dimensional space over the field $overline(R)_i$.
  The maps $M->Lambda_0 M->Lambda_0 M slash J_0 M->X_i$ induce an
  $overline(R)$-homomorphism
  $ theta_i:M slash P M->X_i $
  for each $i$, $1<=i<=t$, and $theta_i lr((M slash P M))$ spans $X_i$ over
  $overline(R)_i$.

  Now let $0<=r<n$, and suppose that we have found elements
  $v_1,dots,v_r in M slash P M$ such that
  $
    theta_i lr((v_1)),dots,theta_i lr((v_r))
    "are linearly independent over" overline(R)_i, quad "for" 1<=i<=t.
  $
  #source(783)
  We wish to find an element $v_(r+1) in M slash P M$ so that the above property
  holds for the larger collection $v_1,dots,v_(r+1)$. Let
  $
    W_i=theta_i^(-1) lr({plus.o_(j=1)^r overline(R)_i theta_i lr((v_j))}),
    quad 1<=i<=t.
  $
  (In the special case where $r=0$, let $W_i=theta_i^(-1) lr((0))=ker theta_i$.)
  Each $W_i$ is then a proper $overline(R)$-subspace of $M slash P M$, since
  $theta_i lr((W_i))$ is contained in an $r$-dimensional
  $overline(R)_i$-subspace whereas $theta_i lr((M slash P M))$ spans the
  $n$-dimensional space $X_i$ over $overline(R)_i$. Now $overline(R)$ is assumed
  infinite, so by Exercise~@exc:infinite-field-finite-subspace-union, the space
  $M slash P M$ cannot be the union of the proper subspaces $W_1,dots,W_t$.
  Hence there exists an element $v_(r+1) in M slash P M$ which does not lie in
  any of $W_1,dots,W_t$. But then $v_(r+1)$ has the desired property.

  We have now obtained (by induction) a set of $n$ elements
  $v_1,dots,v_n in M slash P M$ such that for each $i$, $1<=i<=t$, their images
  $theta_i lr((v_1)),dots,theta_i lr((v_n))$ form a
  $overline(Lambda)_0 e_i$-basis for $X_i$. Choose elements $m_j in M$
  representing the elements ${v_j}$. Then we obtain
  $ Lambda_0 M=sum_(j=1)^n Lambda_0 m_j+J_0 M, $
  so $Lambda_0 M=plus.o Lambda_0 m_j$ by Nakayama's Lemma. Therefore we obtain
  $
    plus.o_(j=1)^n Lambda_0 m_j=Lambda_0 M
    supset.eq M supset.eq plus.o_(j=1)^n Lambda m_j,
  $
  and so
  $
    "ord"_R lr((Lambda_0 M slash M)) "divides"
    "ord"_R lr((Lambda_0 M slash plus.o Lambda m_j)),
  $
  with equality if and only if $M=plus.o Lambda m_j$. But the latter order ideal
  is precisely ${("ord"(Lambda_0 slash Lambda))}^n$, so we have established
  @eq:frohlich-order-ideal-bound. Further, equality in
  @eq:frohlich-order-ideal-bound implies that $M tilde.equiv Lambda^((n))$.
  Conversely, $M tilde.equiv Lambda^((n))$ clearly gives equality in
  @eq:frohlich-order-ideal-bound, so the theorem is proved in this case.

  If the field $overline(R)$ is finite, we follow the procedure described in
  Exercises~@exc:transcendental-separable-base-extension–@exc:infinite-residue-completed-extension.
  Let $E=K(t)$ be a simple transcendental extension of $K$, and extend the
  valuation from $K$ to $E$, getting a d.v.r. $S$ in $E$ with maximal ideal
  $P S$. Let $hat(S)$ be the completion of $S$, $hat(E)$ that of $E$, and let us
  set
  $
    hat(S) Lambda=hat(S) times.o_R Lambda, quad
    hat(S) Lambda_0=hat(S) times.o_R Lambda_0, quad
    hat(E) A=hat(E) times.o_K A,
  $
  and so on. By Exercise~@exc:infinite-residue-completed-extension,
  $hat(S) Lambda$ is an $hat(S)$-order in the commutative separable
  $hat(E)$-algebra $hat(E) A$, and $hat(S) M$ is a full $hat(S) Lambda$-lattice
  in $(hat(E) A)^((n))$. Furthermore, $hat(S)$ has infinite residue class field.
  We may now apply the preceding argument to
  #source(784)
  deduce that
  $
    "ord"_(hat(S)) lr((hat(S) Lambda_0 M slash hat(S) M)) "divides"
    {"ord"_(hat(S)) lr((hat(S) Lambda_0 slash hat(S) Lambda))}^n,
  $ <eq:frohlich-infinite-residue-extension-bound>
  with equality if and only if $hat(S) M tilde.equiv (hat(S) Lambda)^((n))$.

  By @cor:order-extension-dedekind,
  $
    "ord"_(hat(S)) lr((hat(S) Lambda_0 M slash hat(S) M))
    =hat(S) times.o_R "ord"_R lr((Lambda_0 M slash M)), quad
    "ord"_(hat(S)) lr((hat(S) Lambda_0 slash hat(S) Lambda))
    =hat(S) times.o_R "ord"_R lr((Lambda_0 slash Lambda)),
  $
  so @eq:frohlich-infinite-residue-extension-bound implies
  @eq:frohlich-order-ideal-bound. Further, equality holds in one case if and
  only if it holds in the other. But
  $hat(S) M tilde.equiv (hat(S) Lambda)^((n))$ if and only if
  $M tilde.equiv Lambda^((n))$ (see
  Exercise~@exc:infinite-residue-completed-extension). The final assertion in
  the theorem follows from @prop:commutative-order-projective-free-genus, and
  the theorem is established.
]

#corollary[
  Let $J$ be a full $R$-lattice in $A$, and let $Lambda=O(J)$ be its order. Then
  $ "ord"(Lambda_0 J slash J) "divides" "ord"(Lambda_0 slash Lambda), $
  and equality holds if and only if $J or.curly Lambda$.
] <cor:frohlich-fractional-ideal-bound>

#corollary[
  Let $M$ be a full $R$-lattice in $A^((n))$, and let $J$ be any fractional
  ideal (that is, a full $R$-lattice in $A$). Then
  $
    "ord"(Lambda_0 J M slash J M) "divides both"
    ("ord"(Lambda_0 J slash J))^n "and" "ord"(Lambda_0 M slash M).
  $
  Further, $"ord"(Lambda_0 J M slash J M)="ord"(Lambda_0 M slash M)$ if and only
  if $J M or.curly M$.
] <cor:frohlich-product-lattice-bound>
#proof[
  We may assume that $R$ is a complete d.v.r. with infinite residue class field,
  as in the proof of @th:frohlich-order-ideal-bound. We may write
  $Lambda_0 M=plus.o Lambda_0 m_i$, with each $m_i in M$. Then
  $
    Lambda_0 J M=plus.o Lambda_0 J m_i supset.eq J M supset.eq plus.o J m_i.
  $
  Hence $"ord"(Lambda_0 J M slash J M)$ divides
  $"ord"(plus.o Lambda_0 J m_i slash plus.o J m_i)$, that is, it divides
  $("ord"(Lambda_0 J slash J))^n$. Equality holds if and only if
  $J M tilde.equiv J^((n))$.

  Secondly, $J$ is a full $R$-lattice in $A$, so using $J$ in place of $M$ in
  the proof of @th:frohlich-order-ideal-bound, it follows that
  $Lambda_0 J=Lambda_0 x$ for some $x in J$. Clearly $x$ is invertible in $A$,
  and $1=x x^(-1) in J x^(-1)$, so we have
  $ Lambda_0 M=Lambda_0 J x^(-1) M supset.eq J x^(-1) M supset.eq M. $
  Hence
  $ "ord"(Lambda_0 J M slash J M)="ord"(Lambda_0 J x^(-1) M slash J x^(-1) M), $
  and the latter divides $"ord"(Lambda_0 M slash M)$, with equality if and only
  if $J x^(-1) M=M$,
  #source(785)
  that is, $M tilde.equiv J M$. This completes the proof. [This step does not
  require the hypothesis that $K M tilde.equiv A^((n))$.]
]

Taking $M=J$ above, we deduce that
$ "ord"(Lambda_0 J^2 slash J^2) "divides" "ord"(Lambda_0 J slash J), $
with equality if and only if $J^2 or.curly J$. Further, by
Exercise~@exc:fractional-ideal-idempotent-genus, $J^2 or.curly J$ if and only if
$J$ is an invertible ideal. Consider now the increasing sequence of ideals of
$R$:
$
  "ord"(Lambda_0 J slash J) subset.eq "ord"(Lambda_0 J^2 slash J^2)
  subset.eq "ord"(Lambda_0 J^3 slash J^3) subset.eq dots.
$
This terminates, so for some $k>=1$ we have
$ "ord"(Lambda_0 J^(2k) slash J^(2k))="ord"(Lambda_0 J^k slash J^k). $
By the preceding remarks, this implies that $J^k$ is invertible. We improve this
result by establishing the following striking theorem, due to
Dade-Taussky-Zassenhaus @bib:Dade1962a:

#theorem[
  If $dim_K A=n>=2$, then $J^(n-1)$ is invertible for each fractional ideal $J$
  of $A$.
] <th:dade-taussky-zassenhaus-invertible-power>
#idx(
  "Dade-Taussky-Zassenhaus Theorem",
  target: [@th:dade-taussky-zassenhaus-invertible-power],
)
#proof[
  If $Lambda=O(J^(n-1))$, then $J^(n-1)$ is invertible if and only if
  $J^(n-1) or.curly Lambda$. Hence it suffices to treat the case where $R$ is a
  complete d.v.r. and to show that $J^(n-1) tilde.equiv Lambda$. By
  @th:reiner-zassenhaus-local-extension-isomorphism, it suffices to prove this
  after extending the ground ring; hence we may assume that $A$ is a split
  $K$-algebra. Finally, extending the ground ring from $R$ to $S$ as in the
  proof of @th:frohlich-order-ideal-bound, we may further assume that $R$ has
  infinite residue class field. Replacing $J$ by $J x^(-1)$ with suitable
  $x in A$, as in the proof of @cor:frohlich-product-lattice-bound, we may now
  assume that
  $
    1 in J subset.eq Lambda_0, quad
    Lambda_0=plus.o_(i=1)^n R e_i, quad A=plus.o_(i=1)^n K e_i,
  $
  where the ${e_i}$ are the primitive idempotents of $A$. We shall show that
  $J^(n-1)=J^n$, whence $(J^(n-1))^2=J^(n-1)$, so $Lambda=J^(n-1)$, and
  $J^(n-1)$ is invertible.

  Since $1 in J$, we have $J subset.eq J^2 subset.eq J^3 subset.eq dots$. Let
  $phi_i:Lambda_0->R e_i$ be the $i$-th projection map, so $phi_i lr((J))=R e_i$
  since $1 in J$. We proceed to construct $R$-bases of $J,J^2$, etc., as
  follows: choose $w_1=1$, so $phi_1 lr((w_1))=e_1$. Then
  $ J=R w_1 plus.o {J inter (R e_2+dots+R e_n)}, $
  and likewise (since $w_1 in J^m$ for $m>=1$) we have
  $ J^m=R w_1 plus.o {J^m inter (R e_2+dots+R e_n)}. $

  #source(786)
  Let us put
  $ L_m=J^m inter (R e_2+dots+R e_n), quad m>=1. $
  Then $L_1 subset.eq L_2 subset.eq dots$, so
  $phi_2 lr((L_1)) subset.eq phi_2 lr((L_2)) subset.eq dots$, and we claim that
  in fact $phi_2 lr((L_1))=phi_2 lr((L_2))=dots$. Indeed, let $m>=2$ and suppose
  that $phi_2 lr((L_(m-1)))=phi_2 lr((L_1))$. For $x in L_m$ we have $x e_1=0$
  and $x in J dot J^(m-1)$, so we may write
  $
    x & =sum_i y_i lr((beta_i w_1+z_i))
        quad "with" y_i in J,beta_i in R,z_i in L_(m-1) \
      & =y w_1+sum_i y_i z_i quad "for some" y in J.
  $
  From $e_1 x=0=e_1 dot sum y_i z_i$, we obtain $e_1 y w_1=0$, so
  $y w_1 in L_1$. Therefore
  $
    phi_2 lr((x))=phi_2 lr((y w_1))+sum phi_2 lr((y_i))phi_2 lr((z_i))
    in phi_2 lr((L_1)).
  $
  This proves that $phi_2 lr((L_m))=phi_2 lr((L_1))$ for all $m>=1$, as claimed.
  We may therefore choose $w_2 in L_1$ such that
  $ phi_2 lr((L_m))=phi_2 lr((L_1))=R phi_2 lr((w_2)) quad "for all" m>=1, $
  and hence we may write
  $
    J^m=R w_1 plus.o R w_2 plus.o
    (J^m inter (R e_3+dots+R e_n)), quad m>=1,
  $
  where $w_1,w_2 in J$.

  Now put
  $ H_m=J^m inter (R e_3+dots+R e_n), quad m>=1, $
  so $phi_3 lr((H_1)) subset.eq phi_3 lr((H_2)) subset.eq phi_3 lr((H_3))
  subset.eq dots$. We claim that the sequence is constant from $phi_3 lr((H_2))$
  on. Indeed, let $m>=3$ and suppose that $phi_3 lr((H_(m-1)))=phi_3 lr((H_2))$.
  For $x in H_m$ we have $e_1 x=e_2 x=0$, and we may write
  $
    x & =sum_i y_i lr((alpha_i w_1+beta_i w_2+z_i))
        quad "with" alpha_i,beta_i in R,y_i in J,z_i in H_(m-1) \
      & =y w_1+y' w_2+sum y_i z_i quad "for some" y,y' in J.
  $
  Then
  $
    y w_1+y' w_2 in J^2 inter (R e_3+dots+R e_n)=H_2, quad
    sum y_i z_i in J dot H_(m-1).
  $
  Hence $phi_3 lr((x)) in phi_3 lr((H_2))+phi_3 lr((H_(m-1)))
  subset.eq phi_3 lr((H_2))$, which proves that
  $phi_3 lr((H_2))=phi_3 lr((H_3))=dots$. Choose $w_3 in H_2$ so that
  $phi_3 lr((H_2))=R phi_3 lr((w_3))$. We then have
  $
    J^m=R w_1 plus.o R w_2 plus.o R w_3 plus.o
    (J^m inter (R e_4+dots+R e_n)), quad m>=2,
  $
  where $w_1,w_2 in J$ and $w_3 in J^2$.

  #source(787)
  Thus, we may choose $R$-bases for the powers $J,J^2,dots$ so that the first
  two basis elements $w_1,w_2$ can be used for each power, the first three
  $w_1,w_2,w_3$ for all powers from $J^2$ on, and so on. After $n-1$ steps, we
  find $w_1,dots,w_n$ which serve as $R$-basis for all powers from $J^(n-1)$ on.
  Therefore $J^(n-1)=J^n$, and the theorem is proved.
]

Dade-Taussky-Zassenhaus @bib:Dade1962a gave an example in which $J^(n-2)$ is not
invertible, so $n-1$ is in general best possible. This approach to the proof of
the theorem is due to Singer @bib:Singer1973. In an earlier paper, Singer
@bib:Singer1970 showed that $n-1$ can be replaced by $d-1$, where $d$ is the
number of simple components of $A$, provided that we make the additional
hypothesis that the order $O(J)$ of $J$ maps _onto_ the ring of integers in each
component. He used this result to prove that if $J$ is a full left
$ZZ G$-lattice in $QQ G$, where $G$ is a finite abelian group, then $J^(t-1)$ is
invertible. Here, $t="Max"{d(p):p "divides" |G|}$, and $d(p)$ denotes the number
of simple components of $QQ G_p$, where $G_p$ is a Sylow $p$-subgroup of $G$.
Fröhlich's Theorem~@th:frohlich-order-ideal-bound does _not_ generalize to the
non-commutative case; see Ballew @bib:Ballew1970, @bib:Ballew1971.

For further results on invertible powers of ideals, see Bass @bib:Bass1968, Dade
@bib:Dade1962, Dade-Taussky @bib:Dade1965, Faddeev @bib:Faddeev1964,
@bib:Faddeev1965a, Falk @bib:Falk1976, Gorman @bib:Gorman1970.

#exercises-heading

#exercise[
  Let $E=K(t)$ be a simple transcendental extension of $K$, and let $K'$ be a
  finite separable extension of $K$. Show that $E times.o_K K'$ is a finite
  separable field extension of $E$, and that in fact
  $E times.o_K K' tilde.equiv K'(t)$, a simple transcendental extension of $K'$.
] <exc:transcendental-separable-base-extension>
#hint([@exc:transcendental-separable-base-extension])[
  Let $K'=K[x] slash (f(x))$, with $f(x) in K[x]$ separable irreducible. Then
  $E times.o_K K' tilde.equiv E[x] slash (f(x))$; if $f=g h$ with $g,h in E[x]$,
  then the coefficients of $g$ and $h$ are algebraic over $K$, and lie in $E$,
  hence belong to $K$. Thus $f(x)$ is irreducible in $E[x]$. The field
  $E times.o_K K'$ contains $K'[t]$, hence coincides with $K'(t)$.
]

#exercise[
  Keep the above notation, and let $v$ be a discrete valuation on $K'$ with
  complete valuation ring $R'$ and prime element $pi'$, where $v(pi')=1$. Let
  $R=K inter R'$, the valuation ring of $v|_K$ in $K$. Each nonzero
  $xi in K'(t)$ is uniquely of the form $xi=(pi')^m f(t) slash g(t)$, with
  $f(t),g(t) in R'[t]$ primitive. (A polynomial is _primitive_ if the G.C.D. of
  its coefficients is 1.) Now define a valuation $v$ on $K'(t)$ by setting
  $v(xi)=m$. Then $v$ is a discrete valuation on $K'(t)$ extending the valuation
  $v$ on $K'$. Find the valuation ring $S'$ in $K'(t)$, and show that its
  residue class field $S' slash pi' S'$ is a simple transcendental extension
  $overline(R)'(t)$, where $overline(R)'=R' slash pi' R'$. Thus $S'$ has
  infinite residue class field. Show further that $K'(t)$ is _never_ complete in
  the $v$-adic valuation.
] <exc:gauss-valuation-transcendental-field>

#exercise[
  Keep the above notation, and let $S$ be the valuation ring of $v|_E$. Prove
  that $S'=S times.o_R R'$.
] <exc:gauss-valuation-integral-extension>
#hint([@exc:gauss-valuation-integral-extension])[
  Clearly $S times.o_R R' subset.eq S'$. For the reverse inclusion, let
  $xi in S'$. Since $xi in E times.o_K K'$, we may write
  $
    xi=(pi')^m f(t) slash g(t), quad f(t) in R'[t],g(t) in R[t],m in ZZ,
  $
  #source(788)
  where $f(t)$ and $g(t)$ are primitive. Then $m>=0$ since $xi in S'$, and
  $1 slash g(t) in S$, so $xi in S times.o_R R'$.
]

#exercise[
  Keep the above notation, and let $Lambda_0$ be a maximal $R$-order in a f.d.
  commutative separable $K$-algebra $A$. Show that $S times.o_R Lambda_0$ is a
  maximal $S$-order in $E times.o_K A$.
] <exc:gauss-extension-maximal-commutative-order>
#hint([@exc:gauss-extension-maximal-commutative-order])[
  It suffices to treat the case where $A=K'$ and $Lambda_0=R'$. But then
  $S times.o_R R'=S'$, the integral closure of $S$ in $E times.o_K K'$.
]

#exercise[
  Keep the above notation, and let $hat(S)$ be the completion of $S$ with
  respect to its valuation, and $hat(E)$ the corresponding completion of $E$.
  Show that
  #enum(
    numbering: "(i)",
    [$hat(S)$ is a complete d.v.r. with infinite residue class field.],
    [$hat(E) times.o_K A$ is a f.d. commutative separable $hat(E)$-algebra.],
    [$hat(S) times.o_R Lambda_0$ is a maximal $hat(S)$-order in
      $hat(E) times.o_K A$.],
    [If $M$ and $N$ are $Lambda$-lattices, where $Lambda$ is any $R$-order in
      $A$, then $M tilde.equiv N$ if and only if
      $
        hat(S) times.o_R M tilde.equiv hat(S) times.o_R N
        quad "as" (hat(S) times.o_R Lambda) "-lattices."
      $],
  )
] <exc:infinite-residue-completed-extension>
#hint([@exc:infinite-residue-completed-extension])[
  (i) Since $S$ is a d.v.r., its completion $hat(S)$ is also a d.v.r. with the
  same residue class field.

  (ii) is clear from §@sec:separable-algebras-splitting-fields, while (iii)
  follows from Exercise~@exc:gauss-extension-maximal-commutative-order and
  @th:maximal-orders-localization. Finally, (iv) is a consequence of
  @th:reiner-zassenhaus-local-extension-isomorphism.
]

#exercise[
  Let $Omega$ be an infinite field, and let $V$ be an $n$-dimensional
  $Omega$-space. Show that $V$ cannot be the union of a finite number of proper
  subspaces $W_1,dots,W_r$.
] <exc:infinite-field-finite-subspace-union>
#hint([@exc:infinite-field-finite-subspace-union])[Use induction on $r$.]

#exercise[
  Let $J$ be a fractional ideal in $A$. Show that $J^2 or.curly J$ if and only
  if $J$ is invertible.
] <exc:fractional-ideal-idempotent-genus>
#hint([@exc:fractional-ideal-idempotent-genus])[
  If $J^2 or.curly J$ then $J_P^2=J_P x_P$ for each $P$, with $x_P=1$ a.e. Then
  $Lambda_P=J_P x_P^(-1)$ is an $R_P$-order, and
  $Lambda=inter_P Lambda_P=inter O(J_P)=O(J)$. We have $J or.curly Lambda$, so
  $J$ is invertible.
]

#exercise[
  Let $G$ be a cyclic $p$-group with generator $x$ of order $p^m$, $R$ the ring
  of $p$-adic integers, and let $J="rad" R G=(x-1)R G+p R G$. Show that $J^m$ is
  the smallest invertible power of $J$.
] <exc:cyclic-p-group-radical-invertible-power>
#hint([@exc:cyclic-p-group-radical-invertible-power])[See Singer
  @bib:Singer1970.]

#exercise[
  Let $R$ be a d.v.r., $Lambda$ an $R$-order in a commutative separable
  $K$-algebra $A$, and let $M,N in cal(P)(Lambda)$. Show that $M tilde.equiv N$
  if and only if $K M tilde.equiv K N$.
] <exc:commutative-order-projective-generic-isomorphism>
#hint([@exc:commutative-order-projective-generic-isomorphism])[
  After passing to completions, we may assume $R$ complete. Let ${epsilon_i}$ be
  a full set of primitive idempotents in $Lambda$, and ${e_j}$ in $A$. Each
  $epsilon_i$ is a sum of $e$'s, with no overlap between different $epsilon$'s.
  If $M tilde.equiv product.co (Lambda epsilon_i)^((m_i))$, the isomorphism
  class of $K M$ determines the ${m_i}$.
]

#source(789)
In the remaining Exercises, $R$ denotes a Dedekind domain.

#exercise[
  Let $A$ be a f.d. $K$-algebra (not necessarily commutative), $Lambda$ any
  $R$-order in $A$, and $M$ a $(Lambda,Lambda)$-bimodule f.g. over $R$. Show
  that $M$ is invertible if and only if $hat(M)_P$ is invertible for each
  maximal ideal $P$ of $R$. (Here, $hat(M)_P=$ $P$-adic completion of $M$.)
] <exc:invertible-bimodule-completion>

#exercise[
  Let $A$ be a central simple $K$-algebra, $Lambda$ a hereditary $R$-order in
  $A$. For each $P$, let
  $ M(P)=Lambda inter "rad" hat(Lambda)_P. $
  Show that $M(P)$ is an invertible two-sided ideal of $Lambda$, and that
  $
    hat(R)_P times.o_R M(P)="rad" hat(Lambda)_P, quad
    hat(R)_Q times.o_R M(P) tilde.equiv hat(Lambda)_Q quad "for" Q!=P,
  $
  where $Q$ denotes a maximal ideal of $R$.
] <exc:hereditary-order-completed-radical-ideal>
#hint([@exc:hereditary-order-completed-radical-ideal])[
  Use @th:local-hereditary-orders-block-form; see @bib:Reiner1975[MO] (39.1).
]

#exercise[
  Keep the notation above. Show that the set of invertible two-sided ideals of
  $Lambda$ is a free abelian group with generators ${M(P)}$.
] <exc:hereditary-invertible-ideal-group>
#hint([@exc:hereditary-invertible-ideal-group])[See @bib:Reiner1975[MO],
  Exercise~39.6.]

#exercise[
  Let $A$ be any ring, and let $f,g,h$, etc., be automorphisms of $A$. By
  $attach(A, bl: f, br: g)$ we denote the $(A,A)$-bimodule having the same
  elements as $A$, but with the action of $A$ “twisted” by $f$ and $g$, thus:
  $ x(a)y=f(x)a g(y) quad "for all" x,y,a in A. $
  Here, ${(a):a in A}$ is the set of elements of $attach(A, bl: f, br: g)$.
  Prove that there are $(A,A)$-bimodule isomorphisms:
  $
    attach(A, bl: f, br: g)
    tilde.equiv attach(A, bl: h f, br: h g)
    tilde.equiv attach(A, bl: 1, br: f^(-1)g)
    tilde.equiv attach(A, bl: g^(-1)f, br: 1), quad
    attach(lr((attach(A, bl: f, br: g))), bl: f', br: g')
    tilde.equiv attach(A, bl: f f', br: g g'),
  $
  $
    attach(A, bl: f, br: g) times.o attach(A, bl: f', br: g')
    tilde.equiv attach(A, bl: f, br: g f'^(-1)g'), quad
    attach(A, bl: 1, br: g) times.o attach(A, bl: 1, br: g')
    tilde.equiv attach(A, bl: 1, br: g g'),
  $
  $
    attach(A, bl: 1, br: f) times.o attach(A, bl: f, br: 1)
    tilde.equiv A tilde.equiv
    attach(A, bl: f, br: 1) times.o attach(A, bl: 1, br: f),
  $
  where $times.o$ means $times.o_A$. Show further that for each $f$, the
  bimodule $attach(A, bl: 1, br: f)$ is invertible, and that
  $attach(A, bl: 1, br: f) tilde.equiv A$ as bimodules if and only if $f$ is an
  inner automorphism of $A$.
] <exc:automorphism-twisted-invertible-bimodules>
