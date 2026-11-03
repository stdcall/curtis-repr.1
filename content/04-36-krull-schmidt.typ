#import "main-defs.typ": *
#import "statements.typ": *

== The Krull-Schmidt-Azumaya Theorem over Discrete Valuation Rings
<sec:krull-schmidt-discrete-valuations>
#item-series(start: 0)

Throughout this section, we abbreviate “Krull-Schmidt-Azumaya” as K-S-A. We say
that the K-S-A Theorem is valid for a ring $Lambda$ if every f.g.
$Lambda$-module is expressible as a finite direct sum of indecomposable
$Lambda$-modules, with the summands uniquely determined up to isomorphism and
order of occurrence.#idx("Krull-Schmidt-Azumaya Theorem") We saw in
§@sec:idempotents-krull-schmidt-projective-covers that the K-S-A Theorem holds
for every artinian ring $Lambda$. It also
#source(790)
holds if $Lambda$ is an $R$-algebra f.g./$R$ as module, where $R$ is a complete
d.v.r. On the other hand, the K-S-A Theorem usually fails for $R$-orders when
$R$ is a Dedekind ring in a global field; this is already evident from
Steinitz's Theorem, when $R$ is not a P.I.D. As we shall see in this section,
the K-S-A Theorem is usually not valid when $R$ is a d.v.r. which is not
complete. Furthermore, it is usually not valid when $R$ is a semilocal ring.

Let us begin by giving a simple and useful example:

#theorem[
  Let $G$ be a finite group of order $n$, and let $R$ be a d.v.r. with quotient
  field $K$. If $n$ is a unit in $R$, then the K-S-A Theorem is valid for
  $R G$-lattices.
] <th:krull-schmidt-invertible-group-order>
#proof[
  Set $Lambda=R G$, $A=K G$. By
  Theorem~@th:invertible-group-order-lattice-isomorphism, every (left)
  $Lambda$-lattice $M$ is projective as $Lambda$-module. The last paragraph of
  the proof of @th:maximal-orders-are-hereditary, which is independent of the
  preceding part of the proof, then shows that we may write $M=plus.o M_i$,
  where each $M_i$ is a $Lambda$-lattice such that $K M_i$ is a simple
  $A$-module. Since $K M=plus.o K M_i$, the summands ${K M_i}$ are the
  composition factors of the $A$-module $K M$, and are therefore uniquely
  determined by $K M$, up to isomorphism and order of occurrence. Using
  @th:invertible-group-order-lattice-isomorphism once more, we conclude that the
  $Lambda$-lattices ${M_i}$ are uniquely determined by $M$, up to isomorphism
  and order of occurrence. This completes the proof. (An alternate approach is
  as follows: By @prop:group-ring-maximality, $Lambda$ is a maximal $R$-order in
  $A$. We then obtain the desired result as a special case of
  Exercise~@exc:maximal-order-dvr-krull-schmidt. However, the latter ultimately
  depends on Theorem~@th:maximal-orders-are-hereditary, which is a considerably
  deeper result than Theorem~@th:invertible-group-order-lattice-isomorphism used
  above.)
]

From now on, suppose that $R$ is a discrete valuation ring (d.v.r.) with maximal
ideal $P$ and quotient field $K$, and let $Lambda$ be an $R$-order in a f.d.
semisimple $K$-algebra $A$. Let $hat(R),hat(Lambda),hat(A)$, etc., denote
$P$-adic completions. We showed in §@sec:local-theory that even when $R$ is not
complete, the K-S-A Theorem may be true for $Lambda$-lattices. Specifically, if
every simple left $A$-module $S$ remains simple upon passing to $P$-adic
completions, then the K-S-A Theorem holds for $Lambda$-lattices by Heller's
Theorem~@th:heller-completion-krull-schmidt. It then also holds for all f.g.
$Lambda$-modules; see Exercise~@exc:simple-completion-krull-schmidt-all-modules.

Let us write $A$ as a direct sum of full matrix rings $M_n lr((D))$, where $D$
is a division algebra whose center $C$ is a finite extension of $K$. We have
$
  hat(K) times.o_K M_n lr((D))
  tilde.equiv M_n lr(((hat(K) times.o_K C) times.o_C D)).
$
The hypotheses of Heller's Theorem are satisfied if and only if
$hat(K) times.o_K C$ is a _field_ $hat(C)$, and furthermore $hat(C) times.o_C D$
is a division algebra, for each summand $M_n lr((D))$ of $A$. For each finite
center extension $C slash K$, the algebra $hat(K) times.o_K C$ is _local
artinian_ if and only if the $P$-adic valuation on $K$ has a unique extension to
$C$.#ed-note[
  The printed field assertion fails for inseparable centers. Choose
  $u in t bb(F)_p[[t]]$ transcendental over $bb(F)_p lr((t))$, and set
  $K=bb(F)_p lr((t,u^p))$, $C=K(u)$, $R=K inter bb(F)_p[[t]]$. Then $R$ is a
  d.v.r. with completion $bb(F)_p[[t]]$, and $R[u]$ is a finite $R$-order in
  $C$. The valuation extends uniquely to the purely inseparable field $C$, but
  $hat(K) times.o_K C tilde.equiv hat(K)[X] slash ((X-u)^p)$ is nonreduced.
] If $C slash K$ is separable, these local artinian factors are fields, so the
field criterion applies as stated above. (See
Exercise~@exc:division-algebra-completion-norm-criterion.)

In particular, suppose that $A tilde.equiv product.co_i M_(n_i) lr((K_i))$,
where each $K_i$ is a finite field extension of $K$ with a unique extension of
the $P$-adic valuation. Put $B_i=hat(K) times.o_K K_i$. Then each $B_i$ is local
artinian and $hat(A) tilde.equiv product.co_i M_(n_i) lr((B_i))$. The K-S-A
Theorem still holds for all f.g. $Lambda$-modules in this case, as follows.

Let $Q$ be a $Lambda$-lattice and let $N$ be a direct summand of $hat(Q)$. Its
generic module $hat(K)N$ is projective over $hat(A)$, since $K Q$ is projective
over the semisimple algebra $A$. Morita equivalence and freeness of finite
projectives over the local rings $B_i$ show that
$hat(K)N tilde.equiv hat(K) times.o_K V$ for a finite $A$-module $V$, with the
corresponding integer multiplicities. Identify these generic modules. The dense
subspace $V$ contains vectors sufficiently close to an $hat(R)$-basis of $N$ to
form another such basis. Let $L_0$ be their $R$-span and put
$L=Lambda L_0 subset.eq V$. Then $L$ is finite and $R$-torsionfree, and
$hat(L)=N$. Thus every summand of an original completed lattice descends; this
does not assert descent of arbitrary completed lattices.

#source(791)
Now let $M$ be any f.g. $Lambda$-module and $N$ a summand of $hat(M)$. Its
torsionfree quotient is a summand of the completion of $M slash "torsion"(M)$,
so descends to a lattice $L$ by the preceding argument. Its torsion submodule
descends to a finite torsion module $U$, since it is killed by some $pi^a$ and
$hat(Lambda) slash pi^a hat(Lambda) tilde.equiv Lambda slash pi^a Lambda$. The
ring $Lambda$ is noetherian, being finite over $R$. A free resolution with
finite terms and flat completion give
$
  "Ext"_(hat(Lambda))^1 lr((hat(L),hat(U)))
  tilde.equiv hat(R) times.o_R "Ext"_Lambda^1 lr((L,U))
  tilde.equiv "Ext"_Lambda^1 lr((L,U)),
$
because the last group is finite and killed by $pi^a$. Hence the extension
defining $N$ descends to a finite $Lambda$-module.

Finally, decompose $hat(M)$ into indecomposables over the complete order
$hat(Lambda)$ and descend its summands. Their sum is isomorphic to $M$ by
@prop:module-isomorphism-completion, which applies to all finite modules. The
same descent shows that an indecomposable original module has indecomposable
completion; uniqueness follows from complete-local K-S-A and
@prop:module-isomorphism-completion.

This situation arose in §@ss:cyclic-p-group-lattices, where $Lambda=ZZ_p G$ with
$ZZ_p$ the localization of $ZZ$ at $p$, and $G$ a cyclic $p$-group. Jones
@bib:Jones1965 (see also Jacobinski @bib:Jacobinski1968b) proved the following
more general result:

#theorem[
  Let $G$ be a $p$-group, where $p$ is an odd prime. Then the K-S-A Theorem
  holds for $ZZ_p G$-lattices.
] <th:krull-schmidt-odd-p-group-lattices>
#idx("Jones' Theorem", target: [@th:krull-schmidt-odd-p-group-lattices])
#idx("Jacobinski's Theorem", target: [@th:krull-schmidt-odd-p-group-lattices])
#proof[
  By Chapter~6 of Volume~II, we have
  $
    QQ G tilde.equiv product.co_(i=1)^s M_(n_i) lr((K_i)),
    quad "where" K_i=QQ(omega_i),
  $
  where each $omega_i$ is a root of 1 of order a power of $p$. But $p$ is
  completely ramified in each $K_i$, so the $p$-adic valuation extends uniquely
  to $K_i$. The result now follows from our remarks above.
]

Jones @bib:Jones1965 also proved:

#theorem[
  Let $G$ be a nilpotent group of odd order, and suppose $G$ has exponent
  $q p^d$, where $p$ is prime, $p divides.not q$, and either $q=1$ or else $p$
  is a primitive root#footnote[
    This means that $phi(q)$ is the least positive integer $t$ such that
    $p^t equiv 1 (mod q)$.
  ] mod~$q$. Then the K-S-A Theorem holds for $ZZ_p G$-lattices.
] <th:krull-schmidt-nilpotent-group-primitive-root>
#idx("primitive root")
#proof[
  The cases where $q=1$ or $d=0$ are already settled by
  @th:krull-schmidt-invertible-group-order and
  @th:krull-schmidt-odd-p-group-lattices, but will be needed here as part of the
  argument below. Let $hat(ZZ),hat(QQ)$, etc., denote $p$-adic completions. It
  suffices to show that for each simple $QQ G$-module $V$, the completion
  $hat(V)$ is a simple $hat(QQ) G$-module. We shall use the result from
  Chapter~6 of Volume~II that since $G$ is a nilpotent group of odd order, the
  Schur index $m_QQ lr((V))$ equals 1. This means that for each extension field
  $K$ of $QQ$, the $K G$-module $K times.o_QQ V$ has no repeated summands. In
  particular, $hat(V)$ has this property.

  Suppose first that $H=chevron.l x chevron.r$ is a cyclic subgroup of $G$, and
  that $V=QQ[x] slash (Phi_m lr((x)))$ is a simple $QQ H$-module, where
  $Phi_m lr((x))$ is the cyclotomic polynomial of order $m$. We shall show that
  the completion $hat(V)$ is a simple $hat(QQ) H$-module. Since $q$ is odd,
  there exist primitive roots (mod~$q$) if and only if $q$ is a prime power (see
  Niven and Zuckerman @bib:Niven1980, §2.9). Therefore we may write
  $m=q' p^(d')$ where $q' divides q$, $d'<=d$, and where $p$ is a primitive root
  (mod~$q'$) if $q'!=1$. Changing notation for convenience, suppose that
  $m=q p^d$. We have $V=QQ[x] slash (Phi_m lr((x)))$ and we need only check that
  $Phi_m lr((x))$ is irreducible in $hat(QQ)[x]$. When $q=1$, this is clear from
  §@ss:cyclotomic-fields. On the other hand, suppose $q>1$. We may write
  $ overline(Phi)_m lr((x))=(overline(Phi)_q lr((x)))^(phi(p^d)), $
  #source(792)
  where bars denote reduction mod~$p$. If $theta$ is a primitive $q$-th root of
  1 over $QQ$, then the zeros of $Phi_q lr((x))$ are
  ${theta^(p^i):0<=i<=phi(q)-1}$. Their images ${overline(theta)^(p^i)}$ are
  then the zeros of $overline(Phi)_q lr((x))$, and they are mutually conjugate
  over $overline(ZZ)$. It follows that $overline(Phi)_q lr((x))$ is irreducible
  in $overline(ZZ)[x]$. An easy argument, left to the reader, then shows that
  $hat(V)$ is a simple $hat(QQ) H$-module. We have thus shown, under our
  hypotheses, that for each cyclic subgroup $H$ of $G$, every simple
  $hat(QQ) H$-module is the completion of a simple $QQ H$-module.

  We are now ready to prove that for each simple $QQ G$-module $V$, its
  completion $hat(V)$ is a simple $hat(QQ) G$-module. By the remarks at the
  beginning of the proof, we may write
  $hat(V) tilde.equiv product.co_(i=1)^r W_i$, where the ${W_i}$ are
  non-isomorphic simple $hat(QQ) G$-modules. Let $i$ be fixed, $1<=i<=r$. By the
  Artin Induction Theorem, there exist cyclic subgroups ${H_j}$ of $G$ and
  $hat(QQ) H_j$-modules $Y_j$ such that
  $ W_i^((n)) plus.o product.co (Y_j)^G tilde.equiv product.co (Y_k)^G, $
  where $n=|G|$. Since each $Y_j$ is a direct sum of simple
  $hat(QQ) H_j$-modules, the preceding step shows that
  $Y_j tilde.equiv hat(X)_j$ for some $QQ H_j$-module $X_j$. Thus we obtain
  $
    W_i^((n)) plus.o product.co (hat(X)_j)^G
    tilde.equiv product.co (hat(X)_k)^G.
  $
  But then (see Exercise~@exc:semisimple-scalar-extension-complement) we have
  $W_i^((n)) tilde.equiv hat(T)_i$ for some $QQ G$-module $T_i$. This gives
  $hat(V)^((n)) tilde.equiv product.co_(i=1)^r hat(T)_i$, so
  $V^((n)) tilde.equiv product.co_(i=1)^r T_i$ by the Noether-Deuring Theorem
  (Exercise~@exc:noether-deuring). Therefore each $T_i$ is a sum of copies of
  $V$, and consequently each $W_i$ is a sum of copies of $hat(V)$. This shows
  that $r=1$ and $W_1=hat(V)$, so $hat(V)$ is simple, and the theorem is
  established.
]

The converse of this result holds when $G$ is abelian (Jones @bib:Jones1965):

#proposition[
  Let $G$ be an abelian group of exponent $q p^d$, where $p divides.not q$. Then
  the K-S-A Theorem holds for $ZZ_p G$-lattices if and only if either $d=0$,
  $q=1$, or $p$ is a primitive root mod~$q$.
] <prop:krull-schmidt-abelian-group-criterion>
#idx("Jones' Theorem", target: [@prop:krull-schmidt-abelian-group-criterion])
#proof[
  If $d=0$, use @th:krull-schmidt-invertible-group-order. For $d>0$, the
  preceding proof applies when $q=1$ or $p$ is a primitive root mod~$q$; abelian
  character Schur indices are 1, without an odd-order assumption. Conversely,
  suppose that $d>0$, $q!=1$, and that $p$ is _not_ a primitive root mod~$q$.
  Let $S=ZZ_p[theta]$, where $theta$ is a primitive $q$-th root of 1 over $QQ$.
  Then $S$ is the integral closure of $ZZ_p$ in $QQ(theta)$, and
  $p S=P_1 dots P_g$, where $g=phi(q) slash ("order of" p mod q)$, so $g>1$.
  Thus $S$ is semilocal but not local.

  Now $G$ has a factor group $H$ which is cyclic of order $p q$, and there is a
  surjection $ZZ_p H->S[x] slash (x^p-1)=Gamma$ (say), obtained by mapping the
  generator of $H$ of order $q$ onto $theta$, and the generator of $H$ of order
  $p$ onto $x$. Then $Gamma$ is a homomorphic image of $ZZ_p G$, and we need
  only verify that the K-S-A Theorem fails for $Gamma$-lattices. However,
  $Gamma$ is indecomposable since the localization $(Gamma)_(P_i)$ is
  indecomposable by @cor:p-group-ring-local-base. Further, $(Gamma)_(P_i)$ is
  not a maximal order
  #source(793)
  for $i=1,2,dots,g$. The desired result now follows as a special case of
  @th:jacobinski-krull-schmidt-failure below.
]

The next result, due to Jacobinski, includes as special cases many of the
examples where it has been shown that the K-S-A Theorem fails.

#theorem[
  Let $R$ be a semilocal#footnote[
    We depart here from our earlier assumption that $R$ is a d.v.r., but we
    suppose that $Lambda$ is an $R$-order in a _separable_ f.d. $K$-algebra $A$.
  ] Dedekind domain, and let $Lambda$ be an $R$-order which cannot be decomposed
  into a direct sum of two non-zero two-sided ideals. Suppose there are at least
  two maximal ideals $P$ of $R$ for which the localization $Lambda_P$ is not a
  maximal $R_P$-order in $A$. Then the K-S-A Theorem fails for
  $Lambda$-lattices.
] <th:jacobinski-krull-schmidt-failure>
#idx("Jacobinski's Theorem", target: [@th:jacobinski-krull-schmidt-failure])
#proof[
  Let $Lambda'$ be a maximal $R$-order in $A$ containing $Lambda$, and let
  ${P_i:1<=i<=k}$ be the set of maximal ideals of $R$ for which
  $Lambda_(P_i)!=Lambda'_(P_i)$. Then $k>=2$, by hypothesis.

  For $M$ a $Lambda$-lattice, and $P$ any maximal ideal of $R$, the localization
  $M_P$ is clearly a $Lambda$-lattice. We note that $Lambda'_P$ is an order
  containing $Lambda_P$, and $M_P$ may fail to be a $Lambda'_P$-lattice, since
  $Lambda'_P M_P$ (computed inside $K M$) need not be contained in $M_P$. We
  shall call the $Lambda$-lattice $M$ “good” at $P$ if $M_P$ is a
  $Lambda'_P$-lattice, and otherwise “bad”. Thus, the $Lambda$-lattice $Lambda$
  itself is bad at $P$ precisely for $P=P_1,dots,P_k$.

  For each $i$, $1<=i<=k$, let $X_i$ be a maximal element in the set of
  $Lambda'_(P_i)$-direct summands of $Lambda_(P_i)$. Then we may write
  $ Lambda_(P_i)=X_i plus.o Y_i, $ <eq:nonmaximal-order-good-bad-decomposition>
  where $X_i$ is a $Lambda'_(P_i)$-lattice, and where the $Lambda_(P_i)$-lattice
  $Y_i$ is nonzero, and $Y_i$ has no $Lambda'_(P_i)$-direct summand. Now define
  $epsilon_i$ to be the sum of all central primitive idempotents $e_j$ of $A$
  for which $e_j Y_i!=0$. Then $Y_i=epsilon_i Y_i$, and since
  $epsilon_i in Lambda'$ by @th:maximal-orders-wedderburn-components, it follows
  from @eq:nonmaximal-order-good-bad-decomposition that
  $epsilon_i in Lambda_(P_i)$.

  If $epsilon_1 Y_i=0$ for $i=2,dots,k$, the same argument shows that
  $epsilon_1 in Lambda_(P_i)$ for each $i>=2$. Since $Lambda=inter_P Lambda_P$,
  where $P$ ranges over all maximal ideals of $R$, it follows that
  $epsilon_1 in Lambda$. But $Lambda$ is assumed indecomposable, so
  $epsilon_1=0$ or 1, and clearly both choices are impossible. Therefore
  $epsilon_1 Y_i!=0$ for some $i>=2$, so we may assume that $epsilon_1 Y_2!=0$.
  Therefore there exists a central primitive idempotent $e in A$ for which
  $e Y_1!=0$, $e Y_2!=0$.

  Now let $N$ be an indecomposable $Lambda_(P_1)$-direct summand of $Y_1$ such
  that $e N!=0$. From the way in which $Y_1$ was chosen, $N$ is not a
  $Lambda'_(P_1)$-lattice. By @prop:localization-completion-lattices, we can now
  find a full $Lambda$-lattice $L_1$ in $K N$ such that $(L_1)_(P_1)=N$, and
  $L_1$ is “good” at all other maximal ideals $P$ of $R$ different from $P_1$.
  Choose $L_2$ analogously, thus obtaining a pair of indecomposable
  $Lambda$-lattices $L_1$ and $L_2$
  #source(794)
  such that
  $ e L_i!=0, quad L_i "is good except at" P_i, quad i=1,2. $

  Let ${S_j}$ be a basic set of simple left $A$-modules, and let
  $
    K L_1 tilde.equiv product.co S_j^((m_j)), quad
    K L_2 tilde.equiv product.co S_j^((n_j)).
  $
  Since both $e L_1$ and $e L_2$ are nonzero, it follows that $min(m_j, n_j)!=0$
  for some $j$. We now define
  $ V=product.co S_j^(max(m_j, n_j)), quad V'=product.co S_j^(min(m_j, n_j)), $
  so $V$ and $V'$ are nonzero $A$-modules, and
  $K(L_1 plus.o L_2) tilde.equiv V plus.o V'$. We may write
  $ V=K L_1 plus.o W_1, quad V=K L_2 plus.o W_2, $
  for some $A$-modules $W_1,W_2$. We now choose a full $Lambda$-lattice $M$ in
  $V$ according to the conditions
  #enum(
    numbering: "(i)",
    [$M_(P_1)=(L_1)_(P_1) plus.o (N_1)_(P_1)$, where $N_1$ is a full
      $Lambda'$-lattice in $W_1$,],
    [$M_(P_2)=(L_2)_(P_2) plus.o (N_2)_(P_2)$, where $N_2$ is a full
      $Lambda'$-lattice in $W_2$,],
    [$M$ is good at all $P$'s different from $P_1$ and $P_2$.],
  )
  Then $M$ is a $Lambda$-direct summand of $L_1 plus.o L_2$, since this holds
  locally, and since $R$ is semilocal (see the discussion at the end of
  §@ss:genus-basic-properties). Thus
  $ L_1 plus.o L_2 tilde.equiv M plus.o M', $
  where $M'$ is a full $Lambda'$-lattice in $V'$. But this gives a
  counterexample to the K-S-A Theorem, since $L_1$ and $L_2$ are indecomposable,
  whereas each indecomposable summand of $M'$ must be a $Lambda'$-lattice. This
  completes the proof of @th:jacobinski-krull-schmidt-failure.
]

Before giving further examples in which the K-S-A Theorem fails to hold, we
prove an interesting result due to Roggenkamp @bib:Roggenkamp1969:

#theorem[
  Let $Lambda$ be an $R$-order in a commutative separable f.d. $K$-algebra $A$,
  where $R$ is a d.v.r. with quotient field $K$. Then the K-S-A Theorem holds
  for projective $Lambda$-lattices.
] <th:roggenkamp-commutative-projective-krull-schmidt>
#idx(
  "Roggenkamp's Theorem",
  target: [@th:roggenkamp-commutative-projective-krull-schmidt],
)
#proof[
  If $Lambda$ decomposes as $product.co Lambda_i$, there is a corresponding
  decomposition for $Lambda$-lattices. Hence it suffices to prove the result
  when $Lambda$ is indecomposable, which we assume from now on. Let
  $hat(Lambda),hat(A)$, etc., denote completions, and let ${epsilon_i}$ be a
  full set of primitive idempotents in $hat(Lambda)$, ${e_j}$ a full set in
  $hat(A)$, and ${a_k}$ a
  #source(795)
  full set in $A$, so each $epsilon_i$ is a sum of $e_j$'s, with no overlaps.
  The same holds for each $a_k$.

  In order to prove that the K-S-A Theorem holds for projective
  $Lambda$-lattices, it suffices to show that the only indecomposable projective
  $Lambda$-lattice is $Lambda$ itself. Let $M in cal(P)(Lambda)$ be
  indecomposable, $M!=0$, and write
  $
    hat(M)=product.co_i (hat(Lambda) epsilon_i)^((m_i)), quad
    K M=product.co_k (A a_k)^((r_k)).
  $
  Suppose first that $K M subset.eq A$, whence
  $hat(K)hat(M) subset.eq hat(A)=product.co hat(A)e_j$. It follows that each
  $m_i$ is 0 or 1, say $m_1=dots=m_r=1$, $m_i=0$ for $i>r$. Let
  $N_0=product.co_(i>r) hat(Lambda) epsilon_i$, so
  $hat(M) plus.o N_0=hat(Lambda)$. We may choose an $A$-module $X$ such that
  $K M plus.o X=A$, and then $hat(K) N_0 tilde.equiv hat(K) X$. Identifying
  $hat(K) N_0$ with $hat(K) X$, and setting $N=X inter N_0$, we see that $N$ is
  a $Lambda$-lattice such that $hat(N)=N_0$. Thus $N in cal(P)(Lambda)$, and we
  have $K(M plus.o N)=K Lambda$; hence $M plus.o N tilde.equiv Lambda$ by
  Exercise~@exc:commutative-order-projective-generic-isomorphism, whence
  $M=Lambda$ since $Lambda$ is indecomposable.

  On the other hand, if $K M subset.not.eq A$ then for some $r>=1$ we have
  $m_1>=2,dots,m_r>=2$, $m_i<=1$ for $i>r$. Thus $hat(K)hat(M)$ must also have
  repeated summands, whence so must $K M$. Indeed, if $epsilon_i$ and $a_k$ have
  a common summand $e_j$, then we have $m_i=r_k$. Hence we can assume (after
  renumbering the ${r_i}$ if need be) that $r_1>=2,dots,r_t>=2$, $r_i<=1$ for
  $i>t$. But then
  $
    hat(K) dot product.co_(i=1)^r (hat(Lambda)epsilon_i)^((m_i))
    tilde.equiv hat(K) dot product.co_(k=1)^t (A a_k)^((r_k)),
  $
  which implies (by consideration of idempotents) that
  $
    hat(K) dot product.co_(i=1)^r hat(Lambda)epsilon_i
    tilde.equiv hat(K) dot product.co_(k=1)^t A a_k.
  $
  Thus there exists an $N in cal(P)(Lambda)$ with
  $hat(N)=product.co_(i=1)^r hat(Lambda)epsilon_i$. Therefore
  $hat(N) divides hat(M)$, and so $N divides M$ by
  Exercise~@exc:module-summand-completion. This contradicts the fact that $M$ is
  indecomposable, and completes the proof.
]

To conclude this section, we give some more examples where the K-S-A Theorem
fails. Returning to our original notation, let $R$ be a d.v.r. with maximal
ideal $P=pi R$, quotient field $K$, and let $Lambda$ be an $R$-order in a
separable $K$-algebra $A$. Let $hat(R),hat(Lambda)$, etc., denote $P$-adic
completions.

#example[
  Let $L$ be a finite separable extension field of $K$, $S$ the integral closure
  of $R$ in $L$, and suppose that $P S=P_1 P_2$, where $P_1$ and $P_2$ are
  distinct maximal ideals of the semilocal Dedekind domain $S$. Let
  $pi_i S=P_i$, $i=1,2$, and let $S_i$ be the $P_i$-adic completion of $S$, and
  $L_i$ the quotient field of $S_i$. Then $hat(L) tilde.equiv L_1 plus.o L_2$,
  $hat(S) tilde.equiv S_1 plus.o S_2$.

  #source(796)
  We choose $A=M_2 lr((L))$, and set
  $
    Lambda=mat(S, S; P S, S) =R "-order in" A
    =S "-order in the" L "-algebra" A.
  $
  Then
  $
    hat(Lambda) tilde.equiv
    mat(S_1, S_1; pi_1 S_1, S_1) plus.o
    mat(S_2, S_2; pi_2 S_2, S_2)=Gamma_1 plus.o Gamma_2, quad "say."
  $
  For $i=1,2$, we note that $Gamma_i$ is a hereditary $S_i$-order, and that
  $Gamma_i slash "rad" Gamma_i tilde.equiv overline(S)_i plus.o overline(S)_i$,
  where $overline(S)_i=S_i slash pi_i S_i$. Thus $Gamma_i$ has two
  non-isomorphic indecomposable projective modules $Gamma_i e_0^((i))$,
  $Gamma_i e_1^((i))$, where $e_0^((i))=mat(0, 0; 0, 1)$,
  $e_1^((i))=mat(1, 0; 0, 0)$. Since $hat(Lambda)$ is hereditary, it follows
  that $Lambda$ is also a hereditary order, and each $Lambda$-lattice is
  projective.

  Now define
  $ M_(a b)=mat(S; P_1^a P_2^b), quad a=0,1, b=0,1, $
  so $M_(a b)$ is an indecomposable $Lambda$-lattice for which
  $ hat(M)_(a b)=Gamma_1 e_a^((1)) plus.o Gamma_2 e_b^((2)). $
  Hence we obtain
  $ M_(0 0) plus.o M_(1 1) tilde.equiv M_(0 1) plus.o M_(1 0). $
  However, $M_(0 0)$ is not isomorphic to $M_(0 1)$ or $M_(1 0)$, since these
  lattices have different completions. The example is due to Roggenkamp
  @bib:Roggenkamp1969, and shows that the K-S-A Theorem need not hold for
  projective $Lambda$-lattices. For further examples of this nature, see
  Roggenkamp @bib:Roggenkamp1970, p.~210.
] <exm:roggenkamp-hereditary-krull-schmidt-failure>

Note that in the above paragraph, $S$ is a semilocal ring and $Lambda$ is a
hereditary $S$-order. Thus, the K-S-A Theorem also fails for projective lattices
in the semilocal case. For other semilocal examples, see Reiner @bib:Reiner1962.

If $R_0$ is a d.v.r. in a field $K_0$, we may sometimes find a finite extension
$K$ of $K_0$, such that the integral closure $R$ of $R_0$ in $K$ is semilocal
rather than local. Each $R$-order $Lambda$ is then also an
$R_0$-order#footnote[See Exercise~@exc:lattices-integral-base-change.], and we
can then proceed to find counterexamples to the K-S-A Theorem for this case.
Thus, even though $R_0$ is a d.v.r., the K-S-A Theorem may fail for
$R_0$-orders. Of course, when $R_0$ is complete, then $R$ is itself a d.v.r.,
and so this method of producing counterexamples no longer applies.

#source(797)
For more counterexamples, see Berman-Gudivok @bib:Berman1962, Dress
@bib:Dress1970, Heller @bib:Heller1961a, Kneser @bib:Kneser1966, Roggenkamp
@bib:Roggenkamp1970.

Jacobinski @bib:Jacobinski1975 obtains necessary and sufficient conditions for
the validity of the K-S-A Theorem for lattices over an order, in the global
case.

#exercises-heading

#exercise[
  Let $Lambda$ be an $R$-order in a $K$-algebra $A$, where $R$ is a d.v.r. with
  completion $hat(R)$. Suppose that for each simple $A$-module $S$, its
  completion $hat(S)$ is a simple $hat(A)$-module. Prove that the K-S-A Theorem
  holds for all f.g. $Lambda$-modules.
] <exc:simple-completion-krull-schmidt-all-modules>
#hint([@exc:simple-completion-krull-schmidt-all-modules])[
  By @th:heller-completion-krull-schmidt, each $hat(Lambda)$-lattice is of the
  form $hat(L)$ for some $Lambda$-lattice $L$. To prove the analogous statement
  for an arbitrary f.g. $hat(Lambda)$-module $X$, we express $X$ as an extension
  $0->T->X->Y->0$, with $T$ the $hat(R)$-torsion submodule of $X$, and $Y$ a
  $hat(Lambda)$-lattice. Then $T=hat(U)$, $Y=hat(L)$, for some $R$-torsion
  $Lambda$-module $U$ and some $Lambda$-lattice $L$. But
  $
    "Ext"_(hat(Lambda))^1 lr((hat(L),hat(U)))
    tilde.equiv hat(R) times.o_R "Ext"_Lambda^1 lr((L,U))
    tilde.equiv "Ext"_Lambda^1 lr((L,U)),
  $
  the last since $"Ext"_Lambda^1 lr((L,U))$ is an $R$-torsion module. Hence $X$
  is the completion of some $Lambda$-extension of $L$ by $U$.
]

#exercise[
  Let $Lambda$ be any $R$-order, where $R$ is a d.v.r. Does the K-S-A Theorem
  for $Lambda$-lattices imply the K-S-A Theorem for f.g. $Lambda$-modules?
] <exc:lattice-krull-schmidt-implies-module-question>

#exercise[
  Let $K$ be a global field, $D$ a skewfield with index $m$ and center $C$,
  where $dim_K C<infinity$. Let $D$ be expressed as a cyclic algebra
  $(L slash C,sigma,a)$, where $L slash C$ is a Galois extension with cyclic
  Galois group $chevron.l sigma chevron.r$ of order $m$, and where $a in C^dot$
  (here, $C^dot=C-{0}$). Let $hat(K)$ be the completion of $K$ at some prime $P$
  of $K$. Show that $hat(K) times.o_K D$ is a skewfield if and only if the
  following two conditions hold:
  #enum(
    numbering: "(i)",
    [The $P$-adic valuation on $K$ extends uniquely to a $P'$-adic valuation on
      $L$,],
    [If $hat(L)$ denotes the $P'$-adic completion of $L$, then $m$ is the least
      positive integer $t$ such that
      $a^t in N_(hat(L) slash hat(C)) lr((hat(L)^dot))$, where $N$ denotes the
      norm map.],
  )
] <exc:division-algebra-completion-norm-criterion>
#hint([@exc:division-algebra-completion-norm-criterion])[
  Use the results in @bib:Reiner1975[MO] §30. We have
  $ hat(K) times.o_K D tilde.equiv (hat(K) times.o_K C) times.o_C D, $
  so if $hat(K) times.o_K D$ is to be a skewfield, we must have
  $hat(K) times.o_K C=hat(C)="field"$. Further,
  $
    hat(C) times.o_C (L slash C,sigma,a)
    tilde.op (hat(L) slash hat(C),sigma^k,a),
  $
  where $tilde.op$ means equality in the Brauer group over $hat(C)$. Here,
  $chevron.l sigma^k chevron.r="Gal"(hat(L) slash hat(C))$, where $hat(L)$ is
  some completion of $L$ containing $hat(C)$. If $hat(C) times.o_C D$ is to be a
  skewfield, we must have $k=1$, that is, $dim_(hat(C)) hat(L)=dim_C L$, and
  also condition~(ii) must be satisfied.
]

#exercise[
  Let $Lambda$ be a maximal $R$-order in a separable $K$-algebra, where $R$ is a
  d.v.r. Show that the K-S-A Theorem holds for $Lambda$-lattices.
] <exc:maximal-order-dvr-krull-schmidt>
#hint([@exc:maximal-order-dvr-krull-schmidt])[
  Use Exercise~@exc:dvr-maximal-order-lattice-isomorphism.
]
