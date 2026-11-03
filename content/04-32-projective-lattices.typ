#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/32-projective-lattices.typ": (
  projective-completion-diagram, projective-extension-diagram,
  projective-induction-diagram, projective-reduction-diagram,
  trace-base-change-diagram,
)

#heading(level: 2)[
  Projective Lattices over Group Rings; Swan’s Theorem
] <sec:projective-lattices>

Throughout this section, let $G$ denote a finite group of order $n$, and let $R$
be a Dedekind domain with quotient field $K$. Our aim here is to prove a
remarkable result due to Swan @bib:Swan1960, stating that under certain mild
hypotheses, every
#source(693)
f.g. projective $R G$-module is locally free (that is, lies in the same genus as
a free module). This result is of basic importance in the applications of
integral representation theory to topological questions (see Milnor
@bib:Milnor1971). We shall begin with a study of the local case, where $R$ is a
discrete valuation ring; all of the difficulty of the proof is concentrated in
this case. Then we shall apply the local results to obtain information about the
global case.

=== Local Case <ss:projective-lattices-local-case>

In this subsection, let $R$ be a d.v.r. with maximal ideal $P=pi R$, quotient
field $K$, and residue class field $overline(R)=R slash P$. We wish to study
f.g. projective $R G$-modules, where $G$ is a finite group. Each such module is
of course $R$-torsionfree and $R$-projective, and we shall therefore call such
modules projective (left) $R G$-lattices. The key result is as follows:

#theorem[
  Let $M$ and $N$ be projective $R G$-lattices such that $K M tilde.equiv K N$
  as $K G$-modules. Then $M tilde.equiv N$ as $R G$-modules.
  #idx(
    "Swan's Theorem",
    target: [@th:local-projective-group-lattice-cancellation],
  )
] <th:local-projective-group-lattice-cancellation>

Swan's original proof depended on the non-singularity of the Cartan matrix (see
§§@sec:cartan-brauer-triangle, @sec:induction-arbitrary-fields), and this
version of it may be found in §@sec:induction-arbitrary-fields; see also
Exercise~@exc:projective-character-isomorphism-cartan or
@bib:CurtisReiner1962[CR] (77.14). Here we shall follow another approach, due to
Hattori @bib:Hattori1965, in which
@th:local-projective-group-lattice-cancellation is established in a much more
general situation. We begin with a trivial lemma about group rings, after
introducing some notation. For $Lambda$ any $R$-order, we set #numbered-block[
  $
    [Lambda,Lambda]={sum_(i=1)^k (a_i b_i-b_i a_i):a_i,b_i in Lambda,k>=1},
    quad Lambda^ast=Lambda slash [Lambda,Lambda].
  $
] <eq:order-commutator-quotient>
Clearly $Lambda^ast$ is an $R$-module, and we have:

#lemma[
  Let $Lambda=R G$ be the integral group ring of a finite group $G$ over any
  commutative ring $R$. Then $Lambda^ast$ is $R$-torsionfree.
] <lem:group-ring-commutator-quotient-free>

#proof[
  Let $x$ range over a full set of non-conjugate elements of $G$, and let $C_x$
  be the class sum (in $R G$) of all conjugates of $x$. If $y=t x t^(-1)$ with
  $t in G$, then $y-x in [Lambda,Lambda]$, and hence the image $x^ast$ (of $x$
  in $Lambda^ast$) depends only on the conjugacy class of $x$.

  Let $c(Lambda)$ be the center of $Lambda$, so
  $ c(Lambda)=plus.o.big_x R C_x. $
  Define $phi in Hom_R lr((c(Lambda),Lambda^ast))$ by $phi(C_x)=x^ast$ for each
  $x$. Next, define $psi in Hom_R lr((Lambda,c(Lambda)))$ by $psi(y)=C_y$,
  $y in G$. Every element of $[Lambda,Lambda]$ is an
  #source(694)
  $R$-linear combination of expressions of the form $y z-z y$, with $y,z in G$;
  since $y z$ and $z y$ are conjugate, it follows that $psi[Lambda,Lambda]=0$,
  so $psi$ induces an $R$-map $psi:Lambda^ast -> c(Lambda)$. Clearly $phi$ and
  $psi$ are inverses of one another, so $Lambda^ast tilde.equiv c(Lambda)$ as
  $R$-modules, and thus $Lambda^ast$ is $R$-free.
]

Our next lemma concerns the structure of $R G slash rad R G$ for the case where
$R$ is local:

#lemma[
  Let $R$ be a d.v.r. with residue class field $overline(R)$, and let $G$ be a
  finite group. Then $R G slash rad R G$ is a separable algebra over the field
  $overline(R)$.
] <lem:group-ring-residue-separable>

#proof[
  Let $Lambda=R G$, and set $overline(Lambda)=Lambda slash P=overline(R) G$.
  Then by @prop:local-theory-radical-completion we have
  $
    Lambda slash rad Lambda tilde.equiv overline(Lambda) slash rad
    overline(Lambda).
  $
  But the latter expression is a separable $overline(R)$-algebra by
  @th:group-algebra-separable-radical-quotient, so we are done.
]

We are now ready to prove @th:local-projective-group-lattice-cancellation, and
amazingly enough, the proof requires only the two properties of the group ring
$R G$ given in the lemmas above. We shall prove the following more general
version of @th:local-projective-group-lattice-cancellation, due to Hattori
@bib:Hattori1965:

#theorem[
  Let $R$ be a d.v.r., and let $Lambda$ be any $R$-order in a $K$-algebra $A$,
  satisfying the conditions:
  #idx(
    "Hattori's Theorem",
    target: [@th:hattori-projective-lattice-cancellation],
  )
  #enum(
    numbering: "(i)",
    [$Lambda^ast$ is $R$-torsionfree, where $Lambda^ast$ is defined as in
      @eq:order-commutator-quotient, and],
    [$overline(Lambda) slash rad overline(Lambda)$ is a separable
      $overline(R)$-algebra (where bars denote reduction mod $P$).],
  )
  Then for any pair of projective left $Lambda$-lattices $M$ and $N$,
  $
    K M tilde.equiv K N "as" A"-modules" <=> M tilde.equiv N "as"
    Lambda"-modules".
  $
] <th:hattori-projective-lattice-cancellation>

#proof[
  Step 1. Let $hat(R)$ be the $P$-adic completion of $R$, and let $hat(Lambda)$,
  $hat(M)$, etc., denote $P$-adic completions. We find at once that
  $
    hat(Lambda)^ast tilde.equiv hat(R) times.o_R Lambda^ast,
    quad hat(Lambda) slash rad hat(Lambda) tilde.equiv Lambda slash rad Lambda,
    quad hat(R) slash P hat(R) tilde.equiv overline(R)
  $
  (see Exercise~@exc:radical-completion). Thus $hat(Lambda)$ satisfies the same
  hypotheses as $Lambda$. Further, $hat(M)$ and $hat(N)$ are projective
  $hat(Lambda)$-lattices, and from $K M tilde.equiv K N$ we obtain
  $hat(K) hat(M) tilde.equiv hat(K) hat(N)$. If we can deduce from this that
  $hat(M) tilde.equiv hat(N)$, then using @prop:module-isomorphism-completion we
  obtain $M tilde.equiv N$, as desired. Hence it suffices to prove the result
  when $R$ is replaced by $hat(R)$. Changing notation, we assume for the rest of
  the proof that $R$ is a complete d.v.r.

  #source(695)
  Our next step will be to replace $R$ by a larger d.v.r. $S$ in some finite
  unramified extension $L$ of $K$. Set
  $
    Lambda_1=S times.o_R Lambda, quad M_1=S times.o_R M, quad N_1=S times.o_R N,
  $
  so $M_1$ and $N_1$ are projective $Lambda_1$-lattices, and $Lambda_1$ is an
  $S$-order in the $L$-algebra $L times.o_K A$. The proof of
  @th:local-extension-indecomposable-endomorphism-correspondence shows at once
  that
  $
    Lambda_1 slash rad Lambda_1 tilde.equiv overline(S) times.o_(overline(R))
    (overline(Lambda) slash rad overline(Lambda)),
  $
  using @prop:local-theory-radical-completion and the hypothesis that
  $overline(Lambda) slash rad overline(Lambda)$ is a separable
  $overline(R)$-algebra.

  As in the proof of @cor:absolute-indecomposable-unramified-extension, we may
  choose $overline(S)$ to be a splitting field for
  $overline(Lambda) slash rad overline(Lambda)$ over $overline(R)$, and
  $overline(S)$ can be realized as the residue class field of some d.v.r. $S$.
  Thus $Lambda_1 slash rad Lambda_1$ is a split semisimple
  $overline(S)$-algebra. From $K M tilde.equiv K N$ we obtain
  $L M_1 tilde.equiv L N_1$. If we can deduce from this that
  $M_1 tilde.equiv N_1$, then we obtain the desired isomorphism
  $M tilde.equiv N$, by @th:reiner-zassenhaus-local-extension-isomorphism.
  Changing notation once more, we may assume from here on that
  $Lambda slash rad Lambda$ is a split semisimple $overline(R)$-algebra.

  Step 2. In this step, $Lambda$ is an arbitrary ring, and $M$ is a f.g.
  projective left $Lambda$-module. We put $E(M)=End M$, and view $M$ as a
  $(Lambda,E(M))$-bimodule. Set $M'=Hom_Lambda lr((M,Lambda))$, a right
  $Lambda$-module. By §@ss:morita-theorems (see also
  @prop:projective-endomorphism-dual-tensor), there is a two-sided
  $E(M)$-homomorphism $mu:M' times.o_Lambda M -> E(M)$, given by
  $
    mu(f times.o x)=[f,x], quad "where" y[f,x]=f(y)x
    "for all" x,y in M,f in M'.
  $
  The map $mu$ is an isomorphism by Morita's Theorem @th:morita, since $M$ is a
  f.g. projective $Lambda$-module.

  We would like to define a map
  $ alpha:M' times.o_Lambda M -> Lambda $
  by setting $alpha(f times.o m)=f(m)$ for $f in M'$, $m in M$. However, for
  $lambda in Lambda$ we have
  $
    alpha(f lambda times.o m)=(f lambda)(m)=f(m)lambda,
    quad alpha(f times.o lambda m)=f(lambda m)=lambda f(m),
  $
  so $alpha$ is not in general well defined on $M' times.o_Lambda M$ with values
  in $Lambda$. But the above computation shows that there is a well defined map
  $
    alpha:M' times.o_Lambda M -> Lambda^ast,
    quad "given by" alpha(f times.o m)={f(m)}^ast,
  $
  where $ast$ denotes images in $Lambda^ast$, and
  $Lambda^ast=Lambda slash [Lambda,Lambda]$ as in @eq:order-commutator-quotient.
  There is thus a _trace map_ #idx("trace map") #numbered-block[
    $ T:E(M) arrow.r^(mu^(-1)) M' times.o_Lambda M arrow.r^alpha Lambda^ast. $
  ] <eq:projective-lattice-trace-map>

  #source(696)
  It is easily verified that for each f.g. projective $Lambda$-module $M$, the
  trace map $T$ (defined above) is additive and symmetric, and is indeed an
  $R$-homomorphism in our case. Furthermore, $T$ behaves properly under change
  of rings, in the following sense: let $phi:Lambda -> Gamma$ be a ring
  homomorphism. Then $Gamma times.o_Lambda M$ is a f.g. projective
  $Gamma$-module, and there is a map $E(M) -> E(Gamma times.o M)$, given by
  $theta in E(M) mapsto 1 times.o theta in E(Gamma times.o M)$. On the other
  hand, $phi$ induces an additive map $phi^ast:Lambda^ast -> Gamma^ast$. Then
  the following diagram commutes
  #numbered-block[#trace-base-change-diagram()]
  <eq:projective-trace-base-change>
  where $T'$ is the trace map on $E(Gamma times.o M)$.

  As shown in Exercise~@exc:projective-module-trace, the trace map $T$ agrees
  with the usual definition when $M$ is $Lambda$-free and $Lambda$ is
  commutative. Further, for each idempotent $e in Lambda$, we may form the
  projective $Lambda$-module $M=Lambda e$. Each $theta in E(M)$ is then given by
  right multiplication by an element $theta(e) in e Lambda e$, and (see
  Exercise~@exc:projective-module-trace) we have
  #numbered-block[$ T(theta)=theta(e)^ast in Lambda^ast. $]
  <eq:projective-idempotent-trace>
  We now define the _rank element_ #idx("rank element") of the projective left
  $Lambda$-module $M$ as
  $ r_Lambda lr((M))=T(1_M) in Lambda^ast, $
  where $1_M$ is the identity map on $M$. The reader will easily verify that
  #numbered-block[
    $
      r_Lambda lr((M_1 plus.o M_2))=r_Lambda lr((M_1))+r_Lambda lr((M_2)), \
      r_Lambda lr((Lambda e))=e^ast, \
      r_Gamma lr((Gamma times.o_Lambda M))=1 times.o r_Lambda lr((M)) in
      Gamma^ast,
    $
  ] <eq:projective-rank-element-properties>
  where $phi:Lambda -> Gamma$ is any ring homomorphism.

  Step 3. Returning to our original problem, we assume now that $M$ and $N$ are
  projective $Lambda$-lattices such that $K M tilde.equiv K N$, and that
  $Lambda$ satisfies the conditions:
  #enum(
    numbering: "(a)",
    [$Lambda^ast$ is $R$-torsionfree, and],
    [$Lambda slash rad Lambda$ is a split semisimple $overline(R)$-algebra.],
  )
  Clearly $K M$ and $K N$ are f.g. projective left $A$-modules, so their rank
  elements $r_A lr((K M))$ and $r_A lr((K N))$ are defined as in Step 2. Since
  $K M tilde.equiv K N$ we have $r_A lr((K M))=r_A lr((K N))$. Therefore
  $r_Lambda lr((M))$ and $r_Lambda lr((N))$ have the same image in $A^ast$,
  #source(697)
  under the map $Lambda^ast -> K times.o_R Lambda^ast=A^ast$. Condition (a) then
  implies that $r_Lambda lr((M))=r_Lambda lr((N))$ in $Lambda^ast$.

  Now let $Lambda=plus.o.big Lambda e_i$ be a decomposition of $Lambda$ into
  indecomposable left ideals, numbered so that $Lambda e_1,...,Lambda e_r$ are a
  full set of non-isomorphic summands. Let
  $tilde(Lambda)=Lambda slash rad Lambda=plus.o.big tilde(Lambda) tilde(e)_i$;
  this gives a decomposition of the split semisimple $overline(R)$-algebra
  $tilde(Lambda)$ into simple left $tilde(Lambda)$-modules, and
  $tilde(Lambda) tilde(e)_1,...,tilde(Lambda) tilde(e)_r$ are a basic set of
  simple modules (see @th:complete-ring-idempotent-decompositions). Since $R$ is
  now assumed to be a complete d.v.r., the K-S-A Theorem holds for
  $Lambda$-lattices. But $M divides Lambda^((k))$ for some $k$, and therefore,
  for some integers ${m_i}$ and ${n_i}$,
  $
    M tilde.equiv product_(i=1)^r (Lambda e_i)^((m_i)),
    quad N tilde.equiv product_(i=1)^r (Lambda e_i)^((n_i)).
  $
  If $M$ and $N$ have a common summand, say $Lambda e_1$, then we may delete it
  and obtain a new pair of projective $Lambda$-lattices $M'$ and $N'$ such that
  $K M' tilde.equiv K N'$. If we can prove that $M' tilde.equiv N'$, then it
  will follow that $M tilde.equiv N$. Hence for the rest of the proof, we may
  assume that for each $i$, either $m_i=0$ or $n_i=0$.

  Furthermore, if $d=op("G.C.D."){m_1-n_1,...,m_r-n_r}$, then $d divides m_i$
  and $d divides n_i$ for each $i$, so we may write $M=M_0^((d))$,
  $N=N_0^((d))$, with $M_0$ and $N_0$ projective and $K M_0 tilde.equiv K N_0$.
  It would thus suffice to show that $M_0 tilde.equiv N_0$. Changing notation,
  we may hereafter assume that $d=1$; consequently, some
  $overline(m)_i-overline(n)_i != 0$ in $overline(R)$. To fix the notation,
  suppose that $overline(m)_1-overline(n)_1 != 0$ in $overline(R)$.

  We now have
  $
    r_Lambda lr((M))=sum_(i=1)^r m_i e_i^ast,
    quad r_Lambda lr((N))=sum_(i=1)^r n_i e_i^ast.
  $
  Since $r_Lambda lr((M))=r_Lambda lr((N))$, this gives $sum(m_i-n_i)e_i^ast=0$
  in $Lambda^ast$. The ring homomorphism $Lambda -> tilde(Lambda)$ induces a map
  $Lambda^ast -> tilde(Lambda)^ast$, whence
  $sum(overline(m)_i-overline(n)_i)tilde(e)_i^ast=0$ in $tilde(Lambda)^ast$.
  Therefore we obtain #numbered-block[
    $
      sum_(i=1)^r (overline(m)_i-overline(n)_i)tilde(e)_i in
      [tilde(Lambda),tilde(Lambda)].
    $
  ] <eq:hattori-commutator-rank-relation>
  But $tilde(Lambda) tilde.equiv product_(i=1)^r M_(k_i) lr((overline(R)))$ by
  condition (b), so $[tilde(Lambda),tilde(Lambda)]$ correspondingly decomposes
  into a direct sum of $r$ subspaces. From @eq:hattori-commutator-rank-relation
  we deduce that
  $
    (overline(m)_1-overline(n)_1)tilde(e)_1 in
    [M_(k_1) lr((overline(R))),M_(k_1) lr((overline(R)))],
  $
  whence $(overline(m)_1-overline(n)_1)tilde(e)_1$ has zero trace. This is
  impossible since $overline(m)_1-overline(n)_1 != 0$ in $overline(R)$, and
  since the primitive idempotent $tilde(e)_1 in M_(k_1) lr((overline(R)))$ looks
  like $op("diag")(1,0,...,0)$ relative to a suitable $overline(R)$-basis of
  $overline(R)^(k_1)$. This is a contradiction, and shows that the above defined
  $M'$ and $N'$ are $0$. This completes the proof of Hattori's Theorem
  @th:hattori-projective-lattice-cancellation, and also of its special case
  @th:local-projective-group-lattice-cancellation where $Lambda=R G$.
]

#source(698)
#remark(numbered: false)[
  Another proof of @th:local-projective-group-lattice-cancellation, in case $K$
  is sufficiently large, is given in
  @cor:projective-lattices-determined-by-character. For the general case, a
  proof of @th:local-projective-group-lattice-cancellation is given in
  @th:projective-character-map-split-injection (see also
  @bib:CurtisReiner1962[CR] (77.14)).
]

=== Global Case <ss:projective-lattices-global-case>

We are now ready to state and prove the fundamental result of Swan
@bib:Swan1960:

#theorem[
  Let $R$ be a Dedekind domain whose quotient field $K$ has characteristic $0$.
  Let $G$ be a finite group of order $n$, and assume that no prime divisor of
  $n$ is a unit in $R$. Set $Lambda=R G$, $A=K G$. Then every f.g. projective
  left $Lambda$-module $M$ is locally free, that is, $M_P$ is $Lambda_P$-free
  for each maximal ideal $P$ of $R$, where the subscript denotes either
  localization at $P$ or $P$-adic completion. Further, $K M$ is $A$-free, and
  $M slash P M$ is $(Lambda slash P Lambda)$-free for each $P$.
  #idx(
    "Swan's Theorem",
    target: [@th:swan-projective-group-lattices-locally-free],
  )
] <th:swan-projective-group-lattices-locally-free>

#proof[
  Step 1. Let $M$ be any projective $Lambda$-lattice; then for each $P$, the
  localization $M_P$ is a projective $Lambda_P$-lattice. Once we prove that
  $K M tilde.equiv A^((t))$ for some $t$, then we have
  $ K M_P tilde.equiv K Lambda_P^((t)), $
  which implies by @th:local-projective-group-lattice-cancellation that
  $M_P tilde.equiv Lambda_P^((t))$. Further,
  $
    M slash P M tilde.equiv M_P slash P M_P
    tilde.equiv (Lambda_P slash P Lambda_P)^((t))
    tilde.equiv (Lambda slash P Lambda)^((t)),
  $
  so the theorem will be established (including the fact that we can equally
  well use $P$-adic completions instead of localizations at $P$). Thus, it
  suffices for us to prove that $K M$ is $A$-free.

  Step 2. Let the $A$-module $K M$ afford the character $mu$ of $G$. If we can
  show that $mu(x)=0$ for all $x in G-{1}$, then the inner product $(mu,1_G)_G$
  of $mu$ with the trivial character $1_G$ of $G$ will be equal to
  $mu(1) slash n$, where $n=abs(G)$. Since this inner product lies in $ZZ$, we
  then obtain $mu(1)=n t$ for some $t in ZZ$. But then $mu=t rho$, where $rho$
  is the character of $G$ afforded by the regular left module
  $attach(A, bl: A)$. Since $op("char")K=0$, the equality $mu=t rho$ implies the
  desired isomorphism $K M tilde.equiv A^((t))$.

  Let $x in G-{1}$, and let $H=chevron.l x chevron.r$. Then $M_H$ is
  $R H$-projective (since $attach(Lambda, bl: R H)$ is $R H$-free!), and we can
  calculate $mu(x)$ by letting $x$ act on the $K H$-module $K M_H$. Thus, if the
  theorem is established for the case of cyclic groups, then we will have
  $mu(x)=0$ as desired, and therefore the theorem also holds for arbitrary
  groups.

  Changing notation, suppose for the rest of the proof that
  $G=chevron.l x:x^n=1 chevron.r$ is cyclic of order $n$, where $n>1$. We may
  write $x$ as a product of commuting elements, each of prime power order. Hence
  for some rational prime $p$ dividing $n$, we may write $x=y z$, where
  $y z=z y$, and where $y$ has order $p^k$, $k>0$, while $z$ has order prime to
  $p$. Therefore $G=H times E$, where $H=chevron.l y chevron.r$ is a nontrivial
  $p$-group, and where $E=chevron.l z chevron.r$ has order prime to $p$.

  #source(699)
  Now let $K'=K(root(n, 1))$; then by @cor:exponent-cyclotomic-splitting-field
  $K'$ is a splitting field for $G$. Let $R'$ be the integral closure of $R$ in
  $K'$. Since $p$ is not a unit in $R$ by hypothesis, there exists a maximal
  ideal $P'$ of $R'$ containing $p$. Let $S=(R')_(P')$ be the localization of
  $R'$ at $P'$; then $S$ is a d.v.r. whose residue class field $overline(S)$ has
  characteristic $p$.

  The projective $R G$-lattice $M$ gives rise to a projective $S G$-lattice
  $S times.o_R M$, and we may compute $mu(x)$ by letting $x$ act on an $S$-basis
  of $S times.o M$, where $times.o$ means $times.o_R$. Let ${e_i}$ be a full set
  of primitive orthogonal idempotents of the group algebra $K' E$. Since
  $abs(E)$ is a unit in $S$, and $E$ is commutative, it follows from
  @prop:group-character-orthogonality-idempotents that each $e_i in S E$, where
  $S E$ is the integral group ring of $E$ over $S$. Therefore
  $ S times.o M=plus.o.big_i e_i lr((S times.o M)), $
  and each summand $e_i lr((S times.o M))$ is also a projective $S G$-module.
  (We are using strongly the fact that $G$ is abelian, so each
  $e_i lr((S times.o M))$ is indeed an $S G$-module.)

  Now $E=chevron.l z chevron.r$, and for each $i$ we have $z e_i=omega_i e_i$
  for some root of unity $omega_i$ in $S$. On the other hand, we may view each
  $e_i lr((S times.o M))$ as a left $S H$-module, and let it afford the
  character $rho_i$ of $H$ (over the field $K'$). Since $x=y z$, we obtain
  $ mu(x)=sum_i rho_i lr((y)) omega_i, $
  using the fact that $z$ acts on $e_i lr((S times.o M))$ as multiplication by
  $omega_i$. To complete the proof, we need only show that each
  $rho_i lr((y))=0$. But for each $i$, $e_i lr((S times.o M))$ is a projective
  $S H$-module, and $H$ is a $p$-group. Hence by @cor:p-group-ring-local-base
  $S H$ is a local ring, so every projective $S H$-module is $S H$-free. But
  then $rho_i lr((y))=0$ since $y!=1$. This completes the proof that $mu(x)=0$
  for $x in G-{1}$, and establishes the theorem. (The authors wish to thank
  Janusz for pointing out this simplified version of Step 2.)
]

The following corollary is an immediate consequence of Swan's Theorem and the
results in §@sec:genus on genus:

#corollary[
  Keeping the notation and hypotheses of
  @th:swan-projective-group-lattices-locally-free, let $M$ be any projective
  left $Lambda$-lattice. Then $M$ lies in the genus of a free $Lambda$-module
  $Lambda^((r))$ for some integer $r$. Further, if $M != 0$,
  $ M tilde.equiv Lambda^((r-1)) plus.o M_0 $
  for some left ideal $M_0$ in the genus of $Lambda$.
] <cor:swan-projective-lattice-left-ideal-decomposition>

#proof[
  Using @cor:genus-multiple-decomposition, we obtain a decomposition of $M$ as
  above, with $M_0$ in the genus of $Lambda$. Then $K M_0 tilde.equiv K Lambda$,
  so we may identify $M_0$ with a left ideal of $Lambda$.
]

#source(700)
Swan's Theorem also implies that the ring $R G$ cannot be decomposed into a
direct sum of left ideals, since each summand would be $R G$-projective, and
hence its $R$-rank would be a multiple of $n$. Thus $R G$ contains no idempotent
elements except $1$. In this connection we prove a result due to Coleman
@bib:Coleman1966:

#theorem[
  Let $R$ be any integral domain of characteristic $0$, and let $n=abs(G)$. Then
  $R G$ contains an idempotent $e!=1$ if and only if some rational prime divisor
  of $n$ is a unit in $R$.
  #idx("Coleman's Theorem", target: [@th:coleman-group-ring-idempotents])
] <th:coleman-group-ring-idempotents>

#proof[
  If $p divides n$ and $p^(-1) in R$, let $x in G$ have order $p$. Then
  $ p^(-1)(1+x+...+x^(p-1)) $
  is an idempotent in $R G$ distinct from $1$. Conversely, let
  $e=sum_(y in G) alpha_y y in R G$ be idempotent, with each $alpha_y in R$ and
  where $e!=1$. The left regular module $attach((R G), bl: R G)$ affords a
  matrix representation $M$ of $R G$. Since $e^2=e$, the eigenvalues of the
  matrix $M(e)$ are $0$'s and $1$'s; thus $M(e)$ has trace $q$, where $q in ZZ$,
  $0<=q<=n$. If $q=n$, then all eigenvalues of $M(e)$ are $1$, so $M(e)$ is
  nonsingular. But ${M(e)}^2=M(e^2)=M(e)$, so $M(e)$ is the identity matrix.
  Since $R G$ acts faithfully on the left regular module, this gives $e=1$, a
  contradiction. Thus $q<n$, and a similar argument with $1-e$ in place of $e$
  shows that $q>0$.

  On the other hand,
  $ "Trace of" M(e)=sum alpha_y dot "Trace of" M(y)=n alpha_1. $
  Thus $q=n alpha_1$ for some $alpha_1 in R$, so $q slash n in R$, and we have
  $0<q<n$. Hence some rational prime divisor of $n$ must be a unit in $R$, as
  claimed. The theorem also holds when $op("char")R!=0$, using a slight
  modification of the above argument.
]

The preceding results on indecomposability are generalized nicely in the
following result of Berman @bib:Berman1963, Theorem~5, @bib:Berman1965, and
Dress @bib:Dress1970:

#theorem[
  Keeping the hypotheses of @th:swan-projective-group-lattices-locally-free, let
  $H subset.eq G$ and let $R_H$ denote the $R H$-module $R$ on which $H$ acts
  trivially. Then the induced $R G$-module $(R_H)^G$ is indecomposable. #idx(
    "Berman's Theorem",
    target: [@th:transitive-permutation-lattice-indecomposable],
  ) #idx(
    "Dress' Theorem",
    target: [@th:transitive-permutation-lattice-indecomposable],
  )
] <th:transitive-permutation-lattice-indecomposable>

#proof[
  When $H=1$, we have $(R_H)^G=R G$, and the result follows from Swan's Theorem.
  For general $H$, let $N divides (R_H)^G$; we shall show that
  $abs(G thin : thin H)$ divides $op("rank")_R N$, which implies the desired
  result. It suffices to show that for each prime $p$ dividing $abs(G)$, the
  $p$-part of $abs(G thin : thin H)$ divides $op("rank")_R N$. Let $P$ be a
  maximal ideal of $R$ containing $p$, so $overline(R)=R slash P$ has
  characteristic $p$, and let bars denote reduction mod $P$. Let $V$ and $W$ be
  Sylow $p$-subgroups of $G$ and $H$, respectively, with $W subset.eq V$.

  #source(701)
  Since $N divides (R_H)^G$, we have $overline(N) divides (overline(R)_H)^G$.
  But $overline(R)_H divides (overline(R)_W)^H$, so
  $overline(N) divides (overline(R)_W)^G$. Therefore $overline(N)_V$ is a direct
  summand of $(overline(R)_W)^G bar_V$. By Mackey's Subgroup Theorem, the latter
  module is a direct sum of modules of the form $(overline(R)_T)^V$, where $T$
  ranges over certain subgroups of $V$ of the form $attach(W, tl: x) inter V$.
  Since $overline(R)_T$ is absolutely indecomposable and $V$ is a $p$-group,
  Green's Theorem @cor:p-group-indecomposable-induction shows that
  $(overline(R)_T)^V$ is indecomposable. But $overline(N)_V$ is then a direct
  sum of such induced modules, and since
  $
    dim_(overline(R)) (overline(R)_T)^V
    =abs(V thin : thin T)=abs(V thin : thin attach(W, tl: x) inter V),
  $
  it follows that $dim_(overline(R)) overline(N)_V$ is a multiple of
  $abs(V thin : thin W)$. But this dimension equals the $R$-rank of $N$, while
  $abs(V thin : thin W)$ is the $p$-part of $abs(G thin : thin H)$, so the proof
  is completed.
]

The same argument establishes Berman's result: #idx("Berman's Theorem")

_Let $H subset.eq G$, and let $chi$ be a linear character from $H$ into the
complex field. Let $R=ZZ[chi]$ be the ring obtained by adjoining to $ZZ$ all of
the character values ${chi(h):h in H}$, and view $R$ as $R H$-module with
$h in H$ acting as $chi(h)$. Then the induced $R G$-module $R G times.o_(R H) R$
is indecomposable. Indeed, the generalized permutation representation of $G$,
afforded by this induced module, is indecomposable over every ring of algebraic
integers._

#heading(level: 3)[
  Characters Afforded by Projective Lattices
] <ss:projective-lattice-characters>

Throughout this subsection, let $R$ be a Dedekind domain whose quotient field
$K$ has characteristic $0$, and let $G$ be a finite group of order $n$. We shall
call an element $x in G$ _$R$-singular_ #idx("R-singular element") if the order
of $x$ is not a unit in $R$. Our aim is to investigate the relationship between
$R G$-lattices $M$ and the values of their characters on $R$-singular elements
of $G$. The results below are due to Swan @bib:Swan1963.

We begin with an easy generalization of
@th:swan-projective-group-lattices-locally-free, as follows:

#theorem[
  Let $mu$ be the character of $G$ afforded by a projective $R G$-lattice $M$.
  Then $mu(x)=0$ for every $R$-singular element $x in G$.
] <th:projective-character-singular-vanishing>

#proof[
  Let $x in G$ be $R$-singular. Then some rational prime $p$ dividing the order
  of $x$ is a non-unit in $R$, and $p$ is contained in some maximal ideal $P$ of
  $R$. Then $M_P$ is $R_P G$-projective, and also affords $mu$. Further, $x$ is
  $R_P$-singular. Hence it suffices to prove the result when $R$ is replaced by
  its localization $R_P$. Changing notation, assume hereafter that $M$ is
  $R G$-projective and $x$ is $R$-singular, where $R$ is a d.v.r.

  Now choose $H=chevron.l x chevron.r$. Then the argument in Step 2 of the proof
  of @th:swan-projective-group-lattices-locally-free carries over unchanged to
  the present situation, and shows that $mu(x)=0$. This completes the proof.
]

#source(702)
In @th:projective-characters-supported-p-regular we proved a special case of the
above theorem by a different method. We showed there that if $(K,R,k)$ is a
$p$-modular system, with $K$ a sufficiently large field of characteristic $0$,
then the $K$-characters afforded by projective $R G$-modules vanish on
$p$-irregular elements.

We may rephrase Theorem @th:projective-character-singular-vanishing in terms of
Grothendieck groups and projective class groups, using the terminology of
§@ss:modular-notation-terminology. Let $K_0(R G)$ be the projective class group
generated by projective $R G$-lattices, with relations arising from direct sums.
As usual,#footnote[
  Since the ring $K G$ is semisimple, the projective class group $K_0(K G)$
  coincides with the Grothendieck group $G_0(K G)$. (See
  §@ss:grothendieck-groups and
  Exercise~@exc:semisimple-grothendieck-projective-equality.)
] we identify $K_0(K G)$ with the ring $op("ch")K G$ of virtual characters of
$K G$-modules. Then there is a homomorphism of additive groups
$ tau:K_0(R G) -> K_0(K G)=op("ch")K G, $
which takes each projective $R G$-lattice $M$ onto the character of $G$ afforded
by $M$ (or, more precisely, by $K M$). Since each element of $K_0(R G)$ is of
the form $[M]-[N]$, with $M$ and $N$ projective $R G$-lattices, Theorem
@th:projective-character-singular-vanishing is equivalent to the assertion that
for each virtual character $chi in im tau$, $chi$ vanishes at each $R$-singular
$x in G$.

Our next step is to show that this property characterizes the image of $tau$.
Let $e:K_0(k G) -> G_0(K G)$ be the map defined in @eq:projective-character-map,
and remember that $G_0(K G)=K_0(K G)$. In
@prop:cartan-triangle-injectivity-cokernel(iii) we proved that if $(K,R,k)$ is a
$p$-modular system, with $K$ a sufficiently large field of characteristic $0$,
then the image of $e$ corresponds to the set of all virtual characters in
$op("ch")K G$ which vanish on the $p$-irregular elements of $G$. The main result
of this subsection is a far-reaching generalization of that fact, and is as
follows:

#theorem[
  The image of $tau$ consists precisely of all $chi in K_0(K G)$ such that
  $chi(x)=0$ for every $R$-singular $x in G$.
  #idx("Swan's Theorem", target: [@th:projective-lattice-character-image])
] <th:projective-lattice-character-image>

#proof[
  Step 1. Suppose first that $R$ is a d.v.r., $K$ is a splitting field for $G$
  and all of its subgroups, and $G$ is of the form $G=H times E$, where $H$ is a
  $p$-group and $E$ is a $p'$-group, with $p$ a non-unit in $R$. Then every
  irreducible $K$-character $theta$ of $G$ can be expressed as $theta=phi psi$
  with $phi in op("Irr")(H)$, $psi in op("Irr")(E)$, that is,
  $ theta(x, y)=phi(x)psi(y) "for" x in H,y in E. $
  (See Exercise~@exc:direct-product-characters.) If the $K H$-module $V$ affords
  $phi$, and the $K E$-module $W$ affords $psi$, then the outer tensor product
  $V hash W$ affords $theta$.

  Now let $chi in op("ch")K G$ vanish on all $R$-singular elements of $G$. This
  means in our case that $chi(x y)=0$ for all $x in H-{1}$ and all $y in E$. Let
  us express $chi$ in the form
  $
    chi=sum phi_i psi_i, quad phi_i in op("ch")K H, quad psi_i in op("Irr")K E,
  $
  #source(703)
  which is possible by virtue of the earlier remarks. Then for $x in H-{1}$,
  $ sum phi_i lr((x))psi_i=0 "in" op("ch")K E. $
  But the ${psi_i}$ are linearly independent over $K$, by
  @th:frobenius-schur-matrix-coordinates. This shows that for each $i$, $phi_i$
  vanishes on $H-{1}$, so by Step 2 of the proof of
  @th:swan-projective-group-lattices-locally-free we see that $phi_i=b_i rho$
  for some $b_i in ZZ$, where $rho$ is the regular character of $H$. But then
  $chi=rho psi$ for some $psi in op("ch")K E$. We may write $psi=nu_1-nu_2$,
  where $nu_i$ is the character of $E$ afforded by the $R E$-lattice $N_i$,
  $i=1,2$. But $N_i$ is $R E$-projective by @cor:projective-prime-divisors,
  since $abs(E)$ is a unit in $R$. Then $tau$ maps the element
  $ [R H hash N_1]-[R H hash N_2] in K_0(R G) $
  onto $chi$, which completes the proof of the theorem for this special case.

  Step 2. Let $R$ and $K$ be as above, but let $G$ be arbitrary. By Brauer's
  Induction Theorem @th:brauer-induction, there exist elementary subgroups
  ${H_i}$ of $G$, and elements $xi_i in op("ch")K H_i$, such that
  $ 1=sum xi_i^G "in" op("ch")K G. $
  Suppose $chi in op("ch")K G$ vanishes on all $R$-singular elements of $G$;
  then its restriction $chi bar_(H_i)$ vanishes on all $R$-singular elements of
  $H_i$. However,
  $ chi=sum chi dot xi_i^G=sum(chi bar_(H_i) dot xi_i)^G, $
  by @lem:class-function-induction-product. Since $chi bar_(H_i) dot xi_i$
  vanishes on all $R$-singular elements of $H_i$, and since each elementary
  group is of the form described in Step 1, it follows that for each $i$,
  $
    chi bar_(H_i) dot xi_i in im tau_i,
    quad "where" tau_i:K_0(R H_i) -> op("ch")K H_i.
  $
  But then $chi in im tau$, since the following diagram is commutative:
  #projective-induction-diagram()
  This completes the proof of the theorem in the special case where $K$ is a
  splitting field for $G$ and its subgroups, and $R$ is a d.v.r. Another proof
  for this special case is given in
  @prop:cartan-triangle-injectivity-cokernel(ii).

  #source(704)
  Step 3. We assume next that $R$ is a d.v.r., but drop the hypothesis that $K$
  be a splitting field. Let $hat(R)$, $hat(K)$, etc., be completions. The ring
  inclusions $R -> hat(R)$, $K -> hat(K)$, give rise to a commutative diagram
  #projective-completion-diagram()
  Suppose that the elements $a in K_0(K G)$ and $b in K_0(hat(R) G)$ have the
  same image in $K_0(hat(K) G)$. Using
  Exercise~@exc:projective-class-free-difference twice, we may write
  $ a=[V]-[(K G)^((r))], quad b=[X]-[(hat(R) G)^((r))], $
  for some $K G$-module $V$ and some projective $hat(R) G$-lattice $X$, with the
  same choice of $r$ for both $a$ and $b$. Then
  $ [hat(K) V]=[hat(K) X] "in" K_0(hat(K) G), $
  so $hat(K) V tilde.equiv hat(K) X$. By
  @cor:dvr-completion-order-lattice-correspondence, there exists an
  $R G$-lattice $M$ for which $X tilde.equiv hat(M)$. By virtue of
  @th:dvr-projectivity-reduction, $M$ is $R G$-projective, and so both $a$ and
  $b$ are images of the element $[M]-[(R G)^((r))] in K_0(R G)$.

  Now let $chi in op("ch")K G$ vanish on all $R$-singular elements of $G$. Then
  its image $hat(chi) in op("ch")hat(K) G$ has the same property, so if the
  theorem is known to be true for the case of complete d.v.r.'s, it follows that
  $hat(chi) in im hat(tau)$. But then $chi in im tau$ by the preceding remarks.

  For the rest of this Step, we may assume that $R$ is a complete d.v.r. As in
  Step 2 of the proof of @th:swan-projective-group-lattices-locally-free, we can
  choose a splitting field $K'$ containing $K$, with a d.v.r. $S$ whose residue
  class field $overline(S)$ contains the residue class field $overline(R)$ of
  $R$. There is a commutative diagram
  #projective-extension-diagram()
  and by Step 2 we have $beta(chi)=tau'(xi')$ for some $xi' in K_0(S G)$.

  Next, by @prop:grothendieck-character-ring we have
  $op("ch")K G tilde.equiv G_0(K G)$, and therefore the map $beta$ is monic by
  Exercise~@exc:separable-grothendieck-injection. We show next that the map
  $alpha$ is a split monomorphism, and so the image of $alpha$ is a $ZZ$-pure
  submodule of $K_0(S G)$. To prove that
  #source(705)
  $alpha$ is a split monomorphism, let us consider the diagram
  #projective-reduction-diagram()
  Each horizontal map is an isomorphism, by
  @prop:local-theory-radical-completion. Further, $overline(alpha)$ is a split
  monomorphism by @prop:grothendieck-scalar-extension-injections. Hence $alpha$
  is also split, as claimed. Therefore $im alpha$ is $ZZ$-pure in $K_0(S G)$, by
  §@ss:modules-dedekind-domains.

  Now let $rho:K_0(S G) -> K_0(R G)$, $sigma:op("ch")K' G -> op("ch")K G$, be
  the restriction maps. It is easily verified that $tau rho=sigma tau'$, since
  these maps agree on $S G$, and hence on any summand of a free $S G$-module.
  Put $xi=rho(xi') in K_0(R G)$. Then
  $
    tau' alpha(xi)=beta tau(rho xi')=beta sigma tau'(xi')
    =beta sigma beta(chi)=m beta(chi)=tau'(m xi'),
  $
  where $m=dim_K K'$. But then $alpha(xi)=m xi'$, since $tau'$ is monic by
  Hattori's Theorem @th:hattori-projective-lattice-cancellation. Therefore
  $m xi' in im alpha$, and so also $xi' in im alpha$, because $im alpha$ is
  $ZZ$-pure in $K_0(S G)$. Writing $xi'=alpha(eta)$, we obtain
  $ beta tau(eta)=tau' alpha(eta)=tau'(xi')=beta(chi), $
  so $chi=tau(eta)$. This completes the proof of the theorem for the case where
  $R$ is any d.v.r.

  Step 4. It remains for us to show how to pass from the local case to the
  general case. Let $chi in op("ch")K G$ vanish on all $R$-singular elements of
  $G$, where now $R$ is an arbitrary Dedekind domain. Let ${P_1,...,P_t}$ be the
  set of maximal ideals of $R$ which contain $abs(G)$. The previous step shows
  that for each $i$, $1<=i<=t$, there exists a projective $(R_(P_i) G)$-lattice
  $M_i$ such that
  $ tau_i lr({[M_i]-[(R_(P_i) G)^((q))]})=chi, $
  with $q$ independent of $i$. Here, $tau_i$ maps $K_0(R_(P_i) G)$ into
  $K_0(K G)$. The $K G$-modules ${K M_i:1<=i<=t}$ all have the same character,
  so they are mutually isomorphic. By @prop:localization-completion-lattices, we
  can find an $R G$-lattice $M$ such that
  $ M_(P_i) tilde.equiv M_i, quad 1<=i<=t. $
  Then $M$ is $R G$-projective by @cor:projective-prime-divisors, and $tau$ maps
  $[M]-[(R G)^((q))]$ onto $chi$. This proves the theorem.
]

We shall next sharpen Theorem @th:projective-lattice-character-image so that it
deals with ordinary characters rather than virtual characters. Let
$op("ch")^+ K G$ be the semigroup
#source(706)
consisting of all characters of $G$ afforded by $K G$-modules, and let
$K_0^+(R G)$ be the semigroup consisting of all classes $[M]$, where $M$ ranges
over all projective $R G$-lattices. We might expect that each
$chi in op("ch")^+ K G$, which vanishes at all $R$-singular elements of $G$, is
of the form $chi=tau[M]$ for some $M$. However, this need not be the case even
when $R$ is a complete d.v.r. (see
Exercise~@exc:projective-character-positive-cone).

When the group $G$ is suitably restricted, however, the hoped-for result is
true. The following theorem is due to Swan @bib:Swan1963:

#theorem[
  Suppose that the group $G$ is $p$-solvable for each prime factor $p$ of $n$
  which is a non-unit in $R$. Then for each $K G$-module $V$ whose character
  $chi$ vanishes on all $R$-singular elements of $G$, there exists a projective
  $R G$-lattice $M$ such that $V tilde.equiv K M$. #idx(
    "Swan's Theorem",
    target: [@th:p-solvable-positive-projective-character-image],
  ) #idx(
    "group",
    "p-solvable",
    target: [@th:p-solvable-positive-projective-character-image],
  )
  #idx(
    "p-solvable group",
    target: [@th:p-solvable-positive-projective-character-image],
  )
] <th:p-solvable-positive-projective-character-image>

#proof[
  Let us first treat the case where $R$ is a complete d.v.r. in which $p$ is a
  non-unit, and $K$ is a splitting field for $G$ and its subgroups. Using the
  notation of @eq:brauer-character-table-data, let ${eta^1,...,eta^r}$ be the
  principal indecomposable Brauer characters of $G$. Then
  $ chi=sum_(i=1)^r m_i eta^i $
  for some integers $m_i in ZZ$, by @th:projective-lattice-character-image. On
  the other hand, since $G$ is $p$-solvable, each simple Brauer character
  corresponds to a row of the decomposition matrix which is a complete standard
  basis row (see @cor:p-solvable-decomposition-numbers). Thus for each $i$,
  $1<=i<=r$, some irreducible $K$-character $zeta^j$ occurs with multiplicity
  $1$ in $eta^i$, and does not occur in any $eta^l$ for $l!=i$. But then
  $m_i>=0$, since otherwise $zeta^j$ would occur with negative multiplicity in
  the character $chi$. It follows that
  $ V tilde.equiv K M, quad "where" M=product_(i=1)^r U_i^((m_i)), $
  which completes the proof in this case.

  Still assuming $R$ complete, we drop the hypothesis that $K$ be a splitting
  field. Choose a finite extension field $K'$ of $K$ with d.v.r. $R'$ such that
  $K'$ is a splitting field. The previous discussion shows that
  $ K' V tilde.equiv K' M' "for some projective" R' G"-lattice" M'. $
  Let $M=M' bar_(R G)$, so $M in cal(P)(R G)$, and $K M=K M'=K R' M'=K' M'$,
  with the last equality true because $K R'=K'$. This gives
  $ V^((m)) tilde.equiv K M "as" K G"-modules, where" m=dim_K K'. $
  On the other hand, @th:projective-lattice-character-image gives
  $ [V]=[K N_1]-[K N_2] "in" op("ch")K G, $
  #source(707)
  with $N_1,N_2 in cal(P)(R G)$. Therefore
  $ K M plus.o K N_2^((m)) tilde.equiv K N_1^((m)), $
  so by Hattori's Theorem, $M plus.o N_2^((m)) tilde.equiv N_1^((m))$. The K-S-A
  Theorem then yields $M tilde.equiv L^((m))$ for some $L in cal(P)(R G)$, and
  therefore $V tilde.equiv K L$. This completes the proof for $R$ any complete
  d.v.r.

  If $R$ is any d.v.r., not necessarily complete, let $hat(R)$ be its
  completion. Then $hat(V) tilde.equiv hat(K) X$ for some
  $X in cal(P)(hat(R) G)$, so by
  @cor:dvr-completion-order-lattice-correspondence, $V tilde.equiv K M$ where
  $M$ is an $R G$-lattice for which $hat(M) tilde.equiv X$. Thus
  $M in cal(P)(R G)$, and again we are through.

  Finally, the case of arbitrary Dedekind domains is treated just as in Step 4
  of the proof of @th:projective-lattice-character-image, and so we have
  established Theorem @th:p-solvable-positive-projective-character-image.
]

#exercises-heading

#exercise[
  Let $cal(P)(Lambda)$ be the category of f.g. projective left $Lambda$-modules
  over an arbitrary ring $Lambda$, and let $Lambda^ast$ be defined as in
  @eq:order-commutator-quotient. For each $M in cal(P)(Lambda)$, let
  $
    E(M)=End_Lambda lr((M)), quad M'=Hom_Lambda lr((M,Lambda))="right"
    Lambda"-module",
  $
  where $E(M)$ acts from the right on $M$. Let
  $ mu:M' times.o_Lambda M -> E(M) $
  be the two-sided $E(M)$-isomorphism defined as in §@ss:morita-theorems, or in
  Step 2 of the proof of @th:hattori-projective-lattice-cancellation. Let
  $ T:E(M) arrow.r^(mu^(-1)) M' times.o_Lambda M arrow.r^alpha Lambda^ast $
  be the trace map defined by composition, where $alpha(f times.o m)=f(m)^ast$.
  #enum(
    numbering: "(i)",
    [Suppose that $M=plus.o.big_(i=1)^k Lambda m_i$ is $Lambda$-free. For
      $theta in E(M)$, let
      $ m_i theta=sum_(j=1)^k a_(i j) m_j, quad a_(i j) in Lambda. $
      Show that $T(theta)=(sum a_(j j))^ast in Lambda^ast$. Thus $T$ is the
      usual trace map when $Lambda$ is commutative.],
    [Let $e in Lambda$ be idempotent, and let $M=Lambda e in cal(P)(Lambda)$.
      Show that each $theta in E(M)$ is given by right multiplication by some
      element $theta(e) in e Lambda e$, and that $T(theta)={theta(e)}^ast$.],
    [Let $M in cal(P)(Lambda)$, and choose $N in cal(P)(Lambda)$ so that
      $M plus.o N tilde.equiv Lambda^((r))$ for some $r$. Each $theta in E(M)$
      extends to an element $theta_1 in End_Lambda lr((Lambda^((r))))$ by
      letting $theta_1$ vanish on $N$. Represent $theta_1$ as an $r times r$
      matrix over $Lambda$, and show that $T(theta)$ is precisely the trace of
      this matrix, viewed as element of $Lambda^ast$.],
  )
] <exc:projective-module-trace>

#hint([@exc:projective-module-trace])[
  In (i), we have (using notation of §@ss:morita-theorems)
  $ m theta=sum(m, f_j)m_j $
  #source(708)
  for some elements $f_j in M'$; so $a_(i j)=(m_i,f_j)$ for each $i$. Then
  $ m_i theta=sum_j (m_i,f_j)m_j=m_i sum_j [f_j,m_j] $
  implies that $theta=mu{sum f_j times.o m_j}$. Therefore
  $
    T(theta)=(alpha mu^(-1))(theta)=alpha{sum f_j times.o m_j}
    =sum(m_j, f_j)^ast=sum a_(j j)^ast.
  $
  For (ii), define $f in M'$ by $(m,f)=m theta(e)$, $m in M$. Then
  $mu(f times.o e)=theta$, so
  $ T(theta)=alpha(f times.o e)=(e,f)^ast={e theta(e)}^ast={theta(e)}^ast. $
]

#exercise[
  Show that the conclusion of Theorem
  @th:p-solvable-positive-projective-character-image does not hold for the case
  where $R$ is the ring $hat(ZZ)_5$ of $5$-adic integers and $G=S_5$, which is
  _not_ $5$-solvable.
] <exc:projective-character-positive-cone>

#hint([@exc:projective-character-positive-cone])[
  Suppose the conclusion does hold, and let $x=(12345) in G$. Then $tau$ maps
  $K_0^+(R G)$ onto the semigroup
  $ T={chi in op("ch")^+ K G:chi(x)=0}. $
  Since $K_0^+(R G)$ is a free semigroup on $6$ generators and $tau$ is monic,
  the image $T$ is also free. Write $chi=sum_(i=1)^7 a_i zeta^i$, $a_i in ZZ^+$,
  where the ${zeta^i}$ are the irreducible $QQ$-characters of $G$ (see
  §@ss:character-table). Then
  $ chi(x)=0 "if and only if" a_1+a_2+a_7=a_3+a_4. $
  Thus
  $ T={(a_1,...,a_7) in (ZZ^+)^((7)):a_1+a_2+a_7=a_3+a_4}. $
  But $T$ requires at least $8$ generators, which gives a contradiction.
]
