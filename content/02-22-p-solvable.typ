#import "main-defs.typ": *
#import "statements.typ": *

== Modular Representations of $p$-Solvable Groups <sec:p-solvable-groups>

#source(535)
Let $(K,R,k)$ be a $p$-modular system, with $K$ sufficiently large relative to
some given finite group $G$. The main result of this section is that if $G$ is a
_solvable_ group, then every simple $k G$-module $F$ is obtained from some
simple $K G$-module by reduction mod $frak(p)$. This is clearly a considerable
strengthening of our earlier result that the decomposition map
$d:G_0 lr((K G)) -> G_0 lr((k G))$ is surjective (see
@cor:decomposition-map-surjective). The restriction that $G$ be solvable cannot
be omitted, in general, as will be clear from
Corollary~@cor:p-solvable-irreducible-degree-divisibility below. On the other
hand, the main result is valid for a wider class of groups, consisting of all
$p$-solvable groups. This version of the main result is due to Fong, Swan
(@bib:Swan1963, Theorem 6, using Fong~@bib:Fong1961), and
Rukolaine~@bib:Rukolaine1962.

Let $p$ be any prime. We recall from §@ss:background-group-theory that a finite
group $G$ is _$p$-solvable_#idx("group", "p-solvable")#idx("p-solvable group")
if $G$ has a normal series each of whose factors is either a $p$-group or a
$p'$-group. We say that $G$ is $p$-solvable of _height $m$_
#idx("height of p-solvable group")
if $m$ is the minimal number of factors in such a normal series. Evidently, a
solvable group is $p$-solvable for every prime $p$.

Throughout this section, $G$ denotes a finite $p$-solvable group, and $(K,R,k)$
a $p$-modular system, with $K$ sufficiently large, and $char K=0$. The main
result is as follows:

#theorem(name: "Fong-Swan-Rukolaine Theorem")[
  Let $F$ be a simple $k G$-module, where $G$ is a finite $p$-solvable group.
  Then there exists a simple $K G$-module $Z$ such that
  $F tilde.equiv Z_0 slash frak(p)Z_0$ for each full $R G$-lattice $Z_0$ in $Z$.
] <th:fong-swan-rukolaine>
#idx("Fong-Swan-Rukolaine Theorem", target: [@th:fong-swan-rukolaine])

Besides the original sources of the theorem, there is a new and elegant proof
due to Serre (@bib:Serre1977, §17.4), which was reproduced in Dornhoff
(@bib:Dornhoff1972, Part B, §72). We shall give a leisurely account of Serre's
proof, pointing out, as we go along, connections with Clifford theory and
projective representations.

#proof(head: emph[Proof of @th:fong-swan-rukolaine.])[
  _Step 1._ Let bars denote reduction mod $frak(p)$. If $Z_0$ and $Z_1$ are a
  pair of full $R G$-lattices in a $K G$-module $Z$, then by
  @prop:lattice-reduction-composition-factors $overline(Z_0)$ and
  $overline(Z_1)$ have the same composition factors. Therefore if
  $overline(Z_0) tilde.equiv F$, then also $overline(Z_1) tilde.equiv F$, so it
  suffices to find a single $R G$-lattice $Z_0$ with the desired property.

  Now let $(K',R',k')$ be another $p$-modular system, with $K'$ a finite
  extension field of $K$, $R' inter K=R$, and $k'$ a finite extension of $k$.
  Suppose the result is known for the $p$-modular system $(K',R',k')$. We assert
  that it also holds for $(K,R,k)$. Let $F$ be a simple $k G$-module; then
  $F'=k' times.o_k F$ is a simple $k'G$-module, since $k$ is a splitting field
  by @cor:modular-system-sufficiently-large-fields. By hypothesis, there exists
  a simple $K'G$-module $Y$, and a full $R'G$-lattice $Y_0$ in $Y$, such that
  $Y_0 slash frak(p)'Y_0 tilde.equiv F'$. By
  @prop:lattice-reduction-composition-factors, the same result holds for any
  other full $R'G$-lattice in $Y$, because $F'$ is simple. Since $K$ is a
  splitting field for $G$, we have $Y=K' times.o_K Z$ for some simple
  $K G$-module $Z$, by @prop:splitting-field-criteria(iii). Let $Z_0$ be a full
  $R G$-lattice in $Z$. Then
  #source(536)
  $Y'_0=R' times.o_R Z_0$ is a full $R'G$-lattice in $Y$, and we have
  $
    (R' times.o_R Z_0) slash frak(p)'(R' times.o_R Z_0)
    tilde.equiv (R' slash frak(p)'R') times.o_k (Z_0 slash frak(p)Z_0)
    tilde.equiv k' times.o_k overline(Z_0),
  $
  where $overline(Z_0)=Z_0 slash frak(p)Z_0$. Then by the preceding remarks, we
  have $k' times.o_k overline(Z_0) tilde.equiv F' tilde.equiv k' times.o_k F$,
  and hence $overline(Z_0) tilde.equiv F$ by the Noether-Deuring Theorem
  (Exercise~@exc:noether-deuring).

  _Step 2._ We shall prove @th:fong-swan-rukolaine by using induction on the
  height $m$ of $G$, and for groups of the same height, by using induction on
  the order of $G$. We note that if $G$ has height $1$, then $G$ is either a
  $p$-group or a $p'$-group, and the result follows from
  @th:p-group-algebra-local or Exercise~@exc:prime-to-p-projective-lifts.
  Therefore, we may assume that $m>=2$. In that case, $G$ contains either a
  normal $p$-subgroup $D$, or a normal $p'$-subgroup $H$, such that the height
  of the quotient group is at most $m-1$. In the former case, $D$ acts trivially
  on each simple $k G$-module $F$, by @prop:normal-p-subgroup-brauer-kernel.
  Therefore, each simple $k G$-module $F$ can be viewed as a simple
  $k(G slash D)$-module, and hence can be lifted to a simple $K G$-module, by
  the induction hypothesis. Thus the theorem holds when $G$ contains such a
  subgroup $D$.

  _Step 3._ From now on, we may assume that $G$ has height $m>=2$, and contains
  a normal $p'$-subgroup $H$ for which $G slash H$ has height $m-1$. Given a
  simple $k G$-module $F$, its restriction $F_H$ is a direct sum of simple
  $k H$-modules, by Clifford's Theorem~@th:clifford-theorem. If $L$ is one such
  summand, let $T$ be the stabilizer of $L$, that is,
  $T={x in G:attach(L, tl: x) tilde.equiv L}$. Then by @th:clifford-theorem(iv),
  $F tilde.equiv "ind"_T^G F_1$ for some simple $k T$-module $F_1$. If $T!=G$,
  then we can use the induction hypothesis to lift $F_1$ to a $K T$-module, and
  hence lift $F$ ($tilde.equiv "ind"_T^G F_1$) to a $K G$-module. (Of course, we
  are using the fact that $T$ has height $<=m$.)

  _Step 4._ By Step 3, it remains to consider the case where $G$ has height
  $m>=2$, $H$ is a normal $p'$-subgroup of $G$, and $F_H$ has a stable simple
  submodule $L$. By Clifford's Theorem~@th:clifford-projective-factorization, we
  have
  $ F tilde.equiv L times.o_k I, $
  where $L$ affords a projective representation $U$ of $G$, with factor set
  $alpha:G times G -> k$, say, and $I$ affords a projective representation $V$
  of $G slash H$, with factor set $alpha^(-1)$. In this Step 4, we shall lift
  $U$ to a projective $R$-representation of $G$. Later we shall lift $V$, and
  then glue together the resulting projective $R$-representations of $G$ to
  obtain the desired $R$-representation of $G$.

  Since $L$ is a simple $k H$-module, and $H$ is a $p'$-group, there exists an
  $R H$-lattice $M$ such that $K M$ is absolutely simple and $overline(M)=L$, by
  @cor:prime-to-p-brauer-ordinary-characters. Further, for each $x in G$ we have
  $attach(overline(M), tl: x) tilde.equiv
  overline(attach(M, tl: x)) tilde.equiv overline(M)$, since $L$ is a stable
  $k H$-module. We may now#footnote[
    We could instead use Exercise~@exc:invertible-group-order-projective-lattice
    and @prop:projective-cover-summary(iv).
  ] apply Theorem~@th:invertible-group-order-lattice-isomorphism, using the fact
  that $|H|$ is a unit in $R$, to conclude that for each $x in G$, there is an
  isomorphism of $R H$-lattices $M tilde.equiv attach(M, tl: x)$. It follows
  that for each $x in G$ there exists an $R$-automorphism $S(x)$ of $M$
  #source(537)
  such that
  $
    S(h)m=h m "and" h S(x)m=S(x)h^x m
    quad "for all" m in M,h in H,x in G.
  $ <eq:stable-lattice-intertwiners>
  An easy computation shows that for all $x,y in G$, we have
  $S(y)^(-1)S(x)^(-1)S(x y) in End_(R H)(M)$. Since $K M$ is absolutely simple,
  it follows that for $x,y in G$, there exists a unit $beta(x, y) in R$ such
  that
  $ S(x)S(y)=beta(x, y)S(x y), $ <eq:lifted-projective-factor-set>
  and hence $S:G -> GL(M)$ is a projective $R$-representation of $G$. Moreover,
  for each $x in G$, there exists a $k$-automorphism $overline(S)(x)$ of
  $overline(M)$ corresponding to $S(x)$, with the following properties:
  $
    cases(
      overline(S)(h)overline(m)=overline(h m)
      "and" h overline(S)(x)overline(m)
      =overline(S)(x)h^x overline(m),
      overline(S)(x)overline(S)(y)=overline(beta)(x,y)overline(S)(x y)
      quad "for all" x\,y in G\,h in H\,overline(m) in overline(M).
    )
  $
  By the remarks following @th:clifford-projective-factorization it follows that
  the projective $k$-representation $overline(S)$ of $G$ is equivalent to $U$,
  and we have lifted $U$ to a projective $R$-representation of $G$, completing
  the proof of Step 4. By replacing $V$ by an equivalent representation, we may
  identify $U$ with $overline(S)$.

  _Step 5._ In order to lift the projective $k$-representation $V$ to a
  projective $R$-representation of $G$, we have to use the induction hypothesis,
  which does not work smoothly for projective representations. Therefore we
  shall first apply the methods of §@sec:clifford-theory-hecke-algebras to
  construct a central extension $E$ of $G$ to which the $k$-representations $U$
  and $V$, and the $R$-representation $S$, can all be lifted.

  Let $b in H^2(G,R^dot)$ be the equivalence class of the factor set
  $beta:G times G -> R^dot$ which occurs in @eq:lifted-projective-factor-set. We
  shall now prove that $b$ has finite order $e$, where $p divides.not e$, when
  $b$ is viewed as an element of the multiplicative group $H^2(G,R^dot)$. Let us
  put
  $ d=R"-rank" M=dim_K K M. $
  Then $d$ divides $|H|$ by @prop:character-degree-divides-group-order, since
  $K M$ is an absolutely simple $K H$-module. Therefore $d$ is relatively prime
  to $p$, because $H$ is a $p'$-group. Relative to some $R$-basis of $M$, each
  $S(x)$ can be represented by a matrix $bold(S)(x) in GL_d lr((R))$, $x in G$.
  We set $g(x)=det bold(S)(x) in R^dot$, $x in G$. Taking determinants in
  @eq:lifted-projective-factor-set, we obtain
  $ g(x)g(y)={beta(x, y)}^d g(x y) quad "for all" x,y in G. $
  This implies that $b^d=1$ in $H^2(G,R^dot)$, and completes the proof that the
  order $e$ of $b$ is finite, and that $p divides.not e$. (See
  Exercise~@exc:projective-determinant-factor-set.)

  Put $rho(h)=S(h)$ for $h in H$, and take $S(1)=1$. Since $rho$ is a
  representation of $H$, we have $beta(h, l)=1$ for $h,l in H$. Under the
  identification $F tilde.equiv overline(S) times.o_k V$ from Step 4, $H$ acts
  as $overline(rho) times.o 1$, so $V(h)=1$ for $h in H$.

  Since $b^e=1$ in $H^2(G,R^dot)$, there exists a normalized map $a:G -> R^dot$
  such that
  $ a(x)a(y)={beta(x, y)}^e a(x y) quad "for all" x,y in G. $
  #source(538)
  Put $N=e |H|$, which is prime to $p$. Let $K'$ be the finite extension of $K$
  obtained by adjoining all $e$-th roots of the elements $a(x)$ and all $N$-th
  roots of $1$, and extend the valuation ring to $R'$ in $K'$, with residue
  field $k'$. The roots of the units $a(x)$ are units of $R'$. By Step 1, we may
  extend all the existing objects to this modular system and suppress the
  scalar-extension notation; the final lift for the original group $G$ will
  descend to the original system.

  Choose units $c(x)$ with $c(x)^e=a(x)^(-1)$ and $c(1)=1$, and put
  $
    S'(x)=c(x)S(x),quad
    beta'(x,y)=c(x)c(y)c(x y)^(-1) beta(x, y).
  $
  Then $beta'$ takes values in the group $mu_e$ of $e$-th roots of $1$. At the
  same time put
  $ U'(x)=overline(S')(x),quad V'(x)=overline(c)(x)^(-1)V(x). $
  The factor sets of $U'$ and $V'$ are inverses, and
  $U' times.o_k V'=overline(S) times.o_k V$, so this inverse rescaling leaves
  the representation afforded by $F$ unchanged. Because $beta(h, l)=1$ on
  $H times H$, the restriction of $a$ to $H$ is a linear character. Thus
  $a(h)^|H|=1$ and $c(h)^N=1$ for $h in H$.

  Let $omega$ be a primitive $N$-th root of $1$ in $R$. We may write
  $ beta'(x,y)=omega^(n(x,y)),x,y in G, $ <eq:root-of-unity-factor-set>
  where $0<=n(x,y)<N$. Here $beta'$ still takes values in $mu_e subset.eq mu_N$;
  the larger group is used to accommodate all the scalars $c(h)$ on $H$.

  Now let $B=chevron.l b chevron.r$ be cyclic of order $N$, and identify it with
  $mu_N$ by the faithful character $psi:B -> R^dot$, $psi(b)=omega$. As in the
  proof of @th:schur-projective-lifting, define
  $ f:G times G -> B,quad f(x,y)=b^(n(x,y)),x,y in G. $
  This is a factor set. By §@ss:schur-split-extensions it defines a central
  extension
  $ 1 -> B -> E arrow.r^pi G -> 1, $
  with section $x arrow.r u_x$, multiplication $u_x u_y=f(x,y)u_(x y)$, and
  unique expressions ${b^i u_x:0<=i<N,x in G}$. In particular, $|E|=N |G|$.

  The map
  $ tilde(S)(b^i u_x)=psi(b^i)S'(x),i in ZZ,x in G, $
  is an ordinary $R$-representation of $E$. Let $overline(psi)$ be the reduction
  of $psi$. Since $p divides.not N$, reduction is injective on $mu_N$, so
  $overline(psi)$ is also faithful.
  #source(539)
  Define ordinary $k$-representations of $E$ by
  $
    U^*(b^i u_x)=overline(psi)(b^i)U'(x),quad
    V^*(b^i u_x)=overline(psi)(b^i)^(-1)V'(x).
  $
  Thus $U^*$ is the reduction of $tilde(S)$, and the tensor product
  $U^* times.o_k V^*$ is trivial on $B$ and descends to the representation of
  $G$ afforded by $F$.

  _Step 6._ We shall lift $V^*$ to an ordinary $R$-representation of $E$. For
  $h in H$, let $z_h in B$ be the element with $psi(z_h)=c(h)^(-1)$, and define
  $iota(h)=z_h u_h$. This is possible since $c(h)^N=1$. The identity
  $beta'(h,l)=c(h)c(l)c(h l)^(-1)$ shows that $iota(h)iota(l)=iota(h l)$;
  projection to $G$ proves injectivity and $iota(H) inter B=1$. Moreover,
  $ tilde(S)(iota(h))=rho(h),quad V^*(iota(h))=1. $
  In each fibre of $pi$ over $h in H$, faithfulness of $overline(psi)$ implies
  that $iota(h)$ is the unique element killed by $V^*$. Therefore
  $ iota(H)=pi^(-1) lr((H)) inter ker V^*, $
  which is normal in $E$. We may consequently form $overline(E)=E slash iota(H)$
  and obtain a central extension
  $ 1 -> B -> overline(E) -> G slash H -> 1. $
  This supplies the compatible copy of $H$ needed for the quotient.#ed-note[
    The original argument did not construct a compatible copy of $H$ after
    rescaling its factor set. The construction here enlarges the cyclic kernel
    to order $e |H|$ and rescales the complementary tensor factor inversely, so
    the representation of $G$ is preserved.
  ]

  Before applying induction, extend the modular system finitely once more, if
  necessary, so that its characteristic-zero field is sufficiently large for the
  now fixed finite group $E$. The representation $V^*$ is absolutely simple: a
  nonzero proper invariant subspace after field extension would give a proper
  submodule of the absolutely simple module $F$ by tensoring with $U'$. Hence it
  stays simple under this extension. Step 1 permits descent of the eventual lift
  for the original group $G$; we again suppress the scalar-extension notation.
  We shall apply induction to lift $V^*$ from $overline(E)$, and hence to $E$.

  By assumption, $G slash H$ is $p$-solvable of height $<=m-1$, where $m$ is the
  height of $G$, and $m>=2$. Thus $overline(E)$ contains a normal subgroup
  $D>=B$ such that
  $overline(E) slash D tilde.equiv (overline(E) slash B) slash (D slash B)$ has
  height $<=m-2$, and $D slash B$ is either a $p$-group or a $p'$-group. If
  $D slash B$ is a $p$-group, then $D tilde.equiv P times B$ for some $p$-group
  $P$, since $B$ is central. Then $P ⊴ overline(E)$, and $P subset.eq ker V^*$,
  by @prop:normal-p-subgroup-brauer-kernel. Then $overline(E) slash P$ is
  $p$-solvable of height $<=m-1$, and $V^*$ can be lifted to an
  $R$-representation of $overline(E) slash P$, and hence to an
  $R$-representation of $E$, by the induction hypothesis.

  On the other hand, if $D slash B$ is a $p'$-group, then $D$ is a normal
  $p'$-subgroup of $overline(E)$, so the height of $overline(E)$ is $<=m-1$. By
  induction, we can then lift $V^*$ to an $R$-representation of $E$, which we
  again denote by $T$.

  _Step 7._ We can now complete the proof of the theorem as follows. By Step 4
  and the inverse rescaling in Step 5, the simple $k G$-module $F$ affords a
  $k$-representation of the form $U' times.o_k V'$, where $U'$ and $V'$ are
  projective $k$-representations, whose factor sets are inverses of one another.
  In Steps 5 and 6, these projective representations were lifted to ordinary
  $k$-representations $U^*$ and $V^*$ of $E$, where $E$ is the central extension
  of $G$ with cyclic kernel $B$ of order $N$, prime to $p$, as in Step 5. Then
  $U^* times.o_k V^*$ is a $k$-representation of $E$, whose kernel contains $B$,
  because of the way $U^*$ and $V^*$ were defined, using $overline(psi)$ and
  $overline(psi)^(-1)$ on $B$, etc. Then $U^* times.o_k V^*$ defines a
  $k$-representation of $G=E slash B$, and by the previous discussion, this is a
  $k$-representation of $G$ afforded by $F$.

  In Steps 4–6, the $k$-representations $U^*$ and $V^*$ were lifted to
  $R$-representations $tilde(S)$ and $T$ of $E$. Denote $tilde(S)$ by $S$ in
  this final step. Then $S times.o_R T$ is an $R$-representation of $E$, such
  #source(540)
  that $overline(S times.o_R T)$ is a $k$-representation equivalent to
  $U^* times.o_k V^*$, (where $overline(S times.o_R T)$ denotes the
  representation of $E$ obtained by reduction mod $frak(p)$ of $S times.o_R T$).

  Finally, there is the question as to whether $S times.o_R T$ defines a
  representation of $G$. Since $B$ is a $p'$-group, which is contained in the
  kernel of $overline(S times.o_R T)$ it follows by
  @cor:prime-to-p-brauer-ordinary-characters that $B$ is also contained in the
  kernel of $S times.o_R T$. Therefore $S times.o_R T$ defines an
  $R$-representation of $G$ whose reduction mod $frak(p)$ is the
  $k$-representation afforded by $F$. This completes the proof of the
  Fong-Swan-Rukolaine Theorem.
]

#corollary[
  The degree of each irreducible $k$-representation of a $p$-solvable group $G$
  coincides with the degree of some irreducible $K$-representation, and hence
  divides the order of $G$.
] <cor:p-solvable-irreducible-degree-divisibility>

In an example at the end of §@sec:brauer-characters, it was shown that the
degrees of the irreducible $k$-representations of $op("SL")_2 lr((p))$, where
$p=char k$, need not divide the order of $op("SL")_2 lr((p))$. By
Corollary~@cor:p-solvable-irreducible-degree-divisibility, it follows that, in
general, the conclusion of Theorem~@th:fong-swan-rukolaine does not hold for the
groups ${op("SL")_2 lr((p))}$.

#corollary[
  Let $phi$ be an irreducible Brauer character of a finite $p$-solvable group
  $G$, afforded by a simple $k G$-module, where $char k=p$. Then there exists an
  irreducible $K$-character $zeta$ of $G$ such that $zeta_(G_(p'))=phi$, where
  $zeta_(G_(p'))$ denotes the restriction of $zeta$ to the $p'$-elements of $G$.
] <cor:p-solvable-brauer-character-lift>

#corollary[
  For each simple $k G$-module $F_j$ there is an irreducible $K G$-module $Z_i$
  such that $d[Z_i]=[F_j]$, where $G$ is $p$-solvable and $(K,R,k)$ is as above.
  Equivalently, the decomposition matrix contains a row $i$ with $d_(i j)=1$ and
  $d_(i ell)=0$ for $ell!=j$.#ed-note[
    The original claim that every decomposition number is $0$ or $1$ is false.
    For $D_8$ in characteristic $2$, an ordinary irreducible representation of
    degree $2$ reduces to two trivial composition factors, giving a
    decomposition number $2$. The stated replacement is the precise consequence
    of @th:fong-swan-rukolaine.
  ]
] <cor:p-solvable-decomposition-numbers>

For other results on modular representations of $p$-solvable groups, see
Fong~@bib:Fong1962, Cliff~@bib:Cliff1975, @bib:Cliff1977, and
Isaacs~@bib:Isaacs1974, @bib:Isaacs1978. In Isaacs~@bib:Isaacs1974, there is
another proof of the Fong-Swan-Rukolaine Theorem, using some of Gallagher's
results on extending invariant characters from normal subgroups (see
§@ss:extensions-invariant-characters), instead of the theory of projective
representations. Isaacs also points out that the character $zeta$ in
@cor:p-solvable-brauer-character-lift is not uniquely determined.

We conclude by summarizing without proof the main result of
Isaacs~@bib:Isaacs1974. A $K$-character $zeta$ of $G$ is called _$p$-rational_
#idx("p-rational character")
if for each $x in G$ the character value $zeta(x)$ can be expressed as a sum of
roots of unity of orders prime to $p$. Isaacs shows that if $G$ is a
$p$-solvable group with $p!=2$, then every irreducible Brauer character $phi$ of
$G$ can be lifted to a character $zeta in Irr G$ such that
#enum(
  numbering: "(i)",
  [$zeta$ is $p$-rational, and],
  [If $H ⊴ G$, and $psi$ is any irreducible character of $H$ occurring in
    $zeta_H$, then $psi$ is $p$-rational and its restriction $psi_(H_(p'))$ is
    an irreducible Brauer character of $H$.],
)
Furthermore, these properties (i) and (ii) uniquely determine the character
$zeta$ lifting $phi$.

#source(541)
#exercise-heading

#exercise[
  Let $G$ be a finite group with a normal $p$-complement $H$, and let $(K,R,k)$
  be a $p$-modular system with $K$ sufficiently large. Prove that each
  indecomposable projective Brauer character $eta^i$ can be expressed in the
  form $lambda^G$, for some $lambda in Irr_k H$. (For extensions of this result
  to general $p$-solvable groups, see Fong~@bib:Fong1962, Theorem 2D.)
] <exc:normal-p-complement-projective-brauer-induction>
