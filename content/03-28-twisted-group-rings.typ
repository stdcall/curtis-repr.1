#import "main-defs.typ": *
#import "statements.typ": *

== Twisted Group Rings and Crossed-Product Orders <sec:twisted-group-rings>

The twisted group ring $S circle.small G$ of a finite group $G$, over some
commutative ring $S$, is a natural generalization of the ordinary group ring
$S G$. In the case of twisted group rings, we assume that $G$ acts as a group of
automorphisms of $S$, and then “twist” the multiplication in $S circle.small G$
according to this action. Specifically, suppose that $a arrow.r sigma(a)$,
$a in S$, is the automorphism of $S$ which corresponds to the element
$sigma in G$. We then define multiplication in $S circle.small G$ according to
the rule
$ sigma dot a=sigma(a) sigma "for all" sigma in G, a in S. $
If each $sigma in G$ acts as the identity automorphism of $S$, then of course we
obtain the ordinary group ring $S G$ once more.

We have already seen, in Example @exm:dihedral-group-algebra-reduced-norm, that
twisted group algebras may arise as Wedderburn components of ordinary group
algebras. In the same way, problems about integral representations of groups
often lead to questions about lattices over twisted group rings. In practice,
$G$ is the Galois group of some finite Galois extension $L$ of a field $K$, $R$
is a Dedekind domain with quotient field $K$, and $S$ is the integral closure of
$R$ in $L$. Then we can form the twisted group algebra $L circle.small G$, which
will turn out to be a full matrix algebra over $K$. This algebra contains the
twisted group ring $S circle.small G$, which is an $R$-order in
$L circle.small G$.

As we shall see, the properties of the twisted group ring $S circle.small G$
depend strongly upon the arithmetic nature of the inclusion $R subset.eq S$. The
first basic
#source(611)
result below is that $S circle.small G$ is a maximal $R$-order if and only if
$d(S slash R)=R$, where $d(S slash R)$ denotes the discriminant ideal of $S$
relative to $R$ (see end of §@ss:dedekind-ideal-theory). The second important
fact is that $S circle.small G$ is a hereditary ring if and only if
$T_(L slash K) lr((S))=R$. As we shall see, the conditions that
$d(S slash R)=R$, or that $T_(L slash K) lr((S))=R$, are equivalent to
assertions about the behavior of maximal ideals of $R$ in the larger ring $S$.

We will then work out an example where it is possible to classify completely all
$(S circle.small G)$-lattices. This example will be used in
§@ss:dihedral-metacyclic-integral-representations, where it will play a vital
role in the determination of integral representations of a dihedral group of
order $2p$, or more generally, of certain metacyclic groups.

The section concludes with a brief discussion of orders in crossed-product
algebras. Twisted group algebras are special cases of crossed-product algebras,
and some of our results have natural extensions to orders in such algebras.

The material in this section is quite important from the standpoint of
classifying integral representations of groups in certain specific cases.
However, unlike the earlier sections of this chapter, the present section does
not play as crucial a role in the treatment in Chapter
@ch:local-global-integral-representations of integral representation theory.
Some readers may therefore wish to concentrate on the examples and statements of
theorems, and return later to the details of the proofs.

We begin by defining the _twisted group ring_#idx("twisted group ring")#idx(
  "twisted group algebra",
)#footnote[
  Another kind of twisted group algebra was introduced in
  @exm:crossed-products-twisted-group-algebras(ii), and was used in
  §@ss:clifford-systems and §@ss:green-indecomposability.
] $S circle.small G$ of a finite group $G$, where $S$ is a commutative ring on
which $G$ acts as a group of automorphisms. We set
$ S circle.small G=op("⨁", limits: #true)_(sigma in G) S u_sigma, $
<eq:twisted-group-ring-module>
where the symbols ${u_sigma:sigma in G}$ form a $S$-basis for
$S circle.small G$, and multiplication is defined by
$
  (a u_sigma)(b u_tau)=a sigma(b)u_(sigma tau)
  "for all" a,b in S, sigma,tau in G.
$ <eq:twisted-group-ring-multiplication>

#example[
  Let $R$ be a Dedekind domain with quotient field $K$, and let $S$ be the
  integral closure of $R$ in a finite Galois extension $L$ of $K$, with Galois
  group $G$. Each $sigma in G$ determines a $K$-automorphism of $L$, inducing an
  $R$-automorphism of $S$, and we may form the rings
  $ A=plus.o L u_sigma,quad Lambda=plus.o S u_sigma. $
  Then $u_1$ is the identity element of $A$, and we leave it as an exercise for
  the reader to check that:
  $ "center of" A=K u_1,quad "center of" Lambda=R u_1. $
  #source(612)
  Thus, $A$ is a $K$-algebra (but not an $L$-algebra, if $L!=K$!), and $Lambda$
  is an $R$-order in $L circle.small G$.

  Let us show at once that there is an isomorphism of $K$-algebras:
  $ A tilde.equiv M_n lr((K)),quad "where" n=dim_K L=|G|. $
  We define a map $psi:A arrow End_K L$ by
  $ a arrow.r a_l,quad u_sigma arrow.r sigma,quad "for" a in L,sigma in G. $
  Since
  $ (a_l sigma)(b_l tau)=a_l sigma(b)_l sigma tau=(a sigma(b))_l sigma tau $
  for $a,b in L$, $sigma,tau in G$, it follows at once that $psi$ is a
  homomorphism of $K$-algebras. Let us show that $psi$ is a monomorphism, by
  proving that $A$ has no nontrivial two-sided ideals. Indeed, if $X$ is a
  nonzero two-sided ideal of $A$, let
  $ x=a_(sigma_1)u_(sigma_1)+dots+a_(sigma_r)u_(sigma_r) in X,quad x!=0, $
  with $r$ minimal. If $r>1$, choose $b in L$ with
  $sigma_1 lr((b))!=sigma_2 lr((b))$. Then $x-sigma_1 lr((b))^(-1)x b$ is a
  nonzero element of $X$ with a shorter expression. This contradicts our choice
  of $x$, so necessarily $r=1$, and then $X$ contains a unit
  $a_(sigma_1)u_(sigma_1)$ of $A$. Therefore $X=A$, as desired. This completes
  the proof#footnote[
    Compare this proof with the Hint in
    Exercise~@exc:artin-embeddings-independent.
  ] that $psi$ is an algebra monomorphism. Since $A$ and $End_K L$ both have
  $K$-dimension $n^2$, it follows that $psi$ is an isomorphism. Of course,
  $End_K L tilde.equiv M_n lr((K))$ since $dim_K L=n$.

  For later use, we note that the map $psi$ enables us to view $L$ as a left
  $A$-module, and then obviously $L$ is a simple left $A$-module. The action of
  $A$ on $L$ is given explicitly by
  $ (a u_sigma)x=a sigma(x),quad a,x in L,sigma in G. $
  This construction was used in the proof of
  @prop:hyperelementary-simple-module-lifting.
] <exm:galois-twisted-group-algebra>

#example[
  As a second example of a twisted group ring, let $n>2$, and put
  $
    H=chevron.l x,y:x^n=1,y^2=1,y x y^(-1)=x^(-1) chevron.r,quad
    G=chevron.l y chevron.r,quad C=chevron.l x chevron.r,
  $
  and let $R$ be any commutative ring. We let $G$ act as a group of
  automorphisms on the ordinary group ring $R C$ by defining
  $ attach(xi, tl: y)=y xi y^(-1) "for all" xi in R C, $
  where the product $y xi y^(-1)$ is computed inside the ordinary group ring
  $R H$. We may form the twisted group ring $(R C) circle.small G$, and obtain
  an isomorphism of
  #source(613)
  $R$-algebras
  $ R H tilde.equiv (R C) circle.small G. $
  For $xi in R H$, we have $y xi=attach(xi, tl: y)y$.

  Now let $omega$ be a primitive $n$-th root of $1$ over $QQ$, and let $Phi(X)$
  be the cyclotomic polynomial of order $n$. Then
  $Phi(X)="min. pol."_QQ lr((omega))$, and $omega^(-1)$ is also a zero of
  $Phi(X)$. It follows that
  $ X^(phi(n)) Phi lr((X^(-1)))=plus.minus Phi(X). $
  Since
  $ attach({Phi(x)}, tl: y)=y Phi(x)y^(-1)=Phi lr((x^(-1))) "in" ZZ H, $
  it follows that $Phi(x) ZZ H$ is a two-sided ideal in $ZZ H$. There are ring
  isomorphisms
  $
    ZZ H slash Phi(x) ZZ H
    tilde.equiv {ZZ C slash Phi(x) ZZ C} circle.small G
    tilde.equiv ZZ[omega] circle.small G,
  $
  and here $ZZ[omega]=op("alg. int."){QQ(omega)}$ (see §@ss:cyclotomic-fields).
  Since $y x y^(-1)=x^(-1)$, and the map $ZZ C arrow ZZ[omega]$ carries $x$ onto
  $omega$, it follows that $attach(omega, tl: y)=omega^(-1)=overline(omega)$ in
  the twisted group ring $ZZ[omega] circle.small G$. Thus
  $ attach(xi, tl: y)=overline(xi),quad xi in ZZ[omega], $
  where bar denotes complex conjugation. Thus, twisted group rings appear
  naturally as factor rings of ordinary group rings. The same argument shows
  that the twisted group algebra $QQ(omega) circle.small G$ is a simple
  component of the ordinary group algebra $QQ H$.
] <exm:dihedral-twisted-group-ring>

Until further notice, we shall adopt the notation and hypotheses of Example
@exm:galois-twisted-group-algebra, so let $L$ be a finite Galois extension of
$K$ with Galois group $G$, and let $S$ be the integral closure of $R$ in $L$.
The first major result, due to Auslander-Goldman @bib:Auslander1960b, is as
follows:

#theorem[
  The twisted group ring $S circle.small G$ is a maximal $R$-order in
  $L circle.small G$ if and only if the discriminant ideal $d(S slash R)$
  coincides with $R$.
] <th:twisted-group-ring-maximality>
#idx("Auslander-Goldman Theorem", target: [@th:twisted-group-ring-maximality])
#proof[
  For each maximal ideal $P$ of $R$, let the subscript $P$ denote localization
  at $P$. We have
  $ (S circle.small G)_P=S_P circle.small G, $
  and by @th:maximal-orders-localization, $S circle.small G$ is maximal if and
  only if $S_P circle.small G$ is a maximal $R_P$-order
  #source(614)
  for each $P$. Further,
  $ d(S_P slash R_P)={d(S slash R)}_P $
  by §@ss:valuations-completions. Hence it suffices to prove the result when $R$
  is replaced by $R_P$. Changing notation, we may assume for the rest of the
  proof that $R$ is a d.v.r.

  Let us put $A=L circle.small G$, $Lambda=S circle.small G$. As in
  §@ss:maximal-orders-existence, the discriminant ideal $d(Lambda)$ is computed
  by using the reduced trace $tr$ from $A$ to $K$, while the discriminant ideal
  $d(S slash R)$ is computed by using the ordinary trace $T$ from $L$ to $K$.
  Let us show first that #named-equation(name: [$(ast)$])[
    $ d(Lambda)={d(S slash R)}^n, $
  ] <eq:twisted-order-discriminant>
  where $n=dim_K L=|G|$. Let $S=op("⨁", limits: #true)_(i=1)^n R s_i$,
  $G={sigma_1,dots,sigma_n}$; then $Lambda$ has an $R$-basis
  ${s_i u_(sigma_j):1<=i,j<=n}$, and by
  @eq:reduced-trace-norm-center-transitivity we have:
  $
    tr{(s_i u_(sigma_j))(s_k u_(sigma_l))}
    &=tr{s_i sigma_j lr((s_k))u_(sigma_j)u_(sigma_l)} \
    &=cases(
      T lr((s_i sigma_j lr((s_k)))) & quad "if" sigma_j=sigma_l^(-1),
      0 & quad "otherwise."
    )
  $
  It follows that
  $
    d(Lambda)=R dot product_(j=1)^n det[T lr(
        (s_i sigma_j
          lr((s_k)))
      )]_(1<=i,k<=n).
  $
  However,
  $
    det[T lr((s_i sigma_j lr((s_k))))]_(1<=i,k<=n)=plus.minus det[T lr(
        (s_i
          s_k)
      )]_(1<=i,k<=n).
  $
  Furthermore,
  $ d(S slash R)=R dot det[T lr((s_i s_k))]_(1<=i,k<=n), $
  and so we obtain @eq:twisted-order-discriminant at once.

  We are now ready to complete the proof of the theorem. If $d(S slash R)=R$,
  then $d(Lambda)=R$, and therefore $Lambda$ is a maximal $R$-order by
  @prop:order-discriminant-localization(iii). Conversely, suppose that $Lambda$
  is a maximal $R$-order in $A$. Since $A tilde.equiv M_n lr((K))$ by
  @exm:galois-twisted-group-algebra, it follows that
  $Lambda tilde.equiv M_n lr((R))$ (see
  Exercise~@exc:matrix-maximal-order-endomorphisms). We shall use this fact to
  show that $d(Lambda)=R$. When an element $lambda in Lambda$ is represented by
  a matrix in $M_n lr((R))$, its reduced trace $tr(lambda)$ is precisely the
  trace of this matrix. Let ${e_(i j):1<=i,j<=n}$ be the matrix units in
  $M_n lr((R))$, so $e_(i j)$ is the matrix with entry $1$ at position $(i,j)$
  and zeros elsewhere. These $n^2$ matrix units form an $R$-basis for
  $M_n lr((R))$, and we have
  $ tr lr((e_(i j)e_(k l)))=delta_(j k)delta_(i l), $
  where $i,j,k,l$ range from $1$ to $n$. It follows that the discriminant ideal
  of the
  #source(615)
  $R$-order $M_n lr((R))$ is equal to $R$. Thus $d(Lambda)=R$ as claimed. But
  then $d(S slash R)=R$ by @eq:twisted-order-discriminant, and the proof is
  finished.
]

#remarks(numbered: false)[
  #enum(
    numbering: "(i)",
    [By §@ss:dedekind-ideal-theory, we know that $d(S slash R)=R$ if and only if
      $S$ is unramified over $R$. This means that for each maximal ideal $P$ of
      $R$, we may write $P S$ as a product $product P_i$ of distinct prime
      ideals, and that $S slash P_i$ is separable over $R slash P$ for each
      $i$.],
    [The preceding proof shows that for any Dedekind domain $R$, not necessarily
      a P.I.D., the relation $d(Lambda)={d(S slash R)}^n$ is valid.],
  )
]

#example[
  Let $Lambda=S circle.small G$, where $S=ZZ[omega]$, using the notation of
  @exm:dihedral-twisted-group-ring. Let
  $
    L=QQ(omega),quad K=QQ(omega+overline(omega)),quad
    R=ZZ[omega+overline(omega)],
  $
  so $G=op("Gal")(L slash K)$, $R=op("alg. int."){K}$, and $S$ is the integral
  closure of $R$ in $L$. If we assume that $n$ is odd, then the rational prime
  $2$ is unramified in the extension $L slash QQ$ by
  @prop:cyclotomic-unramified-primes. It follows at once that $S_2$ is
  unramified over the ring $R_2$, where the subscript $2$ denotes localization.
  (Note that $R_2$ is a semilocal Dedekind domain.) Then
  $
    S_2=ZZ_2 times.o_ZZ S=ZZ_2[omega],quad R_2=ZZ_2 times.o_ZZ
    R=ZZ_2[omega+overline(omega)].
  $
  By the Auslander-Goldman Theorem @th:twisted-group-ring-maximality, we may
  conclude that the twisted group ring $S_2 circle.small G$ is a maximal
  $R_2$-order in $L circle.small G$. However, if $n$ is an odd prime power
  greater than $1$, then $S circle.small G$ is not a maximal $R$-order in
  $L circle.small G$, since $S$ is not unramified over $R$.
] <exm:cyclotomic-conjugation-twisted-order>

We turn next to the more complicated question as to when a twisted group ring
$S circle.small G$ is a hereditary $R$-order, and again we use the notation and
hypotheses of @exm:galois-twisted-group-algebra. Our second main result, due to
Auslander-Rim @bib:Auslander1963, page 578, is as follows:

#theorem[
  The twisted group ring $S circle.small G$ is a hereditary $R$-order if and
  only if $T_(L slash K) lr((S))=R$, or equivalently, if and only if
  $T_(L slash K) lr((s_0))=1$ for some $s_0 in S$.
] <th:twisted-group-ring-heredity>
#idx("Auslander-Rim Theorem", target: [@th:twisted-group-ring-heredity])
#idx("Rim's Theorem", target: [@th:twisted-group-ring-heredity])
#proof[
  Set $Lambda=S circle.small G$, and suppose that there exists an element
  $s_0 in S$ such that $sum_(sigma in G) sigma(s_0)=1$. We must show that every
  left ideal $M$ of $Lambda$ is projective as $Lambda$-module. The map
  $s arrow.r s u_1$, $s in S$, embeds $S$ in $Lambda$. Thus every
  $Lambda$-module is also an $S$-module. Since $M$ is an $S$-submodule of the
  $S$-lattice $Lambda$, it follows that $M$ is $S$-projective. Now let
  $theta:X arrow M$ be a $Lambda$-surjection of the $Lambda$-module $X$ onto
  $M$. Then there exists $psi in Hom_S lr((M,X))$ which splits $theta$, that is,
  $theta psi=1_M$. Put
  $ psi'=sum_sigma u_sigma s_0 psi u_sigma^(-1) in Hom_Lambda lr((M,X)). $
  #source(616)
  Then
  $
    theta psi' & =sum theta u_sigma s_0 psi u_sigma^(-1)
                 =sum u_sigma s_0 theta psi u_sigma^(-1) \
               & =sum u_sigma s_0 u_sigma^(-1)=sum sigma(s_0)=1.
  $
  Hence $psi'$ splits $theta$, which shows that $M$ is $Lambda$-projective.
  (Compare this argument with that in
  Exercise~@exc:trace-surjective-galois-projective and the proof of
  @th:gaschutz-relative-projectivity.)

  We have now shown that $Lambda$ is left hereditary if
  $T_(L slash K) lr((S))=R$. A similar argument proves that $Lambda$ is right
  hereditary in this case. We could also have used the final part of the proof
  of Theorem @th:maximal-orders-are-hereditary, where we showed that an order
  $Lambda$ is left hereditary if and only if $Lambda$ is right hereditary.

  Turning to the converse, assume now that $Lambda$ is left hereditary and let
  $y=sum_sigma u_sigma in Lambda$. There is a left $Lambda$-surjection
  $phi:Lambda arrow Lambda y$, given by right multiplication by $y$. Since
  $Lambda y$ is a left ideal of $Lambda$, and hence is $Lambda$-projective,
  there exists a map $theta in Hom lr((Lambda y,Lambda))$ such that
  $phi theta=1$ on $Lambda y$. Let us set
  $ theta(y)=sum_(sigma in G) a_sigma u_sigma,quad a_sigma in S. $
  Since $u_tau y=y$ for all $tau in G$, we obtain
  $
    sum a_sigma u_sigma=theta(y)=theta(u_tau y)=u_tau theta(y)=u_tau dot sum
    a_sigma u_sigma
  $
  for each $tau$. This readily implies that $a_sigma=sigma(a_1)$ for each
  $sigma in G$. But then
  $
    y=(phi theta)(y)=lr((sum_sigma a_sigma u_sigma))y=lr(
      (sum_sigma
        sigma(a_1))
    )y,
  $
  whence $sum_sigma sigma(a_1)=1$. Hence $T_(L slash K) lr((S))=R$, and the
  theorem is established.
]

#remark(numbered: false)[
  We saw in Theorem @th:twisted-group-ring-maximality that $S circle.small G$ is
  a maximal $R$-order if and only if $S$ is unramified over $R$. It is natural
  to ask whether there is some condition on ramification which will guarantee
  that $S circle.small G$ is a hereditary $R$-order. We shall show now, using
  results from §@sec:dedekind-domains, that $S circle.small G$ is hereditary if
  and only if $S$ is tamely ramified over $R$. Indeed, we need only show that
  $T_(L slash K) lr((S))=R$ if and only if $S$ is tamely ramified over $R$. We
  have already proved this in Exercise~@exc:tame-extension-trace-surjective, and
  the remarks which follow are merely intended to summarize some results and
  definitions concerning ramification.

  To start with, let $L$ be any separable extension of $K$, not necessarily a
  Galois extension. Let $P$ range over the maximal ideals of $R$, and write
  $ P S=product_(i=1)^g P_i^(e_i),quad e_i>0, $
  where the ${P_i}$ are distinct maximal ideals of $S$. As in
  §@ss:dedekind-ideal-theory, call $P_i$ _unramified_#idx("unramified") over $R$
  if $e_i=1$ and $S slash P_i$ is a separable extension of $R slash P$; (this
  latter condition is automatically satisfied when $K$ is a global field, for
  then $R slash P$ is a finite field.) Call $P_i$ _ramified_#idx("ramified")
  over $R$ if either $e_i>1$ or $S slash P_i$ is inseparable over
  #source(617)
  $R slash P$. By §@ss:dedekind-ideal-theory (see also @bib:Reiner1975[MO
    (4.37)]), $P_i$ is ramified over $R$ if and only if $P_i$ divides the
  different $D(S slash R)$.

  We call $S slash R$ _unramified_#idx("unramified") if each maximal ideal $P_i$
  of $S$ is unramified over $R$; this occurs if and only if $D(S slash R)=S$, or
  equivalently if and only if the discriminant ideal $d(S slash R)$ coincides
  with $R$.

  The concept of _tame ramification_ plays a basic role in the question as to
  whether $T_(L slash K) lr((S))=R$. Call $P_i$ _tamely ramified_#idx(
    "ramified",
    "tamely",
  )#idx("tamely ramified") over $R$ if its ramification index $e_i$ is not zero
  in $S slash P_i$, and $S slash P_i$ is separable over $R slash P$. We call $S$
  tamely ramified over $R$ if for each maximal ideal $P$ of $R$, there exists at
  least one $P_i$ containing $P$ which is tamely ramified over $R$. Then by
  Exercise~@exc:tame-extension-trace-surjective, $S slash R$ is tamely ramified
  if and only if $T_(L slash K) lr((S))=R$.

  The preceding discussion simplifies somewhat when $L$ is a Galois extension of
  $K$, which we now assume. For each $P_i$ and each $sigma in G$, the conjugate
  ideal $P_i^sigma$ is also a maximal ideal of $S$. By @bib:CurtisReiner1962[CR
    §20], we know that $P S$ factors as a product of distinct conjugates of
  $P_i$, all factors occurring with the same ramification index. Likewise, the
  residue class fields $S slash P_i^sigma$ are mutually isomorphic over
  $R slash P$. Thus, if $P_i$ is unramified over $R$, then so is each of its
  conjugates $P_i^sigma$, $sigma in G$. Likewise, if $P_i$ is tamely ramified
  over $R$, then so is each $P_i^sigma$. Hence, when $L$ is a Galois extension
  of $K$, we see that $S slash R$ is tamely ramified if and only if each $P_i$
  is tamely ramified over $R$.

  Finally, $T_(L slash K) lr((S))$ is a nonzero ideal of $R$, and by
  Exercise~@exc:tame-extension-trace-surjective it coincides with $R$ if and
  only if $S$ is tamely ramified over $R$.
]

#example[
  Let $p$ be an odd prime, and take $n=p$ in
  @exm:cyclotomic-conjugation-twisted-order. By §@ss:cyclotomic-fields, there is
  a unique maximal ideal $P_1$ of $S$ which ramifies over $R$, namely, the ideal
  $P_1$ such that $p S=P_1^(p-1)$. The ramification index of $P_1$ relative to
  $R$ is $2$, so $P_1$ is tamely ramified over $R$. Thus $S slash R$ is tame,
  and we conclude that $S circle.small G$ is a hereditary $R$-order.
] <exm:prime-cyclotomic-twisted-hereditary-order>

We shall next consider the general problem of classifying all $Lambda$-lattices,
where $Lambda$ is a twisted group ring $S circle.small G$, with $S$ tamely
ramified over $R$. This problem arises frequently in specific cases when we try
to classify integral representations of groups. For example, the results below
will be needed in §@ss:dihedral-metacyclic-integral-representations, where we
consider representations of certain metacyclic groups.

Suppose now that $Lambda=S circle.small G$ is a hereditary $R$-order in the
$K$-algebra $A=L circle.small G$. As in the proof of
@th:maximal-order-ideal-factorization, we know that a left $Lambda$-lattice $M$
is indecomposable if and only if $K M$ is a simple left $A$-module. Apart from
isomorphism, there is a unique simple $A$-module, which may be chosen as the
field $L$ itself, according to the proof of @exm:galois-twisted-group-algebra.
Since every $Lambda$-lattice can be expressed as a finite direct sum of
indecomposable lattices, our first task is to investigate the full
$Lambda$-lattices in $L$.

Let $M$ be a full $Lambda$-lattice in the left $A$-module $L$. Then $M$ is a
fractional $S$-ideal in the field $L$ (see §@ss:dedekind-ideal-theory) such that
$ sigma(M)=M "for every" sigma in G. $
#source(618)
Such ideals are called _ambiguous ideals_#idx("ambiguous ideal")#idx(
  "ideal",
  "ambiguous",
). For example, $S frak(a)$ is an ambiguous ideal for every fractional $R$-ideal
$frak(a)$ in $K$. We may easily decide whether two ambiguous $S$-ideals $M$ and
$N$ are isomorphic as $Lambda$-lattices. Indeed, each
$f in Hom_Lambda lr((M,N))$ extends to an element of $Hom_A lr((L,L))$, and is
therefore given by right multiplication by some $x in K$, including $0$.
Therefore $M tilde.equiv N$ if and only if $M=N x$ for some $x in K^dot$.

We are now ready to determine all ambiguous $S$-ideals $frak(A)$ in $L$. If
$P_1$ is a maximal ideal of $S$ which occurs to the exponent $n$ in $frak(A)$,
then since $sigma(frak(A))=frak(A)$ for all $sigma in G$, it follows that each
of the $R$-conjugates $P_1^sigma$ of $P_1$ must also occur to the exponent $n$.
Given any maximal ideal $P$ of $R$, we may write
$ P S=tau(P)^e,quad "where" tau(P)=P_1 dots.c P_g, $
and the ${P_i}$ are the distinct $R$-conjugates of the maximal ideal $P_1$ of
$S$. The exponent $e=e(P,S slash R)$ is the ramification index of $P$ (in the
extension $L slash K$), and equals $1$ for almost all $P$. Clearly $tau(P)$ is
an ambiguous ideal of $S$, and is the largest ambiguous ideal in $S$ in which
$P_1$ occurs as a factor. It follows at once that every ambiguous $S$-ideal
$frak(A)$ in $L$ is uniquely expressible in the form
$ frak(A)={product_P tau(P)^(k_P)} frak(a)=frak(Q) frak(a),quad "say", $
where $frak(a)$ is an $R$-ideal in $K$, $P$ ranges over the maximal ideals of
$R$ ramified in $S$, and for each $P$, $0<=k_P<=e(P,S slash R)-1$. The
$G$-invariant submodule of $frak(A)$ is given by
$
  frak(A) inter K=frak(a)(frak(Q) inter K)
  =frak(a) dot product_(k_P>0) P=frak(a) psi(frak(Q)),quad "say".
$
Suppose now that the $Lambda$-lattice $M$ is expressed as an external direct sum
$M=product.co_(i=1)^n frak(Q)_i frak(a)_i$, with each $frak(Q)_i frak(a)_i$ as
above. The $G$-invariant submodule of $M$, which is determined up to isomorphism
by the isomorphism class of $M$, is then equal to
$product.co frak(a)_i psi(frak(Q)_i)$, where $psi(frak(Q)_i)$ is defined as
above. Thus, the $R$-isomorphism class of the $R$-lattice
$product.co_(i=1)^n frak(a)_i psi(frak(Q)_i)$ is an invariant of the
$Lambda$-isomorphism class of $M$. Of course, the $R$-lattice
$product.co frak(a)_i psi(frak(Q)_i)$ is determined up to isomorphism by its
rank $n$ and its Steinitz class, namely, the $R$-ideal class of
$product_i frak(a)_i psi(frak(Q)_i)$.

We show next that (with the same notation as above) there is always a
$Lambda$-isomorphism
$
  frak(Q)_i frak(a)_i plus.o frak(Q)_j frak(a)_j
  tilde.equiv frak(Q)_i plus.o frak(Q)_j frak(a)_i frak(a)_j.
$ <eq:ambiguous-ideal-steinitz-transfer>
Thus, in a direct sum $product.co frak(Q)_i frak(a)_i$, we may move the factors
$frak(a)_i$ from one term to another, without affecting the isomorphism class of
the direct sum. In order
#source(619)
to prove @eq:ambiguous-ideal-steinitz-transfer, we note that for each
$x in K^dot$, the $Lambda$-lattices $frak(Q) frak(a)$ and $frak(Q) frak(a)x$ are
isomorphic. We may choose $x$ so that $frak(a)x$ is an ideal of $R$ which is
coprime to each $P in frak(S)$, where $frak(S)$ is the finite set of all maximal
ideals $P$ of $R$ which ramify in $S$ (see
Exercise~@exc:ideal-class-coprime-representative or @bib:CurtisReiner1962[CR
  (18.20)]). Hence in proving @eq:ambiguous-ideal-steinitz-transfer we may
assume that both $frak(a)_i$ and $frak(a)_j$ are ideals of $R$ which are coprime
to each $P in frak(S)$. Therefore
$ (R slash frak(a)_i)_P=0 "for each" P in frak(S), $
<eq:coprime-ideal-local-vanishing>
where the subscript $P$ indicates localization.

Now let $frak(Q)$ be any ambiguous $S$-ideal in $L$, and consider the
$R$-torsion $Lambda$-module $frak(Q) slash frak(a)_i frak(Q)$. By the Primary
Decomposition Theorem @th:primary-decomposition-dedekind, we may express
$frak(Q) slash frak(a)_i frak(Q)$ as a direct sum of its localizations. Further,
the localization at each $P in frak(S)$ is zero, by
@eq:coprime-ideal-local-vanishing. Now let $P in.not frak(S)$, so
$e(P,S slash R)=1$ and $tau(P)=P S$. If $tau(P)$ occurs with exponent $k$ in
$frak(Q)$, then we have $frak(Q)_P=P^k S_P$. Using the fact that
$P^k slash frak(a)_i P^k tilde.equiv R slash frak(a)_i$, as $R$-modules (see
@bib:CurtisReiner1962[CR (18.24)]), we obtain $Lambda$-isomorphisms:
$
  (frak(Q) slash frak(a)_i frak(Q))_P
  &tilde.equiv P^k S_P slash frak(a)_i P^k S_P
  tilde.equiv S_P times.o_R (P^k slash frak(a)_i P^k) \
  &tilde.equiv S_P times.o_R (R slash frak(a)_i)
  tilde.equiv S_P slash frak(a)_i S_P.
$
This shows that the isomorphism class of the $Lambda$-module
$frak(Q) slash frak(a)_i frak(Q)$ is independent of $frak(Q)$. Hence we obtain
$Lambda$-isomorphisms
$
  frak(Q)_j times.o_R (frak(a)_j slash frak(a)_i frak(a)_j)
  tilde.equiv frak(Q)_j times.o_R (R slash frak(a)_i)
  tilde.equiv frak(Q)_i times.o_R (R slash frak(a)_i).
$
We may apply Schanuel's Lemma to the pair of exact sequences of $Lambda$-modules
$
  0 arrow frak(Q)_i frak(a)_i arrow frak(Q)_i
  arrow frak(Q)_i times.o_R (R slash frak(a)_i) arrow 0,
$
$
  0 arrow frak(Q)_j frak(a)_i frak(a)_j arrow frak(Q)_j frak(a)_j
  arrow frak(Q)_j times.o_R (frak(a)_j slash frak(a)_i frak(a)_j) arrow 0,
$
since the $Lambda$-lattices $frak(Q)_i$ and $frak(Q)_j frak(a)_j$ are
$Lambda$-projective. This gives @eq:ambiguous-ideal-steinitz-transfer at once.

Let us illustrate the usefulness of the preceding results in a special case
which arises in classifying integral representations of metacyclic groups (see
§@ss:dihedral-metacyclic-integral-representations). Suppose that there is a
unique maximal ideal $P_0$ of $R$ which ramifies in $S$, and suppose further
that $P_0$ is _completely ramified_#idx("completely ramified") in $S$, that is
$ P_0 S=P^n,quad n=dim_K L=|G|, $
where $P$ now denotes a maximal ideal of $S$. Suppose finally that
$overline(n)!=0$ in $R slash P_0$, so $S$ is tamely ramified over $R$, and
$Lambda=S circle.small G$ is a hereditary $R$-order in the simple $K$-algebra
$A=L circle.small G$. Each ambiguous $S$-ideal $frak(A)$ in $L$ is uniquely
expressible in the form $frak(A)=P^k frak(a)$, where $0<=k<=n-1$ and $frak(a)$
is a fractional
#source(620)
$R$-ideal in $K$. Further
$
  P^k frak(a) tilde.equiv P^l frak(b)
  &arrow.l.r P^k frak(a)=P^l frak(b)x "for some" x in K^dot \
  &arrow.l.r k=l "and" frak(a)=frak(b)x,
$
assuming that $0<=l<=n-1$ and that $frak(b)=R$-ideal in $K$. Hence, a full set
of non-isomorphic indecomposable $Lambda$-lattices is given by
$ {P^k frak(a)_i:0<=k<=n-1,1<=i<=h}, $
where $frak(a)_i$ ranges over a full set of representatives of the $h$ ideal
classes of $R$. (Assume $h$ finite, for simplicity).

We shall now decide when two direct sums of indecomposable $Lambda$-lattices are
isomorphic; the results are due to Rosen @bib:Rosen1963. Let $hat(R)$,
$hat(Lambda)$ and so on, denote $P_0$-adic completions. Since $P_0 S=P^n$, the
$P$-adic completion $hat(S)$ of $S$ coincides with its $P_0$-adic completion.
Clearly,
$
  hat(R) times.o_R P^k frak(a)_i tilde.equiv hat(P)^k hat(frak(a))_i
  tilde.equiv hat(P)^k,
$
since $hat(frak(a))_i$ is an ideal of the d.v.r. $hat(R)$. Now consider a
$Lambda$-lattice
$ M=product.co_(k=0)^(n-1) P^k N_k, $ <eq:ambiguous-lattice-rank-decomposition>
where $N_k$ is an $R$-lattice of $R$-rank $r_k$. Then $hat(N)_k$ is a free
$hat(R)$-lattice of $hat(R)$-rank $r_k$, so we have
$ hat(M) tilde.equiv product.co_(k=0)^(n-1) (hat(P)^k)^((r_k)). $
On the other hand (see §@ss:valuations-completions), $hat(P)_0$ is completely
ramified in the extension $hat(L) slash hat(K)$, and $hat(P)_0 hat(S)=hat(P)^n$,
$n=dim_(hat(K)) hat(L)$. It follows from the preceding paragraph that for $k,l$
distinct, $0<=k,l<=n-1$, the $hat(Lambda)$-modules $hat(P)^k$ and $hat(P)^l$ are
not isomorphic. However, the K-S-A Theorem holds for $hat(Lambda)$-lattices (see
§@ss:krull-schmidt-azumaya). It follows that the integers ${r_0,dots,r_(n-1)}$
are invariants of the isomorphism class of $hat(M)$, and are therefore also
isomorphism invariants of $M$.

Finally, each $R$-lattice $N_k$ is determined (up to isomorphism) by its
$R$-rank $r_k$ and its Steinitz class $[frak(a)_k]$, where $frak(a)_k$ is an
$R$-ideal in $K$. By virtue of @eq:ambiguous-ideal-steinitz-transfer, we can
choose all but one of the $N_k$'s to be a free $R$-module, and can collect all
the $frak(a)_k$'s into a single summand of $M$. Hence (assuming $r_0>=1$ for
simplicity) we have
$
  M tilde.equiv {S dot product_(k=0)^(n-1) frak(a)_k}
  plus.o S^((r_0-1)) plus.o product.co_(k=1)^(n-1) (P^k)^((r_k)).
$
#source(621)
On the other hand, by computing the $G$-invariant submodule of $M$ according to
the earlier part of this discussion, we see that the ideal class of
$product frak(a)_k$ is an isomorphism invariant of $M$. We therefore conclude
that, in the present case, _a full set of isomorphism invariants_ of the
$Lambda$-lattice $M$ given in @eq:ambiguous-lattice-rank-decomposition consists
of
#enum(
  numbering: "(i)",
  [The integers ${r_0,dots,r_(n-1)}$, where $r_k=R$-rank of $N_k$, and],
  [The $R$-ideal class of the product of the Steinitz classes of the
    $R$-lattices $N_0,dots,N_(n-1)$.],
)

We conclude this section with a number of remarks about possible generalizations
and refinements of our results above. By @bib:Reiner1975[MO (40.8)], a given
hereditary order $Lambda$ can be embedded in only finitely many maximal orders,
and the number of such maximal orders is intimately related to the structure of
$Lambda$. We shall see that in some cases, this number can be determined quite
explicitly. Since the problem can always be reduced to the local case (see
@bib:Reiner1975[MO §40]), we begin by assuming that the ground ring $R$ is a
d.v.r., and we recall some definitions from algebraic number theory.

Let $R$ be a d.v.r. with maximal ideal $P$ and residue class field
$overline(R)$. Let ${P_i}$ be the set of maximal ideals of $S$ which contain
$P$, and put $overline(S)=S slash P_1$. We now let
$
  D={sigma in G:sigma(P_1)=P_1},quad
  I={sigma in D:overline(sigma)=1 "on" overline(S)},
$
where $sigma in D$ induces
$overline(sigma) in op("Gal")(overline(S) slash overline(R))$. Then $D$ is the
_decomposition group_#idx("decomposition group") of $P_1$ (relative to $R$), and
$I$ the _inertia group_#idx("inertia group") of $P_1$. It is easily verified
that $D slash I tilde.equiv op("Gal")(overline(S) slash overline(R))$; see Weiss
@bib:Weiss1963, Ch. 4, §10.

Suppose now that $S$ is tamely ramified over the d.v.r. $R$, so
$T_(L slash K) lr((S))=R$, and let $Lambda$ be the twisted group ring
$S circle.small G$. Then $Lambda$ is a hereditary order in $L circle.small G$.
As shown in @bib:Reiner1975[MO §39], there are finitely many maximal orders in
$L circle.small G$ which contain $Lambda$, and $Lambda$ is their intersection.
Further, the number of such maximal orders coincides with the number of maximal
two-sided ideals of $Lambda$, which in turn equals the number of simple
components of the semisimple $overline(R)$-algebra $Lambda slash rad Lambda$.
According to the results of Williamson @bib:Williamson1963, this number is
precisely the order of the inertia group $I$ defined above.

We turn next to the generalization of the concept of a twisted group algebra and
a twisted group ring. As before, let $L$ be a finite Galois extension of $K$
with Galois group $G$, and let $f:G times G arrow L^dot$ be a factor set on $G$
with values in the multiplicative group $L^dot$ of nonzero elements of $L$ (see
@eq:factor-set-condition). We may then form the _crossed-product algebra_#idx(
  "crossed-product algebra",
)
$ A=(L slash K,f)=op("⨁", limits: #true)_(sigma in G) L u_sigma, $
having an $L$-basis consisting of symbols ${u_sigma:sigma in G}$, with
multiplication in $A$ defined by the formulas
$ u_sigma a=sigma(a)u_sigma,quad u_sigma u_tau=f(sigma,tau)u_(sigma tau) $
#source(622)
for all $sigma,tau in G$, $a in L$. The condition that $f$ be a factor set is
precisely the condition that $A$ be an associative algebra. The crossed-product
algebra $A=(L slash K,f)$ has already been encountered in
@exm:crossed-products-twisted-group-algebras. As shown in @bib:Reiner1975[MO
  (29.6)], $A$ is a central simple $K$-algebra with $dim_K A=n^2$, where
$n=|G|=dim_K L$. The $K$-isomorphism class of $A$ depends only upon the
cohomology class of $f$ in $H^2 lr((G,L^dot))$. When $f$ is the trivial factor
set (all of whose values are $1$), the crossed-product algebra $A$ is just a
full matrix algebra $M_n lr((K))$, as we showed in
@exm:galois-twisted-group-algebra.

Now let $S$ be the integral closure of $R$ in $L$, where $R$ is a Dedekind
domain with quotient field $K$. In order to form the analogue of the twisted
group ring $S circle.small G$, we assume that $f:G times G arrow S$ is a factor
set whose values are units in $S$. Then
$ Lambda=op("⨁", limits: #true)_(sigma in G) S u_sigma $
is an $R$-order in the crossed-product algebra $A=(L slash K,f)$. Williamson
@bib:Williamson1963 established the following criterion in the local case (see
also Harada @bib:Harada1964 and Merklen @bib:Merklen1978 for further results);
the trace-one argument below gives the stated Dedekind-domain form.

#theorem[
  All _crossed-product orders_#idx(
    "crossed-product order",
    target: [@th:crossed-product-order-heredity],
  ) defined above, as $f$ ranges over the unit-valued factor sets, are
  hereditary $R$-orders if and only if $T_(L slash K) lr((S))=R$, or
  equivalently, if and only if $S$ is tamely ramified over $R$.#ed-note[
    The original states the equivalence for one fixed factor set. That necessity
    is false. For example, over $R=FF_2(s)[[t]]$, put $pi^2+t pi+t=0$ and
    $Lambda=R[pi]+R[pi]u$, with $u^2=s$ and $u pi=(pi+t)u$. The quadratic
    extension is wild and has trace ideal $t R$, but $rad Lambda=pi Lambda$,
    $(pi Lambda)^2=t Lambda$, and
    $Lambda slash pi Lambda=FF_2(s)[u] slash (u^2-s)$ is a field. Every nonzero
    one-sided ideal is a power of $pi Lambda$, so $Lambda$ is hereditary. The
    corrected quantifier and the proof below are editorial.
  ]
] <th:crossed-product-order-heredity>
#idx("Williamson's Theorem", target: [@th:crossed-product-order-heredity])

#proof[
  Necessity follows by taking the trivial factor set and applying
  @th:twisted-group-ring-heredity. Conversely, choose $s_0 in S$ with
  $T_(L slash K) lr((s_0))=1$. A left ideal $M$ of $Lambda$ is $S$-projective,
  since $S$ is Dedekind. Given a $Lambda$-surjection onto $M$, choose an
  $S$-linear section $psi$ and replace it by
  $ psi'=sum_(sigma in G) u_sigma s_0 psi u_sigma^(-1). $
  Each summand is $S$-linear. Conjugation by any $u_tau$ reindexes the sum; the
  unit cocycle factors cancel because these maps commute with $S$. Hence $psi'$
  is $Lambda$-linear, and its composite with the surjection is multiplication by
  $sum sigma(s_0)=1$. Thus every left ideal is projective. The right-sided
  argument is the same.
]

It is known that a hereditary order $Lambda$ is contained in only finitely many
maximal orders (see @bib:Reiner1975[MO (40.8)]), and it is of interest to
determine all such maximal orders for a given order $Lambda$ of the type
occurring in @th:crossed-product-order-heredity. For related results, see Janusz
@bib:Janusz1980.#idx("Janusz's Theorem") Under the additional hypotheses that
$S$ is tamely ramified over $R$ and that every residue field $R slash P$ is
finite, let $Lambda=plus.o S u_sigma$ be a unit-valued crossed-product order in
$A=(L slash K,f)$. Then the number of maximal $R$-orders in $A$ containing
$Lambda$ is
$ product_P e(P) slash m(P), $
where $P$ ranges over all maximal ideals of $R$. Here $e(P)$ is the ramification
index of any maximal ideal of $S$ above $P$, and $m(P)$ is the index of the
division algebra occurring in the $P$-adic completion of $A$. Both integers are
$1$ for almost all $P$. Maximal overorders can be constructed by choosing a
maximal completed overorder independently at each $P$, descending by
intersection with $A$, and gluing the resulting local lattices.#ed-note[
  The additional hypotheses and the following derivation are editorial. Without
  finite residue fields the count can fail: the unramified crossed product over
  $RR[[t]]$ with coefficients $CC[[t]]$ and cocycle $-1$ is the maximal
  quaternion order, so the count is $1$, while $e=1$, $m=2$. The original final
  formula $O_l lr((J Lambda e))$ is also false, even with the added hypotheses.
  Take $R=ZZ[1 slash 2]$, $alpha^2=-5$, $j^2=-1$, $j alpha=-alpha j$, and
  $Lambda=R[alpha]+R[alpha]j$. The algebra is a division algebra, so its
  primitive idempotent is $1$; every ambiguous ideal $J$ gives an invertible
  two-sided ideal $J Lambda$, whose left order is $Lambda$. Yet the strictly
  larger order with basis $1,j,beta,beta j$, $beta=alpha(2+j) slash 5$, is
  maximal: $beta^2=-1$, $j beta=-beta j$, and its reduced-trace Gram determinant
  is the unit $-16$. Thus the local construction, not the ideal formula,
  supplies a valid description.
]

Here is a derivation of this restricted count and construction. At $P$, write
$C=hat(Lambda)$ and $J=rad C$. The tame residue calculation gives
$J=(rad hat(S))C$ and $J^e=P C$, where $e=e(P)$. This remains valid for
semilocal $hat(S)$, whose factors are permuted transitively by the units
$u_sigma$; passing to a corner gives a full matrix ring over one factor's
crossed product, with no additional counting factor. The hereditary normal form
of @th:local-hereditary-orders-block-form gives a block period $r$, and
$J^r=Pi C$, where $Pi$ is diagonal with the division-order uniformizer in each
block. By @th:division-algebra-maximal-order-valuation(iv), finite residue
fields give $rad(Delta)^m=P Delta$, where $m=m(P)$. Consequently $J^(r m)=P C$.
All successive powers of $J$ are distinct, by Nakayama's Lemma, so $e=r m$. The
normal form has exactly $r=e(P) slash m(P)$ maximal completed overorders. Only
finitely many $P$ ramify, and $e=1$ forces $m=r=1$. Finally,
@prop:localization-completion-lattices and @th:hereditary-orders-localization
glue the independent local choices, giving the displayed product and the stated
construction.
#exercises-heading

#exercise[
  Let $L$ be a f.d. semisimple commutative $K$-algebra, where $K$ is a field,
  and let $G$ be a finite group of $K$-automorphisms of $L$. Suppose that the
  subalgebra of $L$ invariant under $G$ is $K$ itself, and that
  $dim_K L=abs(G)$. Prove that the twisted group algebra $L circle.small G$ is a
  central simple
  #source(623)
  $K$-algebra. (The result was pointed out by Merklen @bib:Merklen1978; for $G$
  cyclic, it is due to Albert @bib:Albert1939, p. 93, Th. 1.)
] <exc:semisimple-galois-twisted-algebra>

#exercise[
  Let $L$ be a Galois extension of $K$ with finite Galois group
  $G={g_1,dots,g_n}$. Let
  $ U(g)=[delta_(g_i,g g_j)]_(1<=i,j<=n),quad g in G, $
  where for $g,h in G$, $delta_(g h)=1$ if $g=h$, and $0$ otherwise (see
  §@sec:induced-modules). For $a in L$, let
  $ a^*=op("diag")(g_1^(-1)a,dots,g_n^(-1)a) in M_n lr((L)). $
  Show that
  $ U(g)a^*=(g a)^* U(g),quad "for all" a in L,g in G. $
  Deduce that the map defined by
  $ a arrow.r a^*,quad g arrow.r U(g), $
  yields an $n$-th degree representation of $L circle.small G$ over the field
  $L$.
] <exc:twisted-galois-matrix-representation>

#exercise[
  Keep the above notation. Show that for $a_i in L$,
  $
    "nr"_((L circle.small G) slash K) lr((sum_(i=1)^n a_i g_i))=det
    lr((sum_(i=1)^n a_i^* U(g_i))).
  $
] <exc:twisted-galois-reduced-norm>

#exercise[
  Prove the following generalization of Maschke's Theorem:#idx(
    "Maschke's Theorem",
    target: [@exc:twisted-group-algebra-separability],
  ) Let $K$ be a field, and $f:G times G arrow K^dot$ a factor set from a finite
  group $G$ into $K^dot$. Let
  $
    A=op("⨁", limits: #true)_(x in G) K u_x,quad "where"
    u_x u_y=f(x,y)u_(x y) "for" x,y in G,
  $
  and where the elements ${u_x}$ commute with those of $K$. Prove that $A$ is a
  separable $K$-algebra if and only if $char K divides.not |G|$.

  #hint([@exc:twisted-group-algebra-separability])[
    (Williamson @bib:Williamson1963, Harada @bib:Harada1964):#idx(
      "Williamson's Theorem",
      target: [@exc:twisted-group-algebra-separability],
    ) The argument works for any commutative ring $K$, and a factor set
    $f:G times G arrow op("u")(K)$. Changing the $K$-basis of $A$, we may assume
    that $f$ is _normalized_#idx("normalized factor set"), that is,
    $ f(x,1)=f(1,x)=1,quad x in G, $
    and therefore $u_1$ is the unity element of $A$. Let $times.o$ be
    $times.o_K$, and let $A^e=A times.o A^circle.small$, where $A^circle.small$
    is the opposite ring of $A$. Then (see @bib:Reiner1975[MO, Exercise 7.9])
    $A$ is $K$-separable if and only if $A$ is projective as left $A^e$-module.
    Let $mu$ be the $A^e$-surjection given by
    $
      mu:A times.o A^circle.small arrow A,quad mu(a times.o b^circle.small)=a
      b "for" a,b in A.
    $
    Then $A$ is $A^e$-projective if and only if there exists a left
    $A^e$-homomorphism $nu:A arrow A^e$ which splits $mu$.
    #source(624)
    If $|G| in op("u")(K)$, the desired map $nu$ is given by
    $ nu(a)=|G|^(-1) sum_(x in G) a u_x times.o u_x^(-1),quad a in A. $
    Conversely, if $nu$ splits $mu$, set
    $
      nu(1)=sum_(x,y in G) alpha_(x,y)(u_x times.o u_y) in A^e,quad
      alpha_(x,y) in K.
    $
    Then
    $
      1=mu nu(1)=sum_(x in G) alpha_(x,x^(-1))f(x,x^(-1))
      =|G| alpha_(1 1),
    $
    since the condition
    $ (u_z times.o 1)nu(1)=nu(u_z)=(1 times.o u_z)nu(1) "for" z in G $
    implies that $alpha_(x,x^(-1))f(x,x^(-1))=alpha_(1 1)$ for all $x in G$.
  ]
] <exc:twisted-group-algebra-separability>

#exercise[
  Let $R$ be a d.v.r. with maximal ideal $P$ and residue class field
  $overline(R)$. Let $Lambda=S circle.small G$ be a twisted group ring as in
  @exm:galois-twisted-group-algebra, and set
  $ P S=(P_1 dots.c P_g)^e,quad J=P_1 dots.c P_g, $
  where the ${P_i}$ are the distinct $G$-conjugates of the maximal ideal $P_1$
  of $S$. Let $hat(Lambda)$ denote the $P$-adic completion of $Lambda$. Assume
  that $|G|$ is a unit in $R$, and that each $S slash P_i$ is a separable
  extension of $overline(R)$. Prove that
  $ rad Lambda=J Lambda,quad rad hat(Lambda)=J hat(Lambda). $

  #hint([@exc:twisted-group-ring-radical])[
    (Williamson @bib:Williamson1963; this proof was supplied to the authors by
    Janusz):#idx(
      "Williamson's Theorem",
      target: [@exc:twisted-group-ring-radical],
    ) Since $sigma(J)=J$ for all $sigma in G$, $J Lambda$ is a two-sided ideal
    of $Lambda$. Further, $(J Lambda)^e=P Lambda subset.eq rad Lambda$, so
    $J Lambda subset.eq rad Lambda$. Put
    $
      overline(Lambda)=Lambda slash J Lambda=op("⨁", limits: #true)_(sigma in
      G) (S slash J)u_sigma,
    $
    with $G$ acting as a group of automorphisms of $S slash J$. But
    $
      S slash J tilde.equiv product_(i=1)^g overline(S)_i,quad "where"
      overline(S)_i=S slash P_i.
    $
    If $phi_i:S arrow overline(S)_i$ is the natural surjection, and $T$ is the
    ordinary trace from $overline(Lambda)$ to $overline(R)$, then for $s in S$
    and $sigma in G$ we have
    $
      T lr((overline(s)u_sigma))=cases(
        |G| dot sum_(i=1)^g T_i lr((phi_i s)) & quad sigma=1,
        0 & quad sigma!=1.
      )
    $
    Here, $T_i$ is the trace from $overline(S)_i$ to $overline(R)$. Then
    $T:overline(Lambda) times overline(Lambda) arrow overline(R)$ is a
    nondegenerate trace form, so $overline(Lambda)$ is a semisimple
    $overline(R)$-algebra, and $rad Lambda=J Lambda$. Now use
    Exercise~@exc:radical-completion to find $rad hat(Lambda)$.
  ]
] <exc:twisted-group-ring-radical>

#exercise[
  Prove Artin's Theorem (see Exercise~@exc:artin-embeddings-independent) by
  using @exm:galois-twisted-group-algebra.
] <exc:artin-theorem-twisted-algebra>
#idx("Artin's Theorem", target: [@exc:artin-theorem-twisted-algebra])
