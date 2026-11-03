#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/37-bass-gorenstein.typ": *

== Bass and Gorenstein Orders <sec:bass-gorenstein-orders>

#source(798)
Throughout this section, let $A$ be a f.d. separable $K$-algebra, and $R$ a
Dedekind domain with quotient field $K$. An $R$-order $Lambda$ in $A$ is called
a _Gorenstein order_#idx("Gorenstein orders")#idx("order", "Gorenstein") if
every $Lambda$-exact sequence:
$ 0 -> Lambda -> M -> N -> 0, $
in which $M$ and $N$ are $Lambda$-lattices, is necessarily split over $Lambda$.
If $Lambda$ has the additional property that every $R$-order in $A$ containing
$Lambda$ is also a Gorenstein order, we call $Lambda$ a _Bass order_. #idx(
  "Bass orders",
)#idx("order", "Bass") It is easily verified that there are inclusions
$
  {"maximal orders"} subset.eq {"hereditary orders"}
  subset.eq {"Bass orders"} subset.eq {"Gorenstein orders"}.
$
Examples show that each inclusion is proper, generally speaking. Bass orders are
a fundamental tool in the Drozd-Roiter and Drozd-Kirichenko approaches to the
characterization of orders of finite representation type (see
§@sec:finite-representation-type).

We shall consider the following properties#footnote[As usual,
  $mu_Lambda lr((X))$ denotes the minimal number of generators of a f.g.
  $Lambda$-module $X$.] of an $R$-order $Lambda$:
$ P_1:mu_Lambda lr((I)) <= 2 "for every left ideal" I "of" Lambda. $
$ P_2:Lambda "is a Bass order". $
$
  P_3:"Every indecomposable" Lambda "-lattice is isomorphic to an ideal of"
  Lambda.
$
The main results of this section are the implications
$ P_1 => P_2 => P_3. $
In general, $P_3$ does not imply $P_1$. For example, every hereditary order is a
Bass order (see below). However, by
Exercise~@exc:hereditary-order-ideal-generators, one can find an ideal $I$ in a
suitable hereditary order $Lambda$, for which $mu_Lambda lr((I))>2$. Even for
commutative orders, $P_3$ need not imply $P_1$. As an example, we may take
$Lambda=R G$ where $G$ is cyclic of order $4$ and $R=hat(ZZ)_2$. Then $P_3$
holds for $Lambda$ by §@ss:cyclic-p-squared-lattices, but
$mu_Lambda lr((4 Lambda'))=3$ where $Lambda'$ is the maximal $R$-order
containing $Lambda$.

The final major result of this section is the following theorem due to Bass,
which was historically the starting point of the development of the material in
this section:
#idx("Bass' Theorem")

_Let $Lambda$ be a commutative noetherian integral domain such that every f.g.
indecomposable torsionfree $Lambda$-module is isomorphic to an ideal of
$Lambda$. Then $mu_Lambda lr((I)) <= 2$ for every ideal $I$ of $Lambda$, so
$P_1$ is equivalent to $P_3$ in this case._

#source(799)Now let $A$ be a f.d. separable $K$-algebra. Given a f.g. left
$A$-module $V$, set $B=(End_A V)^circle$ and view $V$ as $(A,B)$-bimodule. Set
$ V^*=Hom_K lr((V,K))=(B,A)"-bimodule", $
the _dual_ of $V$.#idx("dual of module") Since $A$ is a separable $K$-algebra,
it is also a Frobenius algebra over $K$ by
@prop:eilenberg-nakayama-symmetric-semisimple, so
$(attach(A, br: A))^* tilde.equiv attach(A, bl: A)$. Thus
$
  V^* tilde.equiv Hom_K lr((A times.o_A V,K))
  tilde.equiv Hom_A lr((V,Hom_K lr((attach(A, bl: A),K))))
  tilde.equiv Hom_A lr((V,A))
$ <eq:separable-module-dual-hom>
as $(B,A)$-bimodules, using the Adjointness Theorem~@th:hom-tensor-adjointness.

Now let $V$ be a faithful left $A$-module; then $V$ is a progenerator for
$attach(frak(M), bl: A)$ (and also for $attach(frak(M), br: B)$), and there are
bimodule isomorphisms
$ V^* times.o_A V tilde.equiv B,quad V times.o_B V^* tilde.equiv A, $
<eq:faithful-semisimple-dual-morita>
by virtue of @eq:separable-module-dual-hom and §@ss:morita-theorems.

Assuming still that $V$ is faithful, let $M$ be a full $R$-lattice in $V$, and
define its _left order_ $O_l lr((M))$ and _right order_ $O_r lr((M))$ by #idx(
  "left order",
)#idx("right order")#idx("order", "left")#idx("order", "right")
$
  O_l lr((M))={x in A:x M subset.eq M},
  quad O_r lr((M))={y in B:M y subset.eq M}.
$
Then $O_l lr((M))$ is an $R$-order in $A$, and $O_r lr((M))$ in $B$. These
definitions generalize those given in §@sec:jordan-zassenhaus. Suppose further
that $N$ is a full $R$-lattice in $V^*$, so $O_l lr((N))$ is an $R$-order in
$B$, and $O_r lr((N))$ in $A$. If we set
$
  Lambda=O_r lr((N)) inter O_l lr((M)) subset.eq A,
  quad Gamma=O_l lr((N)) inter O_r lr((M)) subset.eq B,
$
then $Lambda$ and $Gamma$ are orders in $A$ and $B$, respectively. There are
well-defined bimodule homomorphisms
$ N times.o_Lambda M -> B,quad M times.o_Gamma N -> A, $
<eq:lattice-dual-pairing-maps>
consistent with the maps given in @eq:faithful-semisimple-dual-morita. We claim
that there are bimodule isomorphisms
$
  (N times.o_Lambda M)^* tilde.equiv Hom_Lambda lr((N,M^*)),
  quad (M times.o_Gamma N)^* tilde.equiv Hom_Gamma lr((M,N^*)),
$ <eq:lattice-tensor-dual-adjointness>
where $M^*=Hom_R lr((M,R))$ is the _dual_ of $M$.#idx("dual of lattice") Indeed,
we have
$
  (N times.o_Lambda M)^*=Hom_R lr((N times.o_Lambda M,R))
  tilde.equiv Hom_Lambda lr((N,Hom_R lr((M,R))))=Hom_Lambda lr((N,M^*)),
$
and likewise for the other isomorphism in @eq:lattice-tensor-dual-adjointness.

We caution the reader that the maps in @eq:lattice-dual-pairing-maps need not be
monomorphisms (see Exercise~@exc:overorder-tensor-tor-kernel), but their kernels
are $R$-torsion modules, since
#source(800)
$K times.o_R (N times.o_Lambda M) tilde.equiv K N times.o_A K M tilde.equiv B$.
Let $N M$ denote the image of $N times.o M$ in $B$, so the kernel of the map
$N times.o M -> N M$ is an $R$-torsion module. We then have
$
  (N times.o M)^*=Hom_R lr((N times.o M,R))=Hom_R lr((N M,R))=(N M)^*,
$
so @eq:lattice-tensor-dual-adjointness yields
$
  (N M)^* tilde.equiv Hom_Lambda lr((N,M^*)),
  quad (M N)^* tilde.equiv Hom_Gamma lr((M,N^*)).
$ <eq:lattice-pairing-image-duals>
We note that all of the isomorphisms occurring above are natural ones.

Now let $Lambda$ be any $R$-order in $A$, and let $M$ be a left
$Lambda$-lattice; its dual $M^*$ is then a right $Lambda$-lattice, and we have
$M tilde.equiv M^(**)$ as left $Lambda$-lattices (see @lem:lattice-duals), the
isomorphism being natural. Each exact sequence of $Lambda$-lattices
$ 0 -> L -> M -> N -> 0 $ <eq:lattice-exact-sequence-duality>
is $R$-split, hence yields a new exact sequence
$ 0 -> N^* -> M^* -> L^* -> 0 $ <eq:dual-lattice-exact-sequence>
when we apply $Hom_R lr((dot,R))$. Conversely, this second sequence of right
$Lambda$-lattices dualizes to give the original sequence. It follows that the
first sequence is $Lambda$-split if and only if the second sequence is
$Lambda$-split.

We call a left $Lambda$-lattice $L$ _weakly injective_#idx("weakly injective")
if every exact sequence @eq:lattice-exact-sequence-duality of left
$Lambda$-lattices is split over $Lambda$. Then $L$ is weakly injective if and
only if its dual $L^*$ is a projective right $Lambda$-lattice. Equivalently, $L$
is weakly injective if and only if $op("Ext")_Lambda^1 lr((N,L))=0$ for every
left $Lambda$-lattice $N$. It is obvious that weak injectivity is a local
property, that is, $L$ is weakly injective if and only if each localization
$L_P$ (or completion $hat(L)_P$) is weakly injective, where $P$ ranges over the
maximal ideals of $R$.

If $Lambda$ is a hereditary order, then every $Lambda$-lattice is projective,
and consequently every $Lambda$-lattice is weakly injective.

An arbitrary order $Lambda$ is called _weakly self-injective_#idx(
  "weakly self-injective",
) if $attach(Lambda, bl: Lambda)$ is weakly injective; such orders are also
called (left) _Gorenstein orders_.#idx("Gorenstein orders")#idx(
  "order",
  "Gorenstein",
) Thus $Lambda$ is left Gorenstein if and only if each exact sequence of
$Lambda$-lattices $0 -> Lambda -> M -> N -> 0$ is necessarily split over
$Lambda$, or equivalently, if and only if $(attach(Lambda, bl: Lambda))^*$ is
projective as right $Lambda$-lattice. By
@lem:morita-finite-projective-evaluation, this latter condition holds if and
only if the map
$ Lambda times.o_Lambda Hom(Lambda^*, Lambda) -> End_Lambda lr((Lambda^*)) $
is surjective. It follows at once that the property of being a Gorenstein order
is a local property.

It is obvious that every hereditary order is a Gorenstein order. Our next step
is to remove the asymmetry in our definition of Gorenstein orders:

#proposition[
  An $R$-order $Lambda$ is left Gorenstein if and only if it is right
  Gorenstein.
] <prop:gorenstein-left-right-symmetry>

#source(801)
#proof[
  It suffices to treat the case where $R$ is a complete d.v.r. Assume $Lambda$
  is left Gorenstein, so $(attach(Lambda, bl: Lambda))^*$ is projective. Let
  ${e_i}_(i=1)^n$ be a basic set of primitive idempotents in $Lambda$; then by
  §@sec:idempotents-krull-schmidt-projective-covers there are precisely $n$
  non-isomorphic indecomposable projective left $Lambda$-lattices ${Lambda e_i}$
  and right $Lambda$-lattices ${e_i Lambda}$. Since
  $(attach(Lambda, bl: Lambda))^*$ is a direct sum of copies of some of the
  ${e_i Lambda}$, it follows that $attach(Lambda, bl: Lambda)$ is a sum of their
  duals ${(e_i Lambda)^*}$. Thus the modules ${(e_i Lambda)^*:1 <= i <= n}$ are
  a permutation of the modules ${Lambda e_i:1 <= i <= n}$. But then
  $(attach(Lambda, br: Lambda))^*$ is a sum of modules ${(e_i Lambda)^*}$, and
  is therefore projective as left $Lambda$-lattice. Therefore $Lambda$ is right
  Gorenstein, as desired.
]

From now on, we omit the adjectives “left” and “right” in referring to
Gorenstein orders. Let us give some examples of Gorenstein orders:
#enum(
  numbering: "(i)",
  [If $G$ is a finite group, its integral group ring $R G$ is a Gorenstein order
    by @cor:group-ring-self-contragredient.],
  [Every hereditary order is Gorenstein.],
  [Let $R$ be a complete d.v.r. with maximal ideal $P$, and let
    $
      Lambda=mat(R, R; P^2, R)
      ={mat(a, b; c, d):a,b,d in R,c in P^2}.
    $
    Let $e_1=mat(1, 0; 0, 0)$, $e_2=mat(0, 0; 0, 1)$, so
    $ Lambda e_1=mat(R; P^2),quad Lambda e_2=mat(R; R). $
    Then
    $ (Lambda e_1)^*=Hom_R lr((Lambda e_1,R)) tilde.equiv mat(R, P^(-2)) $
    as right $Lambda$-modules, with the isomorphism arising from the formula
    $ mat(R, P^(-2)) mat(R; P^2)=R. $
    But $mat(R, P^(-2)) tilde.equiv mat(P^2, R) tilde.equiv e_2 Lambda$, so
    $(Lambda e_1)^*$ is right $Lambda$-projective. Likewise so is
    $(Lambda e_2)^*$, and $Lambda$ is a Gorenstein order.],
)

As a consequence of the proof of @prop:gorenstein-left-right-symmetry, we have

#corollary[
  An $R$-order $Lambda$ is Gorenstein if and only if
  $(attach(Lambda, br: Lambda))^*$ is a generator for the category
  $attach(frak(M), bl: Lambda)$.
] <cor:gorenstein-dual-generator>

#proof[
  It suffices to prove the result when $R$ is a complete d.v.r. If $Lambda$ is
  Gorenstein, we have just shown that the ${(e_i Lambda)^*}$ are a rearrangement
  of the
  #source(802)
  ${Lambda e_i}$, using the notation of the proof of
  @prop:gorenstein-left-right-symmetry. But then each $Lambda e_i$ is a summand
  of $(attach(Lambda, br: Lambda))^*$, so $(attach(Lambda, br: Lambda))^*$ is a
  generator for $attach(frak(M), bl: Lambda)$. The argument works equally well
  in reverse: if $(attach(Lambda, br: Lambda))^*$ is a generator, then each
  $Lambda e_i$ is a summand of $(attach(Lambda, br: Lambda))^*$, so the
  ${Lambda e_i}$ are a permutation of the ${(e_i Lambda)^*}$. Hence each
  $(Lambda e_i)^*$ is projective, and therefore so is
  $(attach(Lambda, bl: Lambda))^*$.
]

By @lem:morita-generator-evaluation, the condition that
$(attach(Lambda, br: Lambda))^*$ be a generator for
$attach(frak(M), bl: Lambda)$ can be restated as follows: if
$L=(attach(Lambda, br: Lambda))^*$, the map
$ L times.o_Gamma Hom_Lambda lr((L,Lambda)) -> Lambda $
should be surjective, where $Gamma=End_Lambda lr((L))$. This leads us to the
concept introduced by Roiter~@bib:Roiter1963a, @bib:Roiter1963b,
@bib:Roiter1965, of one module “covering” another.

For the moment, let $Lambda$ be any left noetherian ring, and let us restrict
our attention to f.g. left $Lambda$-modules. For two such modules $L$ and $M$,
we introduce the notation #equation-suffix(
  base: [@cor:gorenstein-dual-generator],
  suffix: "a",
)[
  $ L dot Hom_Lambda lr((L,M))=sum_f f(L), $
] <eq:module-cover-trace>
where $f$ ranges over all elements of $Hom_Lambda lr((L,M))$. Then
$L dot Hom_Lambda lr((L,M))$ is a left $Lambda$-submodule of $M$. We shall say
that $L$ _covers_ $M$, and write $L succ M$,#idx("cover >") if
$L dot Hom_Lambda lr((L,M))=M$. (Roiter uses the term “divides”, rather than
“covers”, and writes $L divides M$. This notation conflicts with our standard
notation $X divides Y$ indicating that $X$ is a direct summand of $Y$, so we
shall not use Roiter's terminology here.)

#lemma[
  #enum(
    numbering: "(i)",
    [$L$ covers every direct summand of each homomorphic image of $L$.],
    [$succ$ is transitive.],
    [$Lambda succ M$ for all (f.g.) $M$.],
    [For f.g. left $Lambda$-modules $L$ and $M$, where $Lambda$ is left
      noetherian, $L succ M$ if and only if there is a surjection $L^((n)) -> M$
      for some $n$.],
  )
] <lem:module-cover-properties>

#proof[
  (i) and (ii) are clear. For (iv), let $phi:L^((n)) -> M$ be a surjection, and
  let $f_i$ be the restriction of $phi$ to the $i$-th summand. Then
  $sum f_i lr((L))=M$, so $L succ M$. Conversely, if $L succ M$, and
  $M=sum_(i=1)^k Lambda m_i$, write each generator as a finite sum
  $m_i=sum_j f_(i j) lr((l_(i j)))$, where $f_(i j) in Hom_Lambda lr((L,M))$ and
  $l_(i j) in L$. Collecting these finitely many maps gives a surjection from a
  finite direct sum of copies of $L$ onto $M$. Finally, (iv) implies (iii).
]

We remark also that the property of one module covering another is a local
property. Further, @cor:gorenstein-dual-generator gives:

#source(803)
#claim[
  $Lambda$ is a Gorenstein $R$-order if and only if
  $(attach(Lambda, br: Lambda))^* succ attach(Lambda, bl: Lambda)$.
] <prop:gorenstein-dual-cover-criterion>

The following useful result is due to Faddeev~@bib:Faddeev1965a:

#proposition[
  Let $Lambda$ be an $R$-order, and let $M$ be a faithful left $Lambda$-lattice,
  where $Lambda=O_l lr((M))$. Then $M^* succ Lambda^*$ as right
  $Lambda$-lattices, and $M succ Lambda^*$ as left $Lambda$-lattices.
] <prop:faithful-lattice-covers-order-dual>

#proof[
  Set $V=K M$, $A=K Lambda$, so $V$ is a faithful left $A$-module and
  $Lambda={x in A:x M subset.eq M}$. Put $Delta=(End_Lambda M)^circle$, and let
  $P=M dot M^*$ be the image of the evaluation pairing.#ed-note[
    The printed tensor isomorphism can have a torsion kernel. For $R=QQ[[pi]]$,
    $K=QQ((pi))$, $A=K[t] slash (t^4-pi)$, take
    $Lambda=R 1+R pi t+R pi t^2+R pi t^3$ and $M=R 1+R t+R pi t^2+R pi t^3$.
    Then $Delta=Lambda$ and $M^*=c M$, where $c=t slash (4 pi^2)$. The element
    $1 times.o c t-t times.o c$ has zero product but is nonzero: modulo
    $rad Lambda$, the classes $1,t$ in $M$ and $c,c t$ in $M^*$ give its nonzero
    antisymmetric tensor. The product image, rather than the integral tensor,
    suffices for the proof.
  ] By @eq:lattice-pairing-image-duals,
  $ P^* tilde.equiv Hom_Delta lr((M,M))=Lambda. $
  Reflexivity therefore gives $P tilde.equiv Lambda^*$ as bimodules, and
  evaluation gives a surjection $M times.o_Delta M^* -> P$. Finite right
  $Delta$-generators of $M$ yield a surjection from finitely many copies of
  $M^*$ onto the right $Lambda$-lattice $P$. Similarly, finite left
  $Delta$-generators of $M^*$ yield a surjection from finitely many copies of
  $M$ onto the left $Lambda$-lattice $P$. Thus both covering assertions follow
  without any assertion that the integral tensor map is injective.
]

As an application of this proposition, we obtain:

#theorem[
  Let $Lambda$ be a Gorenstein $R$-order, where $R$ is a complete d.v.r. Then
  every nonprojective indecomposable left $Lambda$-lattice $M$ is a lattice
  relative to some strictly larger $R$-order in $K Lambda$.
] <th:gorenstein-nonprojective-lattice-overorder>

#proof[
  Suppose first that $M$ is a faithful indecomposable $Lambda$-lattice which is
  not a lattice relative to any larger order in $K Lambda$. Then
  $Lambda=O_l lr((M))$, so by @prop:faithful-lattice-covers-order-dual we have
  $M succ Lambda^*$ as left $Lambda$-lattices. But $Lambda^* succ Lambda$ since
  $Lambda$ is a Gorenstein order, and therefore we deduce that $M succ Lambda$.
  But then $Lambda divides M^((k))$ for some $k$, and so
  $Lambda tilde.equiv M^((l))$ for some $l$, since $M$ is indecomposable.
  However, this gives $M divides Lambda$, so $M$ is projective.

  Now let $M$ be any nonprojective indecomposable $Lambda$-lattice, not
  necessarily faithful. We may write $op("ann")_A K M=A e$, with $e in A$ a
  central idempotent. Then $M=(1-e)M$. If $e in.not Lambda$, the split order
  $e Lambda plus.o (1-e)Lambda$ already properly contains $Lambda$ and acts on
  $M$. If $e in Lambda$, however, $Lambda$ is the direct product of $e Lambda$
  and $(1-e)Lambda$. Both factors are Gorenstein, and projectivity of $M$ over
  $(1-e)Lambda$ is equivalent to projectivity over $Lambda$. Thus the faithful
  argument applies to this factor and gives an order $Gamma$ properly containing
  $(1-e)Lambda$ which acts on $M$. Adjoining $e Lambda$ gives the required
  strict overorder of $Lambda$. This completes the proof.
]

The preceding theorem begins to suggest the importance of Gorenstein orders. If
$Lambda$ is a Gorenstein order over a complete d.v.r. $R$, then the
indecomposable $Lambda$-lattices consist of the indecomposable projectives,
together with the indecomposable $Lambda'$-lattices, where $Lambda'$ ranges over
orders properly containing $Lambda$. Usually, the larger the order, the easier
it is to describe lattices relative to it.

#source(804)
We have already pointed out that every hereditary order $Lambda$ is a Gorenstein
order. Further, if $Lambda$ is a hereditary order in $A$, then so is every
larger order $Lambda'$ in $A$. Indeed, every $Lambda'$-lattice is also a
$Lambda$-lattice. Therefore, every short exact sequence of $Lambda'$-lattices is
$Lambda$-split, and hence also $Lambda'$-split by
Exercise~@exc:overorder-lattice-homomorphisms. In the following discussion, a
special role is played by those Gorenstein orders for which every larger order
is also a Gorenstein order. These orders are called _Bass orders_,#idx(
  "Bass orders",
)#idx("order", "Bass") since their basic properties were first studied by
Bass~@bib:Bass1962, @bib:Bass1963 in the commutative case. As we mentioned in
the introduction, there are inclusions
$
  {"maximal orders"} subset.eq {"hereditary orders"}
  subset.eq {"Bass orders"} subset.eq {"Gorenstein orders"},
$
and examples show each inclusion is proper.

Our first aim is to establish the implication $P_2 => P_3$, that is, every
indecomposable lattice over a Bass order $Lambda$ is isomorphic to an ideal of
$Lambda$. We begin with an easy result:

#lemma[
  Let $Lambda$ be an $R$-order in $A$. Then $Lambda$ is a Bass order if and only
  if for all left $Lambda$-lattices $L$ and $M$,
  $ L succ M "implies" L^* succ M^*. $
] <lem:bass-dual-cover-criterion>

#proof[
  Suppose the condition satisfied, and let $Lambda subset.eq Gamma subset.eq A$,
  where $Gamma$ is an $R$-order. Then $Gamma succ Gamma^*$ as $Gamma$-lattices,
  hence also as $Lambda$-lattices. But then $Gamma^* succ Gamma$, so $Gamma$ is
  Gorenstein.

  For the converse, it suffices to treat the case where $R$ is a complete
  d.v.r., since the property of being a Bass order is a local property, as is
  the property of covering. Thus let $Lambda$ be a Bass order, and let
  $L succ M$, that is, $L dot Hom_Lambda lr((L,M))=M$. Write
  $op("ann")_A K L=A e$, where $e$ is either a central idempotent of $A$ or else
  $e=0$. Then $K L$ is a faithful $(1-e)A$-module, and we put
  $ Gamma=O_l lr((L))={a in (1-e)A:a L subset.eq L}, $
  an $R$-order in $(1-e)A$. Then $Lambda subset.eq (1-e)Lambda plus.o e Lambda
  // Continue the same inclusion chain.
  subset.eq Gamma plus.o e Lambda$, and $Gamma plus.o e Lambda$ is an $R$-order
  in $A$. Since $Lambda$ is a Bass order, this means that
  $Gamma plus.o e Lambda$ is a Gorenstein order, whence so is $Gamma$. But then
  by @prop:gorenstein-dual-cover-criterion and
  @prop:faithful-lattice-covers-order-dual, $L^* succ Gamma^* succ Gamma$. But
  $M$ is a $Gamma$-module since $M=L dot Hom_Lambda lr((L,M))$ and $L$ is a
  $Gamma$-module (see Exercise~@exc:cover-descends-overorder-action). Then $M^*$
  is also a $Gamma$-module, so $Gamma succ M^*$. Therefore $L^* succ M^*$, which
  completes the proof.
]

We intend to prove that every indecomposable lattice over a Bass order $Lambda$
is isomorphic to an ideal of $Lambda$. Unfortunately, this is not a local
property, so we must in fact prove a slightly stronger property which is local.
Some
#source(805)
additional notation is required: let ${S_1,dots,S_r}$ be a basic set of simple
left $A$-modules. For any left $Lambda$-lattice $M$, its _signature_ is defined
by#idx("signature")
$
  op("sig") M={m_1,dots,m_r},quad "where"
  // The generic decomposition determines the signature.
  K M tilde.equiv product.co S_i^((m_i)).
$
Put
$
  op("sig") Lambda={a_1,dots,a_r},quad "where"
  // The regular module fixes the comparison multiplicities.
  A tilde.equiv product.co S_i^((a_i)).
$
Now let
$ I(M)=product.co S_i^min(m_i, a_i), $ <eq:lattice-signature-ideal>
so $I(M)$ is a left ideal of $A$ which depends only on $K M$, and is nonzero if
$M != 0$. It is easily verified (Exercise~@exc:signature-ideal-completion) that
for each $P$, $I(hat(M)_P)$ is the $P$-adic completion of $I(M)$.

We are now ready to prove the fundamental result due to
Drozd-Kirichenko-Roiter~@bib:Drozd1967b, generalizing earlier work of
Bass~@bib:Bass1963:

#theorem[
  Let $Lambda$ be a Bass $R$-order in a separable $K$-algebra $A$, and let $M$
  be any left $Lambda$-lattice. Then there is a $Lambda$-decomposition
  $M=M_0 plus.o M'$, where $K M_0=I(M)$. Thus, $M_0$ is isomorphic to a left
  ideal of $Lambda$.
  #idx("Bass' Theorem", target: [@th:bass-signature-ideal-summand])
  #idx(
    "Drozd-Kirichenko-Roiter Theorem",
    target: [@th:bass-signature-ideal-summand],
  )
] <th:bass-signature-ideal-summand>

#proof[
  _Step 1._ We show first that the existence of such a decomposition of $M$ is a
  local property. Let $P$ range over the maximal ideals of $R$, and suppose that
  for each $P$ we have
  $ hat(M)_P=L(P) plus.o N(P),quad "where" hat(K)_P dot L(P)=I(hat(M)_P). $
  Since $I(hat(M)_P)$ is the completion of $I(M)$, it follows from
  @prop:localization-completion-lattices and @cor:localized-lattice-finite-model
  that there exists a left $Lambda$-lattice $L$ such that
  $hat(L)_P tilde.equiv L(P)$ for each $P$ at which $hat(Lambda)_P$ is not a
  maximal order. By @th:genus-local-direct-summand there exists a
  $Lambda$-lattice $M_0$ in the genus of $L$, such that $M_0 divides M$. Clearly
  $K M_0=I(M)$, since this holds at some $P$.

  _Step 2._ By virtue of Step 1, we may assume from now on that $R$ is a
  complete d.v.r., and attempt to prove the theorem for this case. Let $L$ and
  $M$ be left $Lambda$-lattices; we call $L$ “$M$-injective” if given any
  diagram
  #relative-injectivity-diagram()
  in which $M_1$ is a sublattice of $M$ such that $M slash M_1$ is also a
  lattice, there exists a homomorphism $g:M -> L$ extending $f$. Thus, for
  example, every weakly
  #source(806)
  injective $Lambda$-lattice is $M$-injective for all $M$ (see
  Exercise~@exc:weak-injectivity-extension). We establish the following lemma,
  which is the key step in our induction argument:

  #lemma(numbered: false)[
    Let $Lambda$ be a Bass $R$-order, where $R$ is complete. Let $L$ and $M$ be
    left $Lambda$-lattices such that $Hom_Lambda lr((M,L)) != 0$, and suppose
    that $L$ is $M^((k))$-injective for each $k$. Set $op("sig") M={m_i}$,
    $op("sig") L={l_i}$. Define#footnote[See @eq:module-cover-trace.]
    $Q=M dot Hom_Lambda lr((M,L))$, a $Lambda$-sublattice of $L$ with signature
    ${q_i}$, where
    $ q_i=cases(l_i & "if" m_i != 0, 0 & "if" m_i=0). $
    Then there exist $Lambda$-decompositions
    $ M=I plus.o M_1,quad Q=I plus.o L_1, $
    where $I != 0$ and where $L_1$ is $M_1^((k))$-injective for each $k$.
  ] <lem:bass-relative-injective-common-summand>

  #proof[
    We note first that $Q != 0$ because $Hom_Lambda lr((M,L)) != 0$. The formula
    for $op("sig") Q$ follows at once from the equality
    $K Q=K M dot Hom_A lr((K M,K L))$. Next, the hint in
    Exercise~@exc:trace-relative-injectivity shows that $Q$ is
    $M^((k))$-injective for each $k$. By definition of $Q$ we have $M succ Q$,
    so $M^* succ Q^*$ by @lem:bass-dual-cover-criterion. By
    @lem:module-cover-properties, there exists an exact sequence of right
    $Lambda$-lattices
    $ 0 -> T -> M^(* (k)) -> Q^* -> 0 $
    for some $k$. Taking duals, we obtain an exact sequence of left
    $Lambda$-lattices
    $ 0 -> Q arrow.r^f M^((k)) -> T^* -> 0. $
    But since $Q$ is $M^((k))$-injective, the identity map on $Q$ extends to a
    map $g:M^((k)) -> Q$, so $g$ splits $f$, and therefore $Q divides M^((k))$.
    Therefore $Q$ and $M$ have a common nonzero summand $I$, so we may write
    $M=I plus.o M_1$, $Q=I plus.o L_1$ for some $Lambda$-lattices $M_1$ and
    $L_1$. Finally, by Exercise~@exc:relative-injectivity-common-summand, $L_1$
    is $M_1^((k))$-injective for all $k$, which completes the proof of the
    lemma.
  ]

  _Step 3._ We are now ready to prove the theorem. Given a (nonzero) left
  $Lambda$-lattice $M$, put $Q=M dot Hom_Lambda lr((M,Lambda^*))$. Since
  $Lambda^*$ is weakly injective because $Lambda$ is a Bass order, it follows
  from Step 2 that there exist decompositions
  $ M=I_1 plus.o M_1,quad Q=I_1 plus.o Q_1, $
  where $I_1 != 0$, $Q_1$ is $M_1^((k))$-injective for each $k$, and
  $op("sig") Q={q_i}$, where
  $ q_i=cases(a_i & "if" m_i != 0, 0 & "if" m_i=0). $
  #source(807)
  If $op("sig") I_1={beta_i}$, then
  $ op("sig") M_1={m_i-beta_i},quad op("sig") Q_1={q_i-beta_i}. $
  We now repeat the procedure with the pair $M_1,Q_1$ in place of $M,Lambda^*$.
  Specifically, we set
  $ Q'_1=M_1 dot Hom_Lambda lr((M_1,Q_1)). $
  If $Q'_1=0$, then $K M_1$ and $K Q_1$ have no common simple $A$-modules, so
  for each $i$ we have:
  $
    "either" m_i-beta_i=0 "and" q_i-beta_i >= 0,
    "or" m_i-beta_i >= 0 "and" q_i-beta_i=0.
  $
  In this case we find at once that $beta_i=min(a_i, m_i)$, and the
  decomposition $M=I_1 plus.o M_1$ is the desired one, since $K I_1=I(M)$.

  On the other hand, if $Q'_1 != 0$, Step 2 gives a common nonzero summand and a
  decomposition
  $ M_1=I_2 plus.o M_2,quad Q'_1=I_2 plus.o Q_2, $
  where $I_2 != 0$, $Q_2$ is $M_2^((k))$-injective for each $k$, and
  $
    (op("sig") Q'_1)_i=cases(
      q_i-beta_i & "if" m_i-beta_i != 0,
      0 & "if" m_i-beta_i=0.
    )
  $
  Let $op("sig") I_2={gamma_i}$, so
  $
    op("sig") M_2={m_i-beta_i-gamma_i},
    quad op("sig") Q_2={(op("sig") Q'_1)_i-gamma_i}.
  $
  In general, let $m_(j i)$ and $q_(j i)$ be the actual multiplicities in $M_j$
  and $Q_j$. Passing to the trace $Q'_j=M_j dot Hom_Lambda lr((M_j,Q_j))$ first
  prunes the signature:
  $ q'_(j i)=cases(q_(j i) & "if" m_(j i)>0, 0 & "if" m_(j i)=0). $
  If this trace is nonzero, Step 2 supplies a common nonzero summand of
  signature ${gamma_(j i)}$. Removing it gives
  $ m_(j+1,i)=m_(j i)-gamma_(j i),quad q_(j+1,i)=q'_(j i)-gamma_(j i). $
  Thus the subtraction uses the pruned signature.

  Let $s_i$ be the total multiplicity removed so far in component $i$. At each
  active coordinate, where $m_(j i)>0$, the invariant is
  $ m_(j i)=m_i-s_i,quad q_(j i)=a_i-s_i,quad s_i <= min(m_i, a_i). $
  If a coordinate is pruned because $m_(j i)=0$, then $s_i=m_i <= a_i$, so its
  desired minimum has already been removed. A common summand preserves the
  displayed bound. Every nonzero removal decreases the finite $R$-rank of the
  remainder, so the process terminates. At termination, an active coordinate has
  $q_(j i)=0$, giving $s_i=a_i <= m_i$; a pruned coordinate has
  $s_i=m_i <= a_i$. Therefore $s_i=min(m_i, a_i)$ for every $i$. The sum $M_0$
  of the removed summands is a direct summand of $M$ and satisfies $K M_0=I(M)$,
  proving the theorem.
]

We next prove our second major result: $P_1 => P_2$. This is due to
Roiter~@bib:Roiter1966b, generalizing earlier work by Bass.

#source(808)
#theorem[
  Let $Lambda$ be an $R$-order such that $mu_Lambda lr((I)) <= 2$ for each left
  ideal $I$ of $Lambda$. Then $Lambda$ is a Bass order.
  #idx("Bass' Theorem", target: [@th:two-generator-order-bass])
  #idx("Roiter's Theorem", target: [@th:two-generator-order-bass])
] <th:two-generator-order-bass>

#proof[
  Let $P$ be a maximal ideal of $R$, and $J$ any left ideal of $hat(Lambda)_P$.
  As in the first part of the proof of @th:jones-finite-type-completions, $J$ is
  a direct summand of the completion $hat(I)_P$ of some left ideal $I$ of
  $Lambda$. Since $mu_Lambda lr((I)) <= 2$, it follows that
  $mu_(hat(Lambda)_P) lr((J)) <= 2$. We shall deduce from this that each
  $hat(Lambda)_P$ is a Bass order, whence so is $Lambda$. For the rest of the
  proof, we may therefore take $R$ to be a complete d.v.r.

  The hypotheses imply that#footnote[Since $a Lambda' subset.eq Lambda$ for some
    nonzero $a in R$, $Lambda'$ is isomorphic (as $Lambda$-module) to a left
    ideal of $Lambda$.] $mu_Lambda lr((Lambda')) <= 2$ for each overorder
  $Lambda'$. More generally, every left ideal of an overorder $Gamma$ is a
  finite left $Lambda$-submodule of $A$. Clearing a central denominator embeds
  it in $Lambda$; its two $Lambda$-generators also generate it over $Gamma$.
  Thus the hypothesis on every left ideal passes to every overorder. It suffices
  to prove that an order with this full hypothesis is Gorenstein; the same
  argument for all overorders then proves that $Lambda$ is Bass.

  Retain this hypothesis, and let $N=rad Lambda$. Then $Lambda slash N$ is a
  semisimple artinian ring, so we can find a collection of maximal two-sided
  ideals ${W_1,dots,W_r}$ of $Lambda$ such that the factor rings
  $Lambda slash W_i$ are precisely the Wedderburn components of
  $Lambda slash N$. Let $U_i$ denote a simple right $(Lambda slash W_i)$-module.
  We have
  $ Lambda slash N=plus.o.big Lambda slash W_i. $
  Now $Lambda^*$ is a two-sided $Lambda$-module; let $mu_l lr((Lambda^*))$ be
  the minimal number of generators of $Lambda^*$ as left $Lambda$-module, and
  define $mu_r lr((Lambda^*))$ analogously. Then
  $
    mu_l lr((Lambda^*))=mu_l lr((Lambda^* slash N Lambda^*))
    =op("Max")_i mu_l lr((Lambda^* slash W_i Lambda^*)).
  $
  Further, for each $(Lambda slash W_i)$-module $X$, the number of generators of
  $X$ is completely determined by its composition length (see
  Exercise~@exc:simple-artinian-module-generators). By
  Exercise~@exc:dual-lattice-inclusion-reversal, it follows that
  $
    mu_l lr((Lambda^* slash W_i Lambda^*))
    =mu_r lr(((W_i Lambda^*)^* slash Lambda)).
  $
  However, @eq:lattice-pairing-image-duals gives
  $
    (W_i Lambda^*)^*=Hom_Lambda lr((W_i,Lambda))
    ={x in A:x W_i subset.eq Lambda}=T_i "(say)".
  $
  (We write equality rather than isomorphism, taking account of the canonical
  identification of $A^(**)$ with $A$.) Thus
  $ mu_l lr((Lambda^*))=op("Max")_i mu_r lr((T_i slash Lambda)), $
  so we need only show that the right $Lambda$-module $T_i slash Lambda$ is
  cyclic for each $i$.

  #source(809)
  Let $i$ be fixed, and suppose that $T_i slash Lambda$ is not a cyclic right
  $Lambda$-module. We show that in this case we have
  $ T_i=O_l lr((W_i))={x in A:x W_i subset.eq W_i}, $
  and for this it suffices to prove that $T_i W_i subset.eq W_i$. Now
  $T_i slash Lambda$ is a right $(Lambda slash W_i)$-module, and
  $Lambda slash W_i$ is a simple artinian ring with simple right module $U_i$.
  Thus $T_i slash Lambda$ is a direct sum of copies of $U_i$, and so there
  exists a finite collection ${V_alpha}$ of submodules of $T_i$ such that
  $
    V_alpha supset Lambda,quad V_alpha slash Lambda tilde.equiv U_i
    "for each" alpha,quad "and" T_i=sum_alpha V_alpha.
  $
  To prove that $T_i W_i subset.eq W_i$, we need only show that $V W_i=W_i$,
  where $V$ is any $V_alpha$. Surely $V W_i supset.eq W_i$, since
  $V supset Lambda$, so suppose that $V W_i supset W_i$. Let $l( )$ denote
  $Lambda$-composition length. Then
  $ l(V slash V W_i) <= l(Lambda slash W_i), $
  since $V W_i supset W_i$ and $l(V slash Lambda)=1$. On the other hand, if
  $j != i$ then $W_i+W_j=Lambda$, and since $(V slash Lambda)W_i=0$ we have
  $V W_i subset.eq Lambda$, so
  $ V=V(W_i+W_j)=Lambda+V W_j, $
  whence
  $
    V slash V W_j=(Lambda+V W_j) slash V W_j
    tilde.equiv Lambda slash (Lambda inter V W_j).
  $
  But $Lambda inter V W_j supset.eq W_j$, whence
  $ l(V slash V W_j) <= l(Lambda slash W_j) "for" j != i. $
  Therefore $V slash V W_j$ is a cyclic $(Lambda slash W_j)$-module for _every_
  $j$, including $j=i$. Therefore
  $ mu(V)=op("Max")_j mu(V slash V W_j)=1, $
  so $V$ itself is a cyclic right $Lambda$-module. Since $V$ and $Lambda$ are
  full $R$-lattices in $A$, it follows that $V tilde.equiv Lambda$. Letting
  $Lambda slash W_i tilde.equiv U_i^((n))$, we obtain $Lambda$-exact sequences
  $
    0 -> W_i -> Lambda -> U_i^((n)) -> 0,
    quad 0 -> Lambda^((n)) -> V^((n)) -> U_i^((n)) -> 0.
  $
  Thus $Lambda plus.o V^((n)) tilde.equiv Lambda^((n)) plus.o W_i$ by Schanuel's
  Lemma, whence $W_i tilde.equiv Lambda$. We may write $W_i=y Lambda$ for some
  invertible $y in A$, and then $T_i=Lambda y^(-1)$. From $T_i Lambda=T_i$ we
  obtain $y^(-1)Lambda y subset.eq Lambda$. Conjugate orders have the same
  nonzero discriminant for a nondegenerate invariant trace pairing; an inclusion
  changes it by the square of the index. Over the d.v.r. this forces equality,
  so $y^(-1)Lambda=Lambda y^(-1)$. Hence $T_i$ is a cyclic right
  $Lambda$-module, whence so is $T_i slash Lambda$, contrary to our assumption.
  This completes the proof that $T_i=O_l lr((W_i))$.

  #source(810)
  Continuing with the argument, $T_i W_i=W_i$. Put $S_i=Lambda slash W_i$ and
  $X=T_i slash W_i$, a right $S_i$-module. Choose a uniformizer $pi$ of $R$ and
  put $kappa=R slash pi R$. Since $pi Lambda subset.eq W_i$, we have $pi X=0$.
  Dualizing the inclusion of the full lattices $W_i subset.eq T_i$ gives an
  exact sequence of left $Lambda$-modules
  $ 0 -> T_i^* -> W_i^* -> Y -> 0,quad Y=op("Ext")_R^1 lr((X,R)). $
  The separable algebra has a symmetric nondegenerate pairing
  $A^* tilde.equiv A$ as bimodules. Under this identification, clearing a
  central denominator makes the full left lattice $W_i^*$ a left ideal of
  $Lambda$. Hence the hypothesis on left ideals gives $mu_l lr((W_i^*)) <= 2$,
  and its quotient $Y$ is generated by at most two elements over $S_i$.

  The choice of $pi$ identifies $Y$ with $Hom_kappa lr((X,kappa))$ as a left
  $S_i$-module. If $S_i=M_n lr((D_i))$, simple left and right $S_i$-modules both
  have $kappa$-dimension $n dim_kappa D_i$. Thus their particular dual quotients
  have equal composition lengths:
  $ l_l lr((Y))=l_r lr((X)) <= 2 n, $
  since the left regular $S_i$-module has length $n$. The exact sequence of
  right $S_i$-modules now gives
  $
    l_r lr((T_i slash Lambda))+l_r lr((Lambda slash W_i))
    =l_r lr((T_i slash W_i)) <= 2 n.
  $
  As $l_r lr((Lambda slash W_i))=n$, the quotient $T_i slash Lambda$ has right
  length at most $n$ and is cyclic by
  Exercise~@exc:simple-artinian-module-generators. This is the required
  contradiction. Therefore $Lambda^*$ is cyclic on the left and hence isomorphic
  to $Lambda$, so $Lambda$ is Gorenstein. Applying the same argument with the
  full left-ideal hypothesis to every overorder proves that $Lambda$ is Bass.
]

We now prove Bass' Theorem that $P_3 => P_1$ under suitable circumstances:

#theorem[
  Let $Lambda$ be a commutative noetherian integral domain such that every
  indecomposable f.g. torsionfree $Lambda$-module is isomorphic to an ideal of
  $Lambda$. Then $mu_Lambda lr((I)) <= 2$ for every ideal $I$ of $Lambda$.
  #idx("Bass' Theorem", target: [@th:bass-domain-two-generator-ideals])
] <th:bass-domain-two-generator-ideals>

#proof[
  _Step 1._ Throughout this proof, all $Lambda$-modules considered are assumed
  f.g./$Lambda$. The _rank_ of a torsionfree $Lambda$-module $X$ is (by
  definition) $dim_K lr((K times.o_Lambda X))$, where $K$ is the quotient field
  of $Lambda$. Let $frak(m)$ be any maximal ideal of $Lambda$. Each torsionfree
  indecomposable $Lambda_(frak(m))$-module is the localization of some
  torsionfree indecomposable $Lambda$-module, and hence is an ideal of
  $Lambda_(frak(m))$. Thus $Lambda_(frak(m))$ has the same property as $Lambda$,
  and we shall show that $mu_(Lambda_(frak(m))) lr((I)) <= 2$ for each ideal $I$
  of $Lambda_(frak(m))$.

  Changing notation for the moment, let $Lambda$ be a local domain with maximal
  ideal $frak(m)$, and suppose that every indecomposable torsionfree
  $Lambda$-module is isomorphic to an ideal of $Lambda$. Now suppose that there
  is an ideal $I$ of $Lambda$ such that $mu_Lambda lr((I))=n >= 3$, and let
  $F=Lambda^((n))$ be free. Let $I=sum_1^n Lambda x_i$, and let $F -> I$ be the
  surjection given by $(a_1,dots,a_n) in F |-> sum a_i x_i in I$. If
  $xi=(x_1,dots,x_n) in F$, then $I$ is generated by the images of the
  coordinates of $xi$. This also holds if $xi$ is replaced by $xi bold(P)$ with
  $bold(P) in GL_n lr((Lambda))$. Now $xi$ cannot lie in any proper direct
  summand of $F$; for any such summand would be projective, hence free, and so
  relative to some suitable new basis, $xi$ would be represented by an $n$-tuple
  $xi'$ with at least one zero entry. This would contradict the assumption that
  $mu_Lambda lr((I))=n$, because the images of the entries of $xi'$ generate
  $I$.

  We now form the $Lambda$-module $L=F inter K xi$, so $F slash L$ is a
  torsionfree $Lambda$-module. From the exact sequence
  $ 0 -> L -> F -> M -> 0,quad M=F slash L, $
  we see that $M$ has rank $n-1$, so $M$ must decompose nontrivially. Suppose
  that $M=M_1 plus.o M_2$, where $M_1,M_2$ are nonzero. We have
  $
    rank M_1+rank M_2=rank M=n-1,
    quad mu(M_1)+mu(M_2)=mu(M) <= n,
  $
  the latter because $Lambda$ is local (and thus $mu$ is additive!). But
  $rank X <= mu(X)$ for
  #source(811)
  all $Lambda$-modules $X$, with equality if and only if $X$ is free. Now $M$
  cannot be free, since otherwise $xi$ lies in the direct summand $L$ of $F$.
  Thus $mu(M)=n$, and consequently $rank M_i=mu(M_i)$ for exactly one $i$, say
  $i=1$. But then $M_1$ is $Lambda$-free, and we obtain a surjection
  $phi:F -> M_1$ by composition of maps $F -> M -> M_1$. Since $xi in ker phi$,
  we obtain a contradiction, which completes the proof that when $Lambda$ is
  local, $mu_Lambda lr((I)) <= 2$ for each ideal $I$ of $Lambda$.

  _Step 2._ We now return to our original domain $Lambda$. We may suppose that
  #named-equation(name: [$(ast)$])[
    $
      mu_(Lambda_(frak(m))) lr((I_(frak(m)))) <= 2
      "for every ideal" I_(frak(m)) "of" Lambda_(frak(m)),
      "for every maximal ideal" frak(m) "of" Lambda.
    $
  ] <eq:bass-domain-local-two-generator-hypothesis>
  We must show that @eq:bass-domain-local-two-generator-hypothesis implies
  $mu_Lambda lr((I)) <= 2$ for every ideal $I$ of $Lambda$. The key step in this
  proof is the fact that as a consequence of
  @eq:bass-domain-local-two-generator-hypothesis, each nonzero ideal $I$ of
  $Lambda$ is contained in only a finite number of maximal ideals of $Lambda$.
  This follows from Cohen~@bib:Cohen1950, Cor.~1 to Th.~10, and we shall omit
  the details of the proof. In the case where $Lambda$ is an $R$-order in some
  field, it is obvious that for nonzero $I$, the factor ring $Lambda slash I$ is
  a f.g. $R$-torsion $R$-algebra, hence is semilocal and has finitely many
  maximal ideals. Thus, Cohen's Theorem is not needed for the case of orders.

  The ideals $0$ and $Lambda$ require no argument. Now let $I$ be a nonzero
  proper ideal of $Lambda$, and assume
  @eq:bass-domain-local-two-generator-hypothesis holds true. Let
  $frak(m)_1,dots,frak(m)_n$ be the distinct maximal ideals of $Lambda$
  containing $I$. Using an obvious generalization of the Chinese Remainder
  Theorem, we can find a nonzero element $x in I$ which is part of a minimal
  generating set for each $I_(frak(m)_nu)$, $1 <= nu <= n$. Now let
  $frak(q)_1,dots,frak(q)_r$ be the maximal ideals of $Lambda$ which contain
  $x$. For each $rho$, $1 <= rho <= r$, we may choose an element $y_rho in I$
  such that ${x,y_rho}$ generate $I_(frak(q)_rho)$ as
  $Lambda_(frak(q)_rho)$-module. Indeed, if $frak(q)_rho$ is one of the
  $frak(m)$'s, such a choice is possible because of the way $x$ was picked; on
  the other hand, if $frak(q)_rho$ is not one of the $frak(m)$'s, then
  $I_(frak(q)_rho)=Lambda_(frak(q)_rho)$, so choose $y_rho in I-frak(q)_rho$.
  Now choose $y in I$ so that $y equiv y_rho (mod frak(q)_rho I)$,
  $1 <= rho <= r$. It is then easily verified that $I=Lambda x+Lambda y$, so
  $mu_Lambda lr((I)) <= 2$ as desired. This completes the proof.
]

We discuss briefly some further results on these topics:

#enum(
  numbering: "(a)",
  [(Borevich-Faddeev~@bib:Borevich1965a, @bib:Borevich1965b): Let
    $A="commutative separable" K$-algebra, $Lambda=R$-order in $A$,
    $Lambda_0="maximal" R$-order. Call $Lambda$ of _cyclic index_ (in
    $Lambda_0$)#idx("cyclic index") if $Lambda_0=Lambda+Lambda omega$ for some
    $omega$. If $Lambda$ is of cyclic index, then:
    #enum(
      numbering: "(i)",
      [Every full $Lambda$-lattice in $A$ is invertible, or equivalently,
        locally free.],
      [Every full $Lambda$-lattice $M$ in $A^((s))$ uniquely determines an
        ascending chain of $R$-orders in $A$:
        $Lambda subset.eq Lambda_1 subset.eq dots subset.eq Lambda_s$, such that
        $
          M tilde.equiv product.co J_i "as" Lambda "-lattices, with"
          J_i "a full" Lambda "-lattice in" A "such that"
          // Each summand has the indicated multiplier order.
          O_l lr((J_i))=Lambda_i.
        $
      ],
      [The isomorphism invariants of $M$ are the chain of orders ${Lambda_i}$
        and the ideal class of $product_i J_i$ (as $Lambda_s$-module). Further,
        we may choose $J_i=Lambda_i$, $1 <= i <= s-1$, in the above.],
    )
    #source(812)
    #enum(
      numbering: "(i)",
      start: 4,
      [The direct-sum-of-ideals property does not in general imply cyclic
        index.#ed-note[
          Take $Lambda=hat(ZZ)_2 C_4$. In
          @th:prime-square-cyclic-complete-lattice-classification the
          repeated-component family $1 <= k <= p-2$ is empty for $p=2$; each of
          the nine indecomposables embeds in the regular algebra and scales to
          an ideal. Complete K-S-A gives the direct-sum property for all
          lattices. But the normalization is
          $O=hat(ZZ)_2 plus.o hat(ZZ)_2 plus.o hat(ZZ)_2[i]$. For $J=(2,x-1)$,
          where $x$ generates $C_4$, one has
          $O slash J O tilde.equiv bb(F)_2^3$, so $mu_Lambda lr((O))=3$. Cyclic
          index $O=Lambda+Lambda omega$ would give at most two generators, a
          contradiction.
        ]],
    )
  ],
  [(Bass): Let $Lambda$ be an order in the _commutative_ $K$-algebra $A$.
    #idx("Bass' Theorem")
    #enum(
      numbering: "(i)",
      [If $A$ is a field, then $P_3 => P_1$. (Bass~@bib:Bass1962).],
      [$P_2 => P_1$ always. (Bass~@bib:Bass1963, §7).],
      [$P_1$ is a local property. (Bass~@bib:Bass1963, Lemma~7.4).],
    )
  ],
  [(Drozd-Kirichenko-Roiter~@bib:Drozd1967b): Let $R="complete d.v.r."$, $A=D$
    or $D_1 plus.o D_2$ or $M_2 lr((D))$, where the $D$'s are f.d. division
    algebras over $K$. Let $Lambda$ be a local $R$-order in $A$. Then
    $P_3 => P_1$. Further, any local Bass order $Lambda$ must be an $R$-order in
    one of the algebras $A$ of the type above.
    #idx("Drozd-Kirichenko-Roiter Theorem")
  ],
  [(Roiter~@bib:Roiter1963a, @bib:Roiter1963b): We give a brief discussion of
    normal decompositions of modules. By definition, a $Lambda$-module $L$ has a
    _normal decomposition_#idx("normal decomposition") if
    $L=L_1 plus.o dots plus.o L_r$, $r>1$, where the ${L_i}$ are nonzero
    submodules of $L$ such that $L_i succ L_j$ for $1 <= i < j <= r$. If no such
    decomposition exists, call $L$ _normally indecomposable_.
    #idx("normally indecomposable")
  ],
)

The importance of this concept arises from its connection with the earlier
concept of one module covering another. Let us establish:

#proposition[
  Let $Lambda$ be an $R$-order, where $R$ is a complete d.v.r., and let $L$ and
  $M$ be left $Lambda$-lattices such that $L succ M$. Suppose that either $L$ is
  normally indecomposable, or else that every idempotent in $End_Lambda L$ is
  central. Then every $Lambda$-surjection $M -> L$ is split.
] <prop:normal-indecomposable-cover-splitting>

#proof[
  Let $Gamma=End_Lambda L$, acting from the left on $L$. Given a
  $Lambda$-surjection $phi:M -> L$, put
  $ T={phi tau:tau in Hom_Lambda lr((L,M))}="right ideal of" Gamma. $
  Since $L succ M$ and $phi$ is surjective, we have $T dot L=L$. Now let
  $
    overline(Gamma)=Gamma slash rad Gamma,
    quad overline(T)=(T+rad Gamma) slash rad Gamma subset.eq overline(Gamma).
  $
  Then $overline(T)$ is a right ideal of the semisimple ring $overline(Gamma)$.
  If $overline(T)=0$ then $T subset.eq rad Gamma$, so $L=(rad Gamma)L$, which is
  impossible by Nakayama's Lemma (we assume $L != 0$, of course). Thence
  $overline(T) != 0$, so $overline(T)=overline(e) overline(Gamma)$ for some
  idempotent $e in Gamma$. We now have $T subset.eq e Gamma+rad Gamma$, so
  $ L=Gamma L=Gamma T L subset.eq Gamma e L+(rad Gamma)L subset.eq L, $
  #source(813)
  and thus $L=Gamma e L$. Since $e$ centralizes $Lambda$, there is a
  $Lambda$-decomposition
  $ L=e L plus.o (1-e)L. $
  For each $gamma in Gamma$ we have $gamma e in Hom_Lambda lr((e L,L))$, whence
  (in the notation of @eq:module-cover-trace)
  $ L supset.eq e L dot Hom_Lambda lr((e L,L)) supset.eq Gamma e L=L. $
  This shows that $e L succ L$ as left $Lambda$-modules. But $L succ (1-e)L$,
  and thus $e L succ (1-e)L$. We therefore obtain a normal decomposition of $L$,
  except when $e=1$. Thus, if $L$ is assumed normally indecomposable, then $e=1$
  and $overline(T)=overline(Gamma)$. But then $T$ contains a unit of $Gamma$, so
  $T=Gamma$ and thus $1 in T$. Hence $phi tau=1$ for some
  $tau in Hom_Lambda lr((L,M))$, and then $tau$ is the desired splitting of
  $phi$. On the other hand, if we assume instead that each idempotent of $Gamma$
  is central, then $L=Gamma e L=e Gamma L=e L$, so $e=1$ since $Gamma$ acts
  faithfully on $L$. This completes the proof.
]

For further results on normal decompositions of modules, see
Brzezinski~@bib:Brzezinski1978.

#exercises-heading

Throughout, $Lambda$ is an $R$-order in a f.d. separable $K$-algebra $A$.

#exercise[
  Let $L$ be a left $Lambda$-lattice, and consider all diagrams
  #idx("weakly injective", target: [@exc:weak-injectivity-extension])
  #weak-injectivity-diagram()
  with exact row of $Lambda$-lattices. Show that $L$ is weakly injective if and
  only if for each such diagram, $f$ extends to a map $g:M -> L$.
] <exc:weak-injectivity-extension>

#hint([@exc:weak-injectivity-extension])[
  If each $f$ extends, then every exact sequence of lattices
  $ 0 -> L -> M -> M_2 -> 0 $
  must split, by taking $M_1=L$, $f=1$ above. Conversely, given such a diagram,
  let $X$ be the pushout of ${f,mu}$. Then there is an exact sequence
  $0 -> L -> X -> M_2 -> 0$. If $L$ is weakly injective, the sequence splits,
  and from the splitting map $X -> L$ one easily obtains the desired $g:M -> L$.
]

#exercise[
  Given $L$ and $M$, suppose each diagram above, with _fixed_ $M$, can be
  completed to a commutative diagram by means of a map $g:M -> L$. In this case,
  call $L$ “$M$-injective”. Show that if $I$ is a weakly injective
  $Lambda$-lattice, then $M dot Hom_Lambda lr((M,I))$ is $M^((n))$-injective for
  each $n$.
] <exc:trace-relative-injectivity>

#source(814)
#hint([@exc:trace-relative-injectivity])[
  Put $L=M dot Hom_Lambda lr((M,I))=Lambda$-sublattice of $I$. Then, using the
  notation of @eq:module-cover-trace,
  $ M^((n)) dot Hom_Lambda lr((M^((n)),I))=M dot Hom_Lambda lr((M,I))=L. $
  Consider a diagram
  #trace-injectivity-diagram()
  with exact row of $Lambda$-lattices, and $i$ the inclusion map. Then there
  exists $g:M^((n)) -> I$ extending $i f$, and $g(M^((n))) subset.eq L$, so $g$
  extends $f$.
]

#exercise[
  Let $L$ be $M^((n))$-injective for each $n$, and set
  $ L=P plus.o Q,quad M=P plus.o T. $
  Show that $Q$ is $T^((n))$-injective for each $n$.
] <exc:relative-injectivity-common-summand>

#hint([@exc:relative-injectivity-common-summand])[
  Starting with
  #summand-injectivity-diagram()
  form the diagram
  #summand-injectivity-extension-diagram()
  where $f'$ coincides with $f$ on $T_1$ and vanishes on $P^((n))$. Extend $f'$
  to $g'$, project onto $Q$, and then restrict: the desired extension of $f$ is
  $pi_Q compose g'|_(T^((n)))$, where $pi_Q:Q plus.o P -> Q$ is the projection.
]

#exercise[
  Let $G$ be a cyclic group of prime order. Show that $ZZ G$ is a Bass order.
] <exc:prime-cyclic-integral-group-ring-bass>

#exercise[
  Let $L subset.eq M$ be left $Lambda$-lattices. Call $L$ _hypercharacteristic_
  in $M$#idx("hyper-characteristic") if
  $L dot Hom_Lambda lr((L,M)) subset.eq L$, that is, $f(L) subset.eq L$ for each
  $f in Hom_Lambda lr((L,M))$. Show
  #enum(
    numbering: "(i)",
    [For each order $Gamma$ containing $Lambda$, $Gamma^*$ is a
      hypercharacteristic right $Lambda$-sublattice of $Lambda^*$.],
    [Each hypercharacteristic $M subset.eq Lambda^*$ for which
      $Lambda^* slash M$ is $R$-torsion, is some $Gamma^*$.],
    [The correspondence $Gamma <-> M$ is one-to-one inclusion-reversing.],
  )
] <exc:hypercharacteristic-order-dual-correspondence>

#source(815)
#hint([@exc:hypercharacteristic-order-dual-correspondence])[
  If $Lambda subset.eq Gamma$ then $Gamma^* subset.eq Lambda^*$, and
  $
    Hom_Lambda lr((Gamma^*,Lambda^*))=(Gamma^* dot Lambda)^*
    subset.eq (Gamma^* dot Gamma)^*=Hom_Lambda lr((Gamma^*,Gamma^*)),
  $
  so $Gamma^*$ is hypercharacteristic in $Lambda^*$. Conversely, given $M$ as in
  (ii), put $L=M^*="left" Lambda$-lattice containing $Lambda$. Then
  $
    L=(L^* dot Lambda)^*=Hom_Lambda lr((L^*,Lambda^*))
    =Hom_Lambda lr((M,Lambda^*))=Hom_Lambda lr((M,M)),
  $
  so $L$ is an order. The result is due to
  Drozd-Kirichenko-Roiter~@bib:Drozd1967b.
]

#exercise[
  For a $Lambda$-lattice $M$, define $I(M)$ as in @eq:lattice-signature-ideal.
  Show that for each $P$, $I(hat(M)_P)$ is the $P$-adic completion of $I(M)$.
] <exc:signature-ideal-completion>

#hint([@exc:signature-ideal-completion])[
  Let $hat(S)_i=product.co_j S_(i j)^((r_j))$, where ${S_(i j)}$ is a basic set
  of simple left $hat(A)$-modules. Then
  $
    hat(A) tilde.equiv product.co_(i,j) S_(i j)^((r_j a_i)),
    quad hat(K M) tilde.equiv product.co_(i,j) S_(i j)^((r_j m_i)),
  $
  so
  $
    I(hat(M))=product.co_(i,j) S_(i j)^min(r_j m_i, r_j a_i)
    =hat(K) times.o I(M).
  $
]

#exercise[
  Let $R$ be a complete d.v.r., and let $Lambda$ be a local Gorenstein $R$-order
  which is not a maximal order. Then there is a unique minimal overorder
  $Lambda'$ containing $Lambda$, and indeed
  $Lambda'=End_Lambda lr((rad Lambda))$.
] <exc:local-gorenstein-minimal-overorder>

#hint([@exc:local-gorenstein-minimal-overorder])[
  (Roiter~@bib:Roiter1966b). Let $N=rad Lambda$. Since $Lambda^* succ Lambda$
  and $Lambda$ is indecomposable as module, we have
  $Lambda^* tilde.equiv Lambda$. Thus $N Lambda^*$ is the unique maximal
  submodule of $Lambda^*$. If $N Lambda^* succ Lambda^*$, then
  $N Lambda^* tilde.equiv Lambda$, whence $N tilde.equiv Lambda$. But then
  $Lambda$ is a hereditary order by @bib:Reiner1975[MO] (39.1), and is therefore
  a maximal order by @th:local-hereditary-orders-block-form. Thus $N Lambda^*$
  does not cover $Lambda^*$, whence
  $N Lambda^* dot Hom_Lambda lr((N Lambda^*,Lambda^*))=N Lambda^*$. Therefore
  $N Lambda^*$ is hypercharacteristic in $Lambda^*$. Now use
  Exercise~@exc:hypercharacteristic-order-dual-correspondence.
]

#exercise[
  Show that $Lambda$ is a Gorenstein order if and only if every indecomposable
  lattice $L$ can be embedded as a pure submodule of a free $Lambda$-lattice.
  Show also that an $R$-order $Lambda$ is hereditary if and only if
  $M times.o_Lambda L$ is $R$-torsionfree for every right $Lambda$-lattice $M$
  and left $Lambda$-lattice $L$.
] <exc:gorenstein-pure-free-embedding>

#hint([@exc:gorenstein-pure-free-embedding])[
  See Gustafson~@bib:Gustafson1974.
]

#exercise[
  Let $Lambda subset.eq Gamma$ be $R$-orders in $A$, and let $L$ and $M$ be
  $Gamma$-lattices. Show that if $L succ M$ as $Gamma$-lattices, then also
  $L succ M$ as $Lambda$-lattices.
] <exc:overorder-module-cover-restriction>

#exercise[
  Let $Lambda subset.eq Gamma$ as above, and let $L$ be a $Gamma$-lattice, $M$ a
  $Lambda$-lattice. Show that if $L succ M$ as $Lambda$-lattices, then $M$ is
  necessarily a $Gamma$-lattice.
] <exc:cover-descends-overorder-action>

#source(816)
#hint([@exc:cover-descends-overorder-action])[
  Choose a nonzero $a in R$ such that $a Gamma subset.eq Lambda$. For each
  $f in Hom_Lambda lr((L,M))$, $f(a Gamma dot L)=a f(L)$. Hence
  $ a Gamma M=sum_f f(a Gamma L)=sum_f f(a L)=a sum_f f(L)=a M, $
  so $Gamma M=M$.
]

#exercise[
  Let $V$ be a f.g. left $A$-module, and set $V^*=Hom_K lr((V,K))$. For each
  full $Lambda$-lattice $M$ in $V$, let $M^*=Hom_R lr((M,R))$. Then $M^*$ is a
  full $Lambda$-lattice in the right $A$-module $V^*$. Prove that the bijection
  $M <-> M^*$ is inclusion-reversing.
] <exc:dual-lattice-inclusion-reversal>

#hint([@exc:dual-lattice-inclusion-reversal])[
  Let $M subset.eq N$, where $N$ is a full $Lambda$-lattice in $V$, and put
  $T=N slash M$. Now apply $Hom_R lr((dot,R))$ to the exact sequence
  $ 0 -> M -> N -> T -> 0. $
]
