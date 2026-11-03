#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/02-hom-tensor.typ": *

#heading(level: 2)[
  The Functors Hom and $times.o$. Projective, Injective, and Flat Modules
] <sec:hom-tensor-projective-injective-flat>

This section contains a review of basic concepts from homological algebra. Later
(§@sec:ext-tor-cohomology) we shall survey some more advanced topics, including
the functors Ext and Tor, and the cohomology of finite groups. Proofs will be
omitted in most cases, and are often easy exercises for the reader who may be
unfamiliar with them. For the theory of tensor products, we shall assume
knowledge of
#source(36)
the material in @bib:CurtisReiner1962[CR §~12]. A list of references on
Homological Algebra is given at the end of this section, just before the
Exercises.

Throughout this book, all rings are assumed to have identity elements, which act
as identity operators on all modules over the rings. We abbreviate “finitely
generated” as “f.g.”, and write “$M$ is f.g./$A$” to indicate that $M$ is a
finitely generated module over the ring $A$.

=== Homomorphisms <ss:homomorphisms>

Let $A$ be a ring (associative, but not necessarily commutative), and let $M,N$
be left $A$-modules. We denote by $Hom_A lr((M,N))$ the additive group
consisting of all $A$-homomorphisms from $M$ into $N$. For
$f in Hom_A lr((M,N))$, let
$
  cases(
    ker f = "kernel of" f = {m in M: f(m)=0}\,,
    im f = "image of" f = f(M) = {f(m): m in M}\,,
    "cok" f = "cokernel of" f = N slash f(M).
  )
$ <eq:kernel-image-cokernel>
A sequence of $A$-modules and $A$-homomorphisms
$
  M_1 arrow.r^(f_1) M_2 arrow.r^(f_2) M_3 -> dots
  arrow.r^(f_(n-1)) M_n
$
is _exact at_#idx(
  "exact sequence",
) $M_i$ if $ker f_i = im f_(i-1)$. The sequence is _exact_ if it is exact at
each $M_i$, that is, $ker f_i = im f_(i-1)$ for $2 <= i <= n-1$.

A _short exact sequence_#idx(
  "short exact sequence",
) (abbreviated hereafter as “ses”) is an exact sequence of the form
$ 0 -> L arrow.r^f M arrow.r^g N -> 0. $ <eq:short-exact-sequence>
Exactness of this sequence is equivalent to the following three conditions:
$ f "is injective," quad im f = ker g, quad g "is surjective." $
In this case, $g$ induces an $A$-isomorphism $M slash f(L) tilde.equiv N$.

We call the ses @eq:short-exact-sequence _split_#idx(
  "split sequence",
) if $f(L)$ is a direct summand of $M$. Let $id_L$ (or $1_L$) denote the
identity map on the module $L$. We state without proof (see references):

#proposition[
  Given a short exact sequence @eq:short-exact-sequence, the following
  conditions are equivalent:
  #enum(
    numbering: "(i)",
    [The sequence is split.],
    [There exists an $h in Hom_A lr((M,L))$ such that $h f$ is an automorphism
      of $L$.],
    [#source(37)
      There exists an $h' in Hom_A lr((N,M))$ such that $g h'$ is an
      automorphism of $N$.],
  )
] <prop:split-short-exact-sequence>

A diagram of $A$-modules and $A$-homomorphisms
#commutative-square($L_1$, $L_2$, $M_1$, $M_2$, $f_1$, $g_1$, $f_2$, $g_2$)
is _commutative_#idx(
  "commutative diagram",
) if $f_2 f_1 = g_2 g_1$. Likewise, the diagram
#commutative-triangle($L$, $M$, $N$, $f$, $g$, $h$)
is commutative if $g f = h$.

Before listing some standard properties of Hom, let us briefly discuss the
concept of a bimodule. Let $A$ and $B$ be rings; an _$(A,B)$-bimodule_#idx(
  "bimodule",
) $attach(M, bl: A, br: B)$ is an additive group $M$ which is simultaneously a
left $A$-module and a right $B$-module, such that
$ a(m b) = (a m)b, quad a in A, m in M, b in B. $
We sometimes say that “the action of $A$ on $M$ commutes with the action of $B$
on $M$”. It is easy to give examples of bimodules: every ring $A$ is
automatically an $(A,A)$-bimodule $attach(A, bl: A, br: A)$. Further, every left
$A$-module $M$ may be viewed as a right $ZZ$-module, and then $M$ is an
$(A,ZZ)$-bimodule. Finally, if $A$ is a commutative ring and $M$ is a left
$A$-module, we may let $A$ act on the right on $M$ by defining $m dot a = a m$,
$a in A$, $m in M$; then $M$ becomes a bimodule $attach(M, bl: A, br: A)$.
Trivial though it may be, this last observation has many useful consequences, as
we shall see later.

Now let $f in Hom_A lr((M,N))$, where $M,N$ are left $A$-modules. For each left
$A$-module $X$, the homomorphism $f$ induces an additive homomorphism
$ f^*: Hom_A lr((N,X)) -> Hom_A lr((M,X)), $ <eq:hom-contravariant-map>
defined by
$ f^* alpha = alpha f, quad alpha in Hom_A lr((N,X)). $
This definition may be understood more clearly in terms of diagrams: the
#source(38)
map $f^*$ is defined by the condition that for each $alpha$, the diagram
#commutative-triangle($M$, $N$, $X$, $f$, $alpha$, $f^* alpha$)
is commutative.

We may observe that the map $f^*$ goes “in the opposite direction” from $f$,
that is, $f$ maps $M$ into $N$ whereas $f^*$ maps $Hom(N, X)$ into $Hom(M, X)$.
Since $f^*$ arises from a change in the first variable in Hom, we call Hom
_contravariant in the first variable_#idx(
  "contravariant",
). It is easily verified that
$
  (g f)^* = f^* g^*, quad "for all" f in Hom_A lr((M,N)),
  g in Hom_A lr((N,N')).
$
Thus, contravariance reverses the order of composition of homomorphisms!

Let us once more start with an $f in Hom_A lr((M,N))$ and an $A$-module $X$;
then $f$ induces an additive homomorphism
$ f_*: Hom_A lr((X,M)) -> Hom_A lr((X,N)), $ <eq:hom-covariant-map>
defined by
$ f_* alpha = f alpha, quad alpha in Hom_A lr((X,M)). $
In terms of diagrams, $f_*$ is defined by the condition that the diagram
#covariant-triangle
commutes for each $alpha$.

We observe that the map $f_*$ goes “in the same direction” as $f$, since $f$
maps $M$ into $N$ whereas $f_*$ maps $Hom(X, M)$ into $Hom(X, N)$. Since $f_*$
arises from a change in the second variable in Hom, we say that Hom is
_covariant in the second variable_#idx(
  "covariant",
). One easily checks that
$
  (g f)_* = g_* f_* quad "for all" f in Hom_A lr((M,N)),
  g in Hom_A lr((N,N')).
$
Thus, covariance preserves the order of composition of homomorphisms.

The concepts of covariance and contravariance are extremely important in dealing
with modules. For example, let $A$ and $B$ be rings, and let us start with
#source(39)
the data
$
  attach(L, bl: A) = "left" A "-module," quad
  attach(M, bl: A, br: B) = (A,B) "-bimodule."
$
As we shall see, the additive group $Hom_A lr((L,M))$ can be given the structure
of a $B$-module, because of the bimodule structure of $M$. Indeed, since $M$ is
a right $B$-module occurring in a _covariant_ position, it will automatically
turn out that $Hom_A lr((L,M))$ will be a _right_ $B$-module. Let us proceed to
describe this construction explicitly: for each $b in B$, let
$b' in Hom_A lr((M,M))$ be the map defined by
$ b' lr((m)) = m b, quad m in M. $
Clearly $(b c)' = c' b'$ for $b,c in B$. As in @eq:hom-covariant-map, there is
an induced additive homomorphism
$ (b')_*: Hom_A lr((L,M)) -> Hom_A lr((L,M)), $
given by $(b')_* alpha = b' alpha$, $alpha in Hom_A lr((L,M))$. We now define
the action of $B$ on $Hom_A lr((L,M))$ by setting
$ alpha dot b = (b')_* alpha, quad b in B, alpha in Hom_A lr((L,M)). $
Then for $c in B$ we have
$
  alpha dot (b c) & = {(b c)'}_* alpha = {c' b'}_* alpha
                    = {(c')_* (b')_*} alpha \
                  & = (c')_* {alpha dot b} = {alpha dot b} dot c
$
for each $alpha$. Hence $Hom_A lr((L,M))$ is a _right $B$-module_, as claimed.
To be explicit, we have
$
  (alpha dot b)x = (b')_* alpha x = b' lr((alpha x)) = (alpha x)b,
  quad x in L,
$
for all $b in B$, $alpha in Hom_A lr((L,M))$. We could have predicted the final
formula $(alpha b)x = (alpha x)b$ in advance, since it must arise from the fact
that $M$ is a right $B$-module, so $b$ must act from the right on some element
of $M$.

Analogously, starting with the same data as above, we may make $Hom_A lr((M,L))$
into a _left_ $B$-module, since $M$ is a right $B$-module occurring in a
_contravariant_ position. Indeed, for each $b in B$ the above-defined $b'$
induces a map
$ (b')^*: Hom_A lr((M,L)) -> Hom_A lr((M,L)) $
by setting $(b')^* beta = beta b'$, $beta in Hom_A lr((M,L))$. We now define the
action of $B$ on
#source(40)
$Hom_A lr((M,L))$ by the formula
$ b dot beta = (b')^* beta, quad b in B, beta in Hom_A lr((M,L)). $
Then for $b,c in B$ we have
$
  (b c) dot beta & = {(b c)'}^* beta = {c' b'}^* beta
                   = (b')^* (c')^* beta \
                 & = b dot {c dot beta}
$
for all $beta$, as desired. Explicitly, we obtain
$ (b beta)m = beta(m b), quad b in B, m in M, beta in Hom_A lr((M,L)). $
As an example of the above, let $M$ be a left $A$-module and view $A$ as an
$(A,A)$-bimodule. We may form the group
$Hom_A lr((attach(A, bl: A, br: A), attach(M, bl: A)))$ of left
$A$-homomorphisms from $A$ into $M$. By the preceding paragraph, this group
$Hom_A lr((A,M))$ is then automatically a left $A$-module, according to the
formula
$
  (a f)x = f(x a), quad a in A, x in attach(A, bl: A, br: A),
  f in Hom_A lr((A,M)).
$
It is easily verified that there is an isomorphism
$ Hom_A lr((A,M)) tilde.equiv M $ <eq:hom-regular-module>
as left $A$-modules; the isomorphism is given by $f -> f(1)$, for
$f in Hom_A lr((A,M))$.

We may also remark that the isomorphism in @eq:hom-regular-module is
_natural_#idx(
  "natural",
), in the following sense: if $theta_M$ denotes this isomorphism, then for every
pair of left $A$-modules $M$ and $N$, and for every $h in Hom_A lr((M,N))$, the
diagram
#hom-regular-naturality
is commutative.

As a second illustration of the above type of reasoning, suppose for the moment
that the ring $A$ is commutative. Every one-sided $A$-module can then be viewed
as $(A,A)$-bimodule, with elements of $A$ acting the same on the left as on the
right. Hence in this case, for $A$-modules $L$ and $M$, the additive group
$Hom_A lr((L,M))$ automatically acquires the structure of $A$-module. In the
same way, the tensor product $L times.o_A M$ may be viewed as $A$-module.

#source(41)
Given a pair $M_1$ and $M_2$ of left $A$-modules, where $A$ is an arbitrary
ring, we define their _external direct sum_#idx(
  "external direct sum",
) as
$ M_1 plus.dot M_2 = {(m_1,m_2): m_1 in M_1, m_2 in M_2}, $
where these pairs are added componentwise, and where
$ a(m_1,m_2) = (a m_1,a m_2) quad "for all" a in A, m_1 in M_1, m_2 in M_2. $
More generally, let ${M_i: i in I}$ be a possibly infinite family of left
$A$-modules. Let $M$ be the set of all $I$-tuples $(m_i: i in I)$ with
$m_i in M_i$ for each $i in I$, such that $m_i = 0$ a.e. (Here, “a.e.” means
“almost everywhere,” that is, for all but a finite number of values of the index
$i$.) We make $M$ into a left $A$-module by using componentwise addition of
$I$-tuples, and by setting
$ a(m_i) = (a m_i) quad "for" a in A, m_i in M. $
Call $M$ the _external direct sum_ of the family ${M_i: i in I}$; we denote $M$
by either $op(plus.dot, limits: #true)_(i in I) M_i$ or
$product.co_(i in I) M_i$ (see below).#footnote[The direct sum symbol
  $product.co$ is the inverted version of the product symbol $product$. Direct
  products of modules rarely occur in this book.]

On the other hand, let $N$ be a left $A$-module, and let $N_1$ and $N_2$ be a
pair of submodules of $N$ such that each $n in N$ is uniquely expressible as a
sum $n = n_1 + n_2$, $n_i in N_i$. We call $N$ the _(internal) direct sum_#idx(
  "direct sum",
) of the submodules $N_1$ and $N_2$, and write $N = N_1 plus.o N_2$. We note
that if $N = N_1 + N_2$, then the sum is direct if and only if
$N_1 inter N_2 = 0$. Likewise, we write
$N = op("⨁", limits: #true)_(i in I) N_i$ as an _internal direct sum_ of a
family ${N_i: i in I}$ of submodules, if each $n in N$ is uniquely expressible
as a sum $n = sum n_i$, with $n_i in N_i$ and $n_i = 0$ a.e.

There is an obvious connection between the two concepts. Consider an external
direct sum $M = product.co_(i in I) M_i$; for each $i_0 in I$ and each
$m_(i_0) in M_(i_0)$, we may form the $I$-tuple $chevron.l m_(i_0)
chevron.r$ which has entry $m_(i_0)$ at the $i_0$-th place, and zeros elsewhere.
Let $N_(i_0)$ be defined as ${chevron.l m_(i_0) chevron.r: m_(i_0) in M_(i_0)}$.
Clearly we have $N_(i_0) tilde.equiv M_(i_0)$ for each $i_0$, and $M$ is the
direct sum of the family ${N_(i_0): i_0 in I}$ of submodules of $M$. Conversely,
given any internal direct sum $op("⨁", limits: #true)_(i in I) N_i$ of
submodules ${N_i}$ of $N$, we have
$ op("⨁", limits: #true)_(i in I) N_i tilde.equiv product.co_(i in I) N_i. $
It is sometimes vital to be able to distinguish between internal direct sums and
external direct sums. For example, $product.co_(i=1)^n A$ would denote the
$A$-module consisting of all $n$-tuples from $A$ (often denoted by $A^((n))$),
whereas the sum $A + dots + A$ formed within $A$ is not a direct sum if $n > 1$.
This situation occurs in §@sec:dedekind-domains, when we are studying
$R$-lattices with $R$ a Dedekind ring. Every
#source(42)
$R$-lattice is (up to isomorphism) an external direct sum
$product.co_(i=1)^n frak(a)_i$, with each $frak(a)_i$ a nonzero ideal of $R$.
However, if $n > 1$ this sum is _not_ isomorphic to the internal sum
$sum_(i=1)^n frak(a)_i$ of ideals of the ring $R$, and indeed the sum cannot be
direct.

Associated with an internal direct sum $M = op("⨁", limits: #true)_(i in I) M_i$
we have a family of _projection maps_#idx(
  "projection maps",
) ${pi_i: i in I}$, defined by
$ pi_i lr((sum_(j in I) m_j)) = m_i, quad i in I. $
Each $pi_i in End_A lr((M))$, and we have for all $m in M$,
$ m = sum_(i in I) pi_i lr((m)), quad pi_i lr((m)) = 0 "a.e." $
Further,
$
  pi_i^2 = pi_i quad "for" i in I, quad pi_i pi_j = 0 "for" i != j,
  quad 1 = sum_(i in I) pi_i.
$
If $M_i != 0$, then $pi_i != 0$. We also call the ${pi_i}$ a set of _orthogonal
idempotents_#idx(
  "idempotent",
)#idx(
  "orthogonal idempotents",
) associated with the direct sum decomposition of $M$. Here, “orthogonal” refers
to the property that $pi_i pi_j = 0$ for $i != j$, while “idempotent” means that
$pi_i^2 = pi_i != 0$ for each $i$. Conversely, given a set of orthogonal
idempotents ${pi_i: i in I}$ in $End_A lr((M))$, such that for each $m$,
$ 1 = sum_(i in I) pi_i, quad "and" pi_i lr((m)) = 0 "a.e.," $
we obtain an (internal) direct sum decomposition
$
  M = op("⨁", limits: #true)_(i in I) M_i, quad "where" M_i = pi_i lr((M))
  quad "for each" i in I.
$
External direct sums $M = product.co M_i$ give rise to projection maps
$pi_i: M -> M_i$, but $pi_i$ does _not_ act on $M_i$, and it is only after we
rewrite $M$ as an internal direct sum $M = op("⨁", limits: #true) N_i$,
$N_i tilde.equiv M_i$, that we can apply the preceding remarks.

Returning now to our study of Hom, we remark first that there are obvious
isomorphisms of additive groups
$
  cases(
    Hom_A lr((M plus.o M',L)) tilde.equiv
    Hom_A lr((M,L)) plus.o Hom_A lr((M',L))\,,
    Hom_A lr((L,M plus.o M')) tilde.equiv
    Hom_A lr((L,M)) plus.o Hom_A lr((L,M'))\,,
  )
$ <eq:hom-direct-sums>
for every left $A$-module $L$.

#source(43)
Somewhat less obvious is the following property of Hom:

#proposition[
  #enum(
    numbering: "(i)",
    [For each $A$-module $X$ and each $A$-exact sequence
      $ 0 -> L arrow.r^f M arrow.r^g N, $
      the sequence of additive groups
      $
        0 -> Hom_A lr((X,L)) arrow.r^(f_*) Hom_A lr((X,M))
        arrow.r^(g_*) Hom_A lr((X,N))
      $
      is also exact.],
    [For each $A$-module $Y$ and each $A$-exact sequence
      $ L arrow.r^f M arrow.r^g N -> 0, $
      there is an exact sequence of additive groups
      $
        0 -> Hom_A lr((N,Y)) arrow.r^(g^*) Hom_A lr((M,Y))
        arrow.r^(f^*) Hom_A lr((L,Y)).
      $],
  )
] <prop:hom-left-exact>

For proofs, see references listed at the end of
§@sec:hom-tensor-projective-injective-flat. We may remark that these exact
sequences of Hom's can be extended to the right, by introducing the groups Ext
defined in §@sec:ext-tor-cohomology.

To conclude this subsection, let us introduce the concepts of pushouts and
pullbacks of a pair of maps. Given a pair of left $A$-homomorphisms
$f_i: T -> M_i$, $i = 1,2$, we define a left $A$-module $X$, called the
_pushout_#idx(
  "pushout",
) of the pair ${f_1,f_2}$, by the formula
$ X = (M_1 plus.dot M_2) slash {(f_1 t,-f_2 t): t in T}. $
Thus the module $X$ is obtained from the external direct sum $M_1 plus.dot M_2$
by identifying the image of $T$ in $M_1$ with the image of $T$ in $M_2$. There
is a commutative _pushout diagram_ #numbered-block(
  pushout-diagram,
) <eq:pushout-diagram>
where $g_i$ is given by composition of maps: $M_i -> M_1 plus.dot M_2 -> X$,
$i = 1,2$.

#source(44)
Analogously, given a pair of $A$-homomorphisms $f_i: M_i -> U$, $i = 1,2$, we
can form their _pullback_ (or _fibre product_)#idx(
  "fibre product",
)#idx(
  "pullback",
)
$ Y = {(m_1,m_2) in M_1 plus.dot M_2: f_1 m_1 = f_2 m_2}. $
Then there is a commutative _pullback diagram_ #numbered-block(
  pullback-diagram,
) <eq:pullback-diagram>
where $g_i lr((m_1,m_2)) = m_i$, $i = 1,2$.

The concept of fibre products of rings is equally important. First let us recall
the definition of the _external direct product_#idx(
  "external direct product",
) $A times B$ of a pair of rings $A$ and $B$. This product consists of all
ordered pairs $(a,b)$, $a in A$, $b in B$, added and multiplied componentwise.
Clearly $A times B$ is a ring, and there are canonical maps
$ A -> A times B, quad A times B -> A, $
given by $a -> (a,1)$, $a in A$, and $(a,b) -> a$, $(a,b) in A times B$,
respectively. The first of these maps is an injection, the second a surjection.
This same construction may be used for any collection of rings ${A_i: i in I}$,
where the index set $I$ may possibly be infinite.

Now let $A_1,A_2$ and $overline(A)$ be rings, and let $f_i: A_i -> overline(A)$,
$i = 1,2$, be a pair of ring homomorphisms. (We assume always that ring
homomorphisms map identity elements onto identity elements). We now define the
_fibre product_ of the pair ${f_1,f_2}$ as
$ cal(A) = {(a_1,a_2): a_i in A_i, f_1 a_1 = f_2 a_2}. $
<eq:ring-fibre-product>
Then $cal(A)$ is a ring, and there is a commutative diagram
#commutative-square(
  $cal(A)$,
  $A_1$,
  $A_2$,
  $overline(A)$,
  $g_1$,
  $g_2$,
  $f_1$,
  $f_2$,
)
where $g_i lr((a_1,a_2)) = a_i$, $i = 1,2$.

#source(45)
Two examples of fibre products of rings arise often. First, let $I$ and $J$ be
two-sided ideals of an arbitrary ring $A$. Then there is a fibre product diagram
#numbered-block(ideal-fibre-product) <eq:ideal-fibre-product>
where all of the arrows represent canonical ring surjections. (We leave it to
the reader to verify that $A slash (I inter J)$ is isomorphic to the fibre
product of the pair ${f_1,f_2}$.)

Secondly, suppose that there is an inclusion of rings $A subset.eq B$, and that
$I$ is a two-sided ideal of $B$ contained in $A$. Then there is a fibre product
diagram #numbered-block(inclusion-fibre-product) <eq:inclusion-fibre-product>
in which $f_1$ is surjective, but $f_2$ usually not.

=== Tensor Products <ss:tensor-products>

Throughout this section let $A$ and $B$ be rings. We shall write
$attach(M, bl: A)$ to indicate that $M$ is a left $A$-module; likewise $L_A$
denotes a right $A$-module, and $attach(N, bl: A, br: B)$ a left $A$-, right
$B$-bimodule. Let us recall the definition of the tensor product #idx(
  "tensor product",
)$L times.o_A M$ of $L_A$ and $attach(M, bl: A)$. Denote by $F$ the free abelian
group generated by all ordered pairs from the Cartesian product $L times M$, and
let $F_0$ be the subgroup of $F$ generated by all expressions
$
  cases(
    (l_1+l_2,m)-(l_1,m)-(l_2,m)\,,
    (l,m_1+m_2)-(l,m_1)-(l,m_2)\,,
    (l,a m)-(l a,m)\,,
  )
$
for all $l_i in L$, $m_i in M$, $a in A$. We set $L times.o_A M = F slash F_0$,
an additive abelian group. Every element of $L times.o_A M$ is expressible as a
finite sum $sum l_i times.o m_i$, though not uniquely so.

In what follows, we shall often be discussing additive homomorphisms
$f': L times.o_A M -> G$, where $G$ is an abelian additive group. Obviously the
map $f'$ is completely determined once the images
${f'(l times.o m): l in L,m in M}$ are known.
#source(46)
The difficulty in constructing such homomorphisms $f'$ lies in proving that a
proposed mapping is well defined. In order to overcome this difficulty, we shall
need the characterization of $L times.o_A M$ in terms of a universal mapping
property, as described below.

Given a pair of modules $L_A$ and $attach(M, bl: A)$, and an abelian group $G$,
consider a map $f: L times M -> G$. Call $f$ a _balanced map_#idx(
  "balanced map",
) if
$
  cases(
    f(l_1+l_2,m)=f(l_1,m)+f(l_2,m)\,,
    f(l,m_1+m_2)=f(l,m_1)+f(l,m_2)\,,
    f(l,a m)=f(l a,m)
  )
$
for all $l_i in L$, $m_i in M$, $a in A$. The following result is shown in
@bib:CurtisReiner1962[CR §~12]:

#proposition[
  Each balanced map $f: L times M -> G$, where $G$ is an abelian group and
  $L_A$, $attach(M, bl: A)$ are modules, determines a unique additive
  homomorphism $f': L times.o_A M -> G$ such that
  $ f'(l times.o m)=f(l,m) quad "for all" l in L,m in M. $
] <prop:tensor-universal-mapping>

As an application of this result, let us show that $L times.o_A M$ is covariant
in each variable, that is, given $f in Hom_A lr((L,L_1))$ and
$g in Hom_A lr((M,M_1))$, there exists an additive homomorphism
$ f times.o g: L times.o M -> L_1 times.o M_1. $ <eq:tensor-induced-map>
(Here, the $L$'s are right $A$-modules, the $M$'s are left $A$-modules, and we
write $times.o$ instead of $times.o_A$ for convenience.) Consider the map
$ psi: L times M -> L_1 times.o M_1 $
defined by
$ psi(l, m)=f(l) times.o g(m), quad l in L,m in M. $
It is easily verified that $psi$ is a balanced map. Therefore by
@prop:tensor-universal-mapping, $psi$ determines an additive homomorphism
$psi': L times.o M -> L_1 times.o M_1$ such that
$psi'(l times.o m)=f(l) times.o g(m)$, $l in L$, $m in M$. Denoting $psi'$ by
$f times.o g$, we have obtained the desired homomorphism @eq:tensor-induced-map,
with
$ (f times.o g)(l times.o m)=f(l) times.o g(m), quad l in L,m in M. $
Since we know that $f times.o g$ is well defined, we also have
$ (f times.o g){sum l_i times.o m_i}=sum f(l_i) times.o g(m_i) $
for every finite sum $sum l_i times.o m_i$, $l_i in L$, $m_i in M$. However, it
would not have been
#source(47)
permissible to just define $f times.o g$ by this last formula, since we would
then have had to prove that if $sum l_i times.o m_i = sum l'_j times.o m'_j$ in
$L times.o M$, then $sum f(l_i) times.o g(m_i)=sum f(l'_j) times.o g(m'_j)$. The
use of @prop:tensor-universal-mapping avoids this difficulty.

Suppose next that $attach(L, bl: B, br: A)$ is a bimodule, and
$attach(M, bl: A)$ a module. Then $L times.o_A M$ may be made into a left
$B$-module, since $L$ is a left $B$-module occurring in a covariant position.
Specifically, we have
$ b(l times.o m)=b l times.o m, quad b in B,l in L,m in M. $
We omit the obvious argument that this formula gives a well defined action of
$B$ on the additive group $L times.o_A M$, and that $L times.o_A M$ becomes a
left $B$-module.

In particular, the ring $A$ is itself an $(A,A)$-bimodule. Hence for each left
$A$-module $M$, there is a left $A$-module structure on $A times.o M$, given by
the formula
$
  a(x times.o m)=a x times.o m, quad a in A,
  x in attach(A, bl: A, br: A),m in M.
$
As is well known (see @bib:CurtisReiner1962[CR §~12]), there is a natural
isomorphism of left $A$-modules:
$ A times.o M tilde.equiv M, $ <eq:tensor-regular-module>
determined by the map $a times.o m -> a m$, $a in A$, $m in M$. [To be precise,
the balanced map $psi: A times M -> M$ given by $psi(a, m)=a m$, determines an
additive homomorphism $psi': A times.o M -> M$ such that
$psi'(a times.o m)=a m$. Then $psi'$ is a left $A$-isomorphism.]

We list without proof a pair of isomorphism formulas:
$
  cases(
    (L plus.o L') times.o M tilde.equiv
    (L times.o M) plus.o (L' times.o M)\,,
    L times.o (M plus.o M') tilde.equiv
    (L times.o M) plus.o (L times.o M').
  )
$
In fact, a stronger result holds true: given any family ${L_alpha}$ of right
$A$-modules, and any left $A$-module $M$, there is a natural isomorphism of
additive groups:
$
  (product.co_alpha L_alpha) times.o_A M tilde.equiv
  product.co_alpha (L_alpha times.o_A M).
$ <eq:tensor-direct-sums>
A corresponding result holds for expressions of the type
$L times.o product.co M_beta$.

The following basic result is easily proved (see @bib:CurtisReiner1962[CR
  §~12]):

#proposition(title: [Associativity of tensor products])[
  Given rings $A$ and $B$, and the data $L_A$, $attach(M, bl: A, br: B)$,
  $attach(N, bl: B)$, there is a natural isomorphism of additive groups
  $ (L times.o_A M) times.o_B N tilde.equiv L times.o_A (M times.o_B N), $
  determined by the formula $(l times.o m) times.o n -> l times.o (m times.o n)$
  for all $l in L$, $m in M$, $n in N$.
] <prop:tensor-associativity>

#source(48)
This proposition will play a basic role in our later discussion of induced
representations of groups, since it implies at once that the induction map is
transitive (see @prop:induction-transitive). Equally important will be the
following “adjointness” formula connecting Hom and $times.o$, since it will
imply the Frobenius reciprocity law for group representations (see
@th:frobenius-reciprocity).

#theorem(name: "Adjointness Theorem")[
  Given rings $A$ and $B$, and the data $attach(L, bl: A)$,
  $attach(M, bl: B, br: A)$, $attach(N, bl: B)$, there is a natural isomorphism
  $
    tau: Hom_A lr((L,Hom_B lr((M,N)))) tilde.equiv
    Hom_B lr((M times.o_A L,N))
  $
  of additive groups, given by the formula
  $ (tau f)(m times.o l)=f_l lr((m)), quad m in M,l in L, $
  where $f$ ranges over all elements of $Hom_A lr((L,Hom_B lr((M,N))))$, and
  $f_l$ denotes the image of $l$ under the map $f$.
] <th:hom-tensor-adjointness>
#idx(
  "Adjointness Theorem",
  target: [@th:hom-tensor-adjointness],
)

#proof(head: emph[Sketch of Proof.])[
  First verify that $Hom_B lr((M,N))$ is a left $A$-module, and that
  $M times.o_A L$ is a left $B$-module. Then check that $tau f$ is well defined.
  Finally, show that $tau$ has an inverse $lambda$ defined as follows: for each
  $g in Hom_B lr((M times.o_A L,N))$, let
  $ {(lambda g)_l}m = g(m times.o l), quad m in M,l in L. $
  Here, $(lambda g)_l$ denotes the image of $l$ under the map $lambda g$.
]

[For those familiar with category theory, we may remark that the preceding
result asserts that the functor $M times.o_A dot$ is left adjoint to
$Hom_B lr((M,dot))$. The first of these functors carries left $A$-modules to
left $B$-modules, while the second functor does the opposite.]

To conclude this subsection, let us state the analogue of @prop:hom-left-exact
for tensor products; for proofs, see Rotman~@bib:Rotman1979, or do as exercise.

#proposition[
  #enum(
    numbering: "(i)",
    [Given an exact sequence of left $A$-modules
      $L arrow.r^f M arrow.r^g N -> 0$, and given any right $A$-module $X$, the
      sequence of additive groups
      $
        X times.o_A L arrow.r^(1 times.o f) X times.o_A M
        arrow.r^(1 times.o g) X times.o_A N -> 0
      $
      is exact.],
    [#source(49)
      Given an exact sequence of right $A$-modules $U -> V -> W -> 0$, and given
      any left $A$-module $L$, the sequence
      $ U times.o_A L -> V times.o_A L -> W times.o_A L -> 0 $
      is an exact sequence of additive groups.],
  )
] <prop:tensor-right-exact>

=== Categories and Functors <ss:categories-functors>

We shall introduce here some ideas and terminology from category theory, since
the language of category theory provides a clarifying and unifying approach to
the ideas introduced earlier in this section, as well as to other areas of
mathematics. For simplicity, we shall deal only with categories of modules over
a ring, and subcategories thereof. For a ring $A$, denote by $frak(M)_A$ the
_category of right $A$-modules_#idx(
  "category",
)\; the _objects_ of $frak(M)_A$ are right $A$-modules. For each pair of objects
$M,N in frak(M)_A$, there is a set of _morphisms_#idx(
  "morphism",
) (or _maps_) from $M$ to $N$, namely $Hom_A lr((M,N))$. In the same way, we can
speak of the category $attach(frak(M), bl: A)$ of left $A$-modules, the category
$attach(frak(M), bl: A, br: B)$ of $A,B$-bimodules, or the category
$frak(A) frak(B)$ of abelian groups.

Now let $frak(A)$ be a category with objects $A,A'$, etc., and $frak(B)$ a
category with objects $B,B'$, etc. A _covariant functor_#idx(
  "covariant",
)#idx(
  "functor",
) $F: frak(A) -> frak(B)$ assigns to each object $A in frak(A)$ an object
$F A in frak(B)$, and carries each $alpha in Hom_(frak(A)) lr((A,A'))$ onto a
map $F alpha in Hom_(frak(B)) lr((F A,F A'))$, in such a way as to preserve
identity maps and compositions of maps. We assume always that the functor is
_additive_#idx(
  "additive functor",
), that is, $F(alpha+alpha')=F alpha+F alpha'$.

For example, let $X in attach(frak(M), bl: A)$ be fixed, and define a functor
$F: attach(frak(M), bl: A) -> frak(A) frak(B)$ by setting
$F M = Hom_A lr((X,M))$ for each left $A$-module $M$. We must also describe the
action of $F$ on maps. For each $alpha in Hom_A lr((M,N))$, let
$F alpha: F M -> F N$ be the map denoted by $alpha_*$ (see
@eq:hom-covariant-map). It is easily checked that $F$ is a covariant functor; it
is often denoted symbolically by $Hom_A lr((X,*))$ or $Hom_A lr((X,dot))$.

As another example of a covariant functor, let $X in attach(frak(M), bl: A)$ be
fixed, and define $G: frak(M)_A -> frak(A) frak(B)$ by setting
$G M = M times.o_A X$ for each right $A$-module $M$. The action of $G$ on maps
is easily defined; namely, for each $alpha in Hom_A lr((M,N))$ we set
$G alpha: G M -> G N$, where $G alpha = alpha times.o 1$. We denote $G$
symbolically by $* times.o_A X$.

It is also necessary to consider _contravariant functors_#idx(
  "contravariant",
) $F: frak(A) -> frak(B)$. Such an $F$ assigns to each $A in frak(A)$ an object
$F A in frak(B)$, and carries each $alpha in Hom_(frak(A)) lr((A,A'))$ onto a
map $F alpha in Hom_(frak(B)) lr((F A',F A))$, in such a way as to preserve
identity maps, but reversing compositions (that is,
$F(alpha beta)=F(beta)F(alpha)$ for maps $alpha,beta$). As usual, we assume
always that $F$ is additive. As an example of a contravariant functor
$F: attach(frak(M), bl: A) -> frak(A) frak(B)$, we cite the following: fix a
module $X in attach(frak(M), bl: A)$, and for each left $A$-module $M$ let
$F M = Hom_A lr((M,X))$. To each $alpha in Hom_A lr((M,N))$ we let correspond
the map $F alpha in Hom_A lr((F N,F M))$, where $F alpha$ is the map $alpha^*$
defined as in @eq:hom-contravariant-map. Then $F$ is a contravariant functor,
usually denoted by $Hom_A lr((*,X))$.

#source(50)
A covariant functor $F: frak(A) -> frak(B)$ is called _right exact_#idx(
  "right exact",
) if for each exact sequence $A_1 -> A_2 -> A_3 -> 0$ in $frak(A)$, the sequence
$F A_1 -> F A_2 -> F A_3 -> 0$ is exact in $frak(B)$.
Proposition~@prop:tensor-right-exact is just the assertion that the functors
$X times.o_A *$ and $* times.o_A L$ are right exact. Analogously, a
contravariant functor $G: frak(A) -> frak(B)$ is _right exact_ if the exactness
of $0 -> A_1 -> A_2 -> A_3$ implies that of $G A_3 -> G A_2 -> G A_1 -> 0$.

On the other hand, the covariant functor $F: frak(A) -> frak(B)$ is _left
exact_#idx(
  "left exact",
) if the exactness of $0 -> A_1 -> A_2 -> A_3$ implies that of
$0 -> F A_1 -> F A_2 -> F A_3$. Proposition~@prop:hom-left-exact (i) asserts
that the functor $Hom_A lr((X,*))$ is left exact. Likewise, a contravariant
functor $G: frak(A) -> frak(B)$ is _left exact_ if the exactness of
$A_1 -> A_2 -> A_3 -> 0$ implies that of $0 -> G A_3 -> G A_2 -> G A_1$. By
Proposition~@prop:hom-left-exact (ii), $Hom_A lr((*,Y))$ is a left exact
contravariant functor from $attach(frak(M), bl: A)$ to $frak(A) frak(B)$.

Finally, an _exact functor_#idx(
  "exact functor",
) is one which is both left and right exact. It is easily shown (see references)
that the following holds true:

#proposition[
  Let $F: frak(A) -> frak(B)$ be a functor. The following conditions are
  equivalent:
  #enum(
    numbering: "(i)",
    [$F$ is exact.],
    [$F$ preserves exactness of short exact sequences.],
    [$F$ preserves exactness of all exact sequences.],
  )
] <prop:exact-functor-criteria>

#proof(head: emph[Sketch of Proof.])[
  The implications (i)$arrow.r.double$(ii) and (iii)$arrow.r.double$(i) are
  obvious, and we need only prove that (ii)$arrow.r.double$(iii). Assume (ii),
  and let $A_1 arrow.r^alpha A_2 arrow.r^beta A_3$ be exact in $frak(A)$; we
  must show that
  $ F A_1 arrow.r^(F alpha) F A_2 arrow.r^(F beta) F A_3 $
  is exact in $frak(B)$. Consider the commutative diagram with exact rows and
  #exact-functor-diagram
  where each $i$ is an inclusion map. Since $F$ preserves exactness of short
  exact sequences, when we apply the functor $F$ to this diagram we obtain a new
  commutative diagram in $frak(B)$, with exact rows and exact columns. It is
  then trivial to check that $ker F beta = im F alpha$, which completes the
  proof.
]

#source(51)
#heading(level: 3)[
  Projective, Injective, and Flat Modules
] <ss:projective-injective-flat-modules>

Throughout this section let $A$ be a ring, and let the term “$A$-module” mean
“left $A$-module”, unless explicitly stated otherwise. An $A$-module $F$ is said
to have a _free $A$-basis_#idx(
  "free basis",
) ${x_alpha}$, where $alpha$ ranges over some index set, if there exist elements
$x_alpha in F$ such that each $x in F$ is expressible as a finite sum
$sum a_alpha x_alpha$ with uniquely determined coefficients $a_alpha in A$. Such
modules $F$ are called _free $A$-modules_#idx(
  "free module",
). Thus, $F$ is $A$-free if and only if $F$ is isomorphic to a direct sum of
copies of $attach(A, bl: A)$.

A _projective $A$-module_#idx(
  "projective module",
) is a direct summand of a free module; every free module is of course
projective, but the converse need not hold for arbitrary rings $A$. If ${M_i}$
is any family of $A$-modules, it is immediate from the definition of projective
modules that the direct sum $product.co M_i$ is projective if and only if each
$M_i$ is projective.

We may observe next that every $A$-module $M$ is a homomorphic image of some
free module $F$. In fact, we need only choose any set of elements $m_alpha in M$
such that $M = sum A m_alpha$; now let $F$ be free with basis ${x_alpha}$, and
define the surjection $psi: F -> M$ by letting $psi(x_alpha) = m_alpha$ for each
$alpha$. We also remark that if $M$ is finitely generated as $A$-module, then
the free module $F$ may be chosen free with a finite basis.

We state without proof (see references):

#proposition[
  Let $P$ be any $A$-module. The following conditions are equivalent:
  #enum(
    numbering: "(i)",
    [$P$ is projective.],
    [Every short exact sequence $0 -> X -> Y -> P -> 0$ of $A$-modules must
      split.],
    [For each diagram with exact bottom row
      #projective-lifting
      there exists an $A$-homomorphism $h$ such that $f = g h$.],
    [For each surjection $g: X -> Y$, the induced map
      $ g_*: Hom_A lr((P,X)) -> Hom_A lr((P,Y)) $
      is also surjective.],
    [The functor $Hom_A lr((P,*))$ is exact.],
  )
] <prop:projective-module-criteria>

#source(52)
#remark(numbered: true)[
  The preceding result may be sharpened slightly in the case where $P$ is a
  finitely generated $A$-module. In this case, $P$ is projective if and only if
  every short exact sequence $0 -> X -> Y -> P -> 0$, in which $Y$ is finitely
  generated, is $A$-split.
] <rem:finitely-generated-projective-criterion>

For later use, we prove:

#lemma(name: "Schanuel's Lemma")[
  Given two short exact sequences of left $A$-modules
  $
    0 -> M -> P arrow.r^f X -> 0, quad
    0 -> M' -> P' arrow.r^g X -> 0
  $
  in which $P$ and $P'$ are projective, there is an $A$-isomorphism
  $ M' plus.o P tilde.equiv M plus.o P'. $
] <lem:schanuel>
#idx(
  "Schanuel's Lemma",
  target: [@lem:schanuel],
)

#proof[
  Let $Y$ be the pullback of the pair of maps ${f,g}$ (see
  @eq:pullback-diagram), so there is a commutative diagram
  #commutative-square($Y$, $P$, $P'$, $X$, $g_1$, $f_1$, $f$, $g$)
  By Exercise~@exc:pullback-kernel, it follows that $ker g_1 tilde.equiv ker g$,
  and that $g_1$ is surjective. An analogous result holds for $f_1$. Thus there
  are exact sequences
  $
    0 -> M' -> Y arrow.r^(g_1) P -> 0, quad
    0 -> M -> Y arrow.r^(f_1) P' -> 0.
  $
  Since $P$ and $P'$ are projective, both sequences are $A$-split, and hence
  $ Y tilde.equiv M' plus.o P tilde.equiv M plus.o P'. $
  This completes the proof.
]

Next we turn to the concept of _injective_ modules, dual to that of projective
modules. A module $Q$ is called _injective_#idx(
  "injective module",
) if every short exact sequence $0 -> Q -> X -> Y -> 0$ is split. We state
without proof (see references):

#proposition[
  Let $Q$ be a left $A$-module. The following are equivalent:
  #enum(
    numbering: "(i)",
    [$Q$ is injective.],
    [Every short exact sequence $0 -> Q -> X -> Y -> 0$ must split.],
    [#source(53)
      For each diagram with exact top row
      #injective-extension
      there exists an $h$ such that $g = h f$.],
    [For each injection $f in Hom_A lr((X,Y))$, the induced map
      $f^*: Hom_A lr((Y,Q)) -> Hom_A lr((X,Q))$ is surjective.],
    [The functor $Hom_A lr((*,Q))$ is exact.],
    [For every left ideal $I$ of $A$ and every $g in Hom_A lr((I,Q))$, there
      exists an $h in Hom_A lr((A,Q))$ such that $g = h|_I$ (the restriction of
      $h$ to $I$).],
  )
] <prop:injective-module-criteria>

#remarks(numbered: true)[
  #enum(
    numbering: "(i)",
    [In the preceding proposition, condition (ii) is just the restatement of the
      definition of injectivity, and is included for convenience.],
    [Proposition~@prop:injective-module-criteria is somewhat more difficult to
      prove than the corresponding Proposition~@prop:projective-module-criteria
      for projective modules. In particular, the equivalence of (iii) and (vi)
      is proved by an appeal to Zorn's Lemma.],
    [Given any family ${M_i}$ of $A$-modules, it is easily shown that the
      _direct product_ $product M_i$ is injective if and only if each $M_i$ is
      injective. From this it follows at once that $M_1 plus.o M_2$ is injective
      if and only if both $M_1$ and $M_2$ are injective.],
    [We showed earlier that every module $M$ can be expressed as a homomorphic
      image of a projective module (and, indeed, of a free module). The dual
      statement also holds true:

      _Every $A$-module can be embedded in an injective module._ (For proof, see
      @bib:CurtisReiner1962[CR §~57]).],
  )
] <rem:injective-modules>

We shall need the dual of @rem:finitely-generated-projective-criterion:

#proposition[
  Let $E$ be a finitely generated $A$-module. Then $E$ is injective if and only
  if every short exact sequence
  $ 0 -> E -> X -> Y -> 0, $
  in which $X$ and $Y$ are finitely generated, is necessarily $A$-split.
] <prop:finitely-generated-injective-criterion>

#source(54)
#proof[
  If $E$ is injective, every such sequence splits by
  @prop:injective-module-criteria. Conversely, suppose each such sequence
  splits, and consider a diagram
  #ideal-extension
  in which $i$ is the inclusion map, and $g in Hom_A lr((I,E))$. If $X$ denotes
  the pushout of the pair of maps ${i,g}$, then using
  Exercise~@exc:pushout-cokernel, we obtain a commutative diagram
  #injectivity-pushout
  with exact rows. Since $X$ is a quotient of $E plus.o A$, it is clear that $X$
  is finitely generated as $A$-module. By hypothesis, the bottom row in the
  above diagram is $A$-split. Hence, there exists a map $p in Hom_A lr((X,E))$
  such that $p i' = 1_E$. But then $p g' in Hom_A lr((A,E))$ is such that
  $(p g')i = g$, so we have lifted the map $g$:
  #ideal-extension-lifted
  Hence by @prop:injective-module-criteria (vi) it follows that $E$ is
  injective. This completes the proof.
]

We turn next to the concept of _flatness_#idx(
  "flat",
): a left $A$-module $X$ is _flat_ if $* times.o_A X$ is an exact functor, that
is, for each exact sequence
$ L arrow.r^f M arrow.r^g N $
of right $A$-modules, the sequence of additive groups
$
  L times.o_A X arrow.r^(f times.o 1) M times.o_A X
  arrow.r^(g times.o 1) N times.o_A X
$
is also exact. Let us prove at once that every projective module is flat; this
#source(55)
result is useful, but even more important is the type of reasoning used in the
proof.

#proposition[
  Every projective module is flat.
] <prop:projective-is-flat>

#proof[
  By virtue of the isomorphism $M times.o A tilde.equiv M$ (see
  @eq:tensor-regular-module), it follows at once that the left $A$-module
  $attach(A, bl: A)$ is flat. Since “tensor product commutes with direct sum” by
  @eq:tensor-direct-sums, we deduce that every free module is flat. Now let $X$
  be any projective left $A$-module; then $X$ is a direct summand of some free
  module $F$, and we may write $F = X plus.o X'$ (internal direct sum) for some
  module $X'$.

  Next let $L arrow.r^f M arrow.r^g N$ be an exact sequence of right
  $A$-modules. We have
  $L times.o F tilde.equiv L times.o X plus.o L times.o X'$, where $times.o$
  means $times.o_A$. Hence there is a commutative diagram
  #flat-summand-diagram
  where the vertical maps are isomorphisms, and where
  $
    phi = f times.o 1_X plus.o f times.o 1_(X'), quad
    psi = g times.o 1_X plus.o g times.o 1_(X').
  $
  Since the top row is exact (because $F$ is flat), it follows that the bottom
  row is also exact. Therefore the sequence
  $ L times.o X -> M times.o X -> N times.o X $
  is exact, and so $X$ is flat.
]

As another illustration of this method of reasoning, we prove

#proposition[
  Let $L$ be a finitely generated projective right $A$-module, and let $M$ be
  any right $A$-module. Then there is a natural isomorphism of additive groups
  $ L times.o_A Hom_A lr((M,A)) tilde.equiv Hom_A lr((M,L)), $
  <eq:projective-hom-tensor>
  given thus: for each $x in L$ and $f in Hom_A lr((M,A))$, we map
  $x times.o f in L times.o Hom_A lr((M,A))$ onto the element
  $[x,f] in Hom_A lr((M,L))$, where
  $ [x,f]m = x dot f(m), quad m in M. $ <eq:projective-hom-tensor-map>
] <prop:projective-hom-tensor>

#source(56)
#proof[
  Observe first that $Hom_A lr((M_A,attach(A, bl: A, br: A)))$ is a left
  $A$-module, since Hom is covariant in the second variable. Next, both sides of
  @eq:projective-hom-tensor represent covariant (additive) functors of $L$, that
  is, for fixed $M$ the functors
  $ Hom_A lr((M,*)) "and" * times.o_A Hom_A lr((M,A)) $
  are covariant functors from $frak(M)_A$ to $frak(A) frak(B)$. As in the proof
  of @prop:projective-is-flat, it follows that @eq:projective-hom-tensor is
  valid for a direct sum $L plus.o L'$ if and only if it holds for both $L$ and
  $L'$.

  Now @eq:projective-hom-tensor holds true when $L = A_A$, by virtue of the
  isomorphisms given in @eq:hom-regular-module and @eq:tensor-regular-module. Of
  course, one must verify that these isomorphisms agree with the map defined by
  @eq:projective-hom-tensor-map, but we shall omit this routine calculation. By
  the remarks in the preceding paragraph, it follows that
  @eq:projective-hom-tensor holds whenever $L$ is a free $A$-module on a finite
  basis. But then @eq:projective-hom-tensor is true for every finitely generated
  projective right $A$-module $L$, since each such $L$ is a direct summand of a
  free module on a finite basis.

  [We caution the reader that @eq:projective-hom-tensor need not hold when $L$
  is not finitely generated.]
]

The same method of proof yields
$ Hom_A lr((M,A)) times.o_A L tilde.equiv Hom_A lr((M,L)) $
<eq:left-projective-hom-tensor>
if $M,L$ are left $A$-modules, with $M$ finitely generated and projective.

We have shown above that every projective module is flat. However, in later work
we shall need to know that every torsionfree module over a Dedekind ring is flat
(see Exercise~@exc:dedekind-torsionfree-flat), and such modules need not be
projective. A key step in proving this needed result is the following
proposition, valid for arbitrary rings $A$.

#proposition[
  A right $A$-module $X$ is flat if every f.g. submodule of $X$ is flat.
] <prop:flat-from-finitely-generated-submodules>

#proof[
  Let $times.o$ denote $times.o_A$, and suppose that each f.g. submodule of $X$
  is flat. In order to prove that $X$ is flat, it suffices to show (by virtue of
  @prop:exact-functor-criteria) that for each inclusion $i: L -> M$ of left
  $A$-modules, the map
  $ 1 times.o i: X times.o L -> X times.o M $
  is injective.

  By §@ss:tensor-products, the tensor product $X times.o M$ may be defined as
  $F slash F_0$, with $F$ the free abelian group generated by all ordered pairs
  $(x,m)$, $x in X$, $m in M$, and where $F_0$ is the subgroup of $F$ generated
  by expressions of the form $(x+x',m)-(x,m)-(x',m)$, and so on. Now let
  $ u = sum_(j=1)^r x_j times.o l_j in X times.o L $
  #source(57)
  be such that $(1 times.o i)u = 0$ in $X times.o M$. Then
  $sum (x_j,i(l_j)) in F_0$, and so $sum (x_j,i(l_j))$ may be expressed as a
  finite sum, each term of which is $plus.minus 1$ times a generator of $F_0$.
  These terms involve only finitely many elements of $X$; let $X'$ be the
  submodule of $X$ generated by these elements, together with the elements
  $x_1,dots,x_r$ occurring in $u$. Let $u' = sum x_j times.o l_j$, viewed as an
  element of $X' times.o L$. The above discussion implies at once that the map
  $psi: X' times.o L -> X' times.o M$ carries $u'$ onto the zero element of
  $X' times.o M$. But $psi$ is injective since $X'$ is flat by hypothesis, and
  hence $u' = 0$. However, $u'$ maps onto $u$ under the map
  $X' times.o L -> X times.o L$. Thus $u = 0$, which completes the proof that
  $1 times.o i$ is injective, and establishes the proposition.
]

#corollary[
  Every torsionfree module over a P.I.D.#footnote[P.I.D. is an abbreviation for
    “principal ideal domain”.] is flat.
] <cor:pid-torsionfree-flat>

#proof[
  Let $R$ be a (commutative) P.I.D., and $X$ any torsionfree $R$-module (that
  is, $r x = 0 arrow.r.double r = 0$ or $x = 0$, for $r in R$, $x in X$). To
  prove $X$ flat, we need show that each f.g. submodule $X'$ of $X$ is flat. But
  $X'$ is torsionfree, and by the Structure Theorem for f.g. modules over a
  P.I.D. (see @bib:CurtisReiner1962[CR §~16]) it follows that $X'$ is a free
  $R$-module. Hence $X'$ is flat by @prop:projective-is-flat. This completes the
  proof.
]

As an example, we note that $QQ$ is a flat $ZZ$-module. Indeed, every
torsionfree $ZZ$-module is flat.

The concept of flatness plays an important role in the “Change of Rings” Theorem
given below (see @th:change-of-rings). In order to state this theorem, we need a
number of definitions which are important in their own right. We recall the
following (see @def:algebra-over-commutative-ring):

#definition[
  Let $R$ be a commutative ring. An arbitrary ring $A$ is called an
  _$R$-algebra_ if there exists a ring homomorphism $psi: R -> "center of" A$.
  Using $psi$, every $A$-module (including $A$ itself) may be viewed as
  $R$-module.
] <def:algebra-recalled>

If $A$ is a left noetherian ring, then for each f.g. left $A$-module $M$ there
is an exact sequence
$ A^((s)) -> A^((r)) -> M -> 0, $ <eq:finite-presentation>
with $r,s$ positive integers. Even when $A$ is not necessarily noetherian, there
may be such a sequence for $M$; in such case, we call $M$ _finitely
presented_#idx(
  "finitely presented",
). We emphasize that when $A$ is left noetherian, every f.g. left $A$-module is
necessarily finitely presented.

Now let $A$ and $B$ be $R$-algebras, where $R$ is a commutative ring, and let
$M,N$ be left $A$-modules. We set
$ A' = B times.o_R A, quad M' = B times.o_R M, $
#source(58)
so $M'$ is a left module over the $R$-algebra $A'$. There exists an
$R$-homomorphism
$ alpha: B times.o_R Hom_A lr((M,N)) -> Hom_(A') lr((M',N')), $
<eq:change-of-rings-map>
given by
$ alpha(b times.o f)=b_r times.o f, quad b in B,f in Hom_A lr((M,N)), $
where $b_r$ denotes right multiplication by $b$ acting on $B$. There are
bimodule structures $attach(B, bl: B, br: R)$ and $attach((M'), bl: A', br: B)$,
so that both sides of @eq:change-of-rings-map have the structure of left
$B$-modules. Likewise, the bimodule structures#footnote[The notation $B_(B,R)$
  indicates that $B$ is a right $B$-, right $R$-bimodule.] $B_(B,R)$ and
$attach((N'), bl: A', br: B)$ make the expressions in @eq:change-of-rings-map
into right $B$-modules. It is easily verified that the map $alpha$ defined in
@eq:change-of-rings-map is a two-sided $B$-homomorphism.

#theorem(title: [Change of rings])[
  Let $A$ and $B$ be $R$-algebras, where $R$ is a commutative ring, and let $M$
  and $N$ be left $A$-modules. Put $A' = B times.o_R A$, $M' = B times.o_R M$,
  and let
  $ alpha: B times.o_R Hom_A lr((M,N)) -> Hom_(A') lr((M',N')) $
  be the two-sided $B$-homomorphism defined in @eq:change-of-rings-map. Assume
  that $B$ is a flat $R$-module.
  #enum(
    numbering: "(i)",
    [If $M$ is finitely generated as left $A$-module, then $alpha$ is a
      monomorphism.],
    [If $M$ is finitely presented as left $A$-module, then $alpha$ is an
      isomorphism.],
  )
] <th:change-of-rings>
#idx(
  "Change of Rings Theorem",
  target: [@th:change-of-rings],
)

For the proof, see @bib:Reiner1975[MO §~2e]. The result is often applied in the
special case where $B$ is some commutative ring $R'$ containing $R$. For
example, suppose that $R$ is an integral domain and $R'$ is some ring of
quotients of $R$ (see §@ss:localization). Then $R'$ is necessarily $R$-flat, and
we obtain
$ R' times.o_R Hom_A lr((M,N)) tilde.equiv Hom_(A') lr((M',N')) $
<eq:hom-localization>
if $A$ is a left noetherian $R$-algebra, and $M$ is a finitely presented
$A$-module. Here, $A' = R' times.o_R A$, $M' = R' times.o_R M$.

We list here some standard references on Homological Algebra:

#reference-list(
  [Properties of Hom:],
  [Rotman~@bib:Rotman1979.],
  [Tensor products:],
  [Curtis–Reiner~@bib:CurtisReiner1962.],
  [Ext and Tor:],
  [Cartan–Eilenberg~@bib:Cartan1956, Rotman~@bib:Rotman1979.],

  [Cohomology of groups:],
  [preceding list, and also Babakhanian~@bib:Babakhanian1972,
    Gruenberg~@bib:Gruenberg1970, Weiss~@bib:Weiss1969.],
)

#source(59)
#exercises-heading

#exercise[
  Given a ring $A$ and left $A$-modules $L,M,X,Y$, let $f in Hom_A lr((L,M))$,
  $g in Hom_A lr((X,Y))$. Show that for all $alpha in Hom_A lr((M,X))$,
  $ g_* f^* alpha = f^* g_* alpha = g alpha f, $
  where $f^*,g_*$ are defined as in @eq:hom-contravariant-map and
  @eq:hom-covariant-map.
] <exc:hom-commuting-induced-maps>

#exercise[
  Given a pushout diagram @eq:pushout-diagram, show that $g_1$ induces an
  isomorphism: $"cok" f_1 tilde.equiv "cok" g_2$. Show also that if $f_1$ is
  injective, then so is $g_2$.
] <exc:pushout-cokernel>

#exercise[
  Given a pullback diagram @eq:pullback-diagram, prove that $g_2$ induces an
  isomorphism: $ker g_1 tilde.equiv ker f_2$. Show also that if $f_2$ is
  surjective, then so is $g_1$.
] <exc:pullback-kernel>

#exercise[
  Using the method of proof of @th:hom-tensor-adjointness, show that for rings
  $A,B$ and data $L_A$, $attach(M, bl: A, br: B)$, $N_B$, there is a natural
  isomorphism
  $
    Hom_A lr((L,Hom_B lr((M,N)))) tilde.equiv
    Hom_B lr((L times.o_A M,N)).
  $
] <exc:right-hom-tensor-adjointness>

#exercise[
  Prove the _Snake Lemma:#idx(
    "Snake Lemma",
  ) Given a commutative diagram of modules, with exact rows:_
  #snake-diagram
  _there is an exact sequence_
  $
    ker alpha arrow.r^(rho_*) ker beta -> ker gamma arrow.r^delta
    "cok" alpha -> "cok" beta arrow.r^(sigma_*) "cok" gamma.
  $
  _Further, if $rho$ is injective so is $rho_*$; if $sigma$ is surjective, so is
  $sigma_*.$_

  #hint([@exc:snake-lemma])[
    Define $delta$ by $delta(c)=a' + im alpha$, where
    $ a' -> b', quad b' = beta(b), quad b -> c. $
  ]
] <exc:snake-lemma>

#exercise[
  Let $R$ be a commutative noetherian ring, and let $A$ be an $R$-algebra as in
  @def:algebra-recalled. Suppose that $A$ is f.g. as $R$-module, and let $M,N$
  be f.g. left $A$-modules. Show that $Hom_A lr((M,N))$ is f.g./$R$.

  #hint([@exc:hom-finitely-generated-over-base])[
    $Hom_A lr((M,N))$ is an $R$-submodule of $Hom_R lr((M,N))$, and both $M,N$
    are f.g./$R$. If $R^((k)) -> M -> 0$ is $R$-exact, then so is
    $ 0 -> Hom_R lr((M,N)) -> Hom_R lr((R^((k)),N)). $
    The last term is isomorphic to $N^((k))$ as $R$-module, hence is f.g./$R$.
  ]
] <exc:hom-finitely-generated-over-base>

#exercise[
  Let $A$ be a finite dimensional algebra over a field $K$, and let $M$ be any
  f.g. left
  #source(60)
  $A$-module. For any field $E$ containing $K$, define
  $ A^E = E times.o_K A, quad M^E = E times.o_K M, $
  so $A^E$ is a finite dimensional $E$-algebra and $M^E$ is a f.g. left
  $A^E$-module. Let $N$ be any left $A$-module. Show that
  $
    E times.o_K Hom_A lr((M,N)) tilde.equiv
    Hom_(A^E) lr((M^E,N^E))
  $ <eq:hom-field-extension>
  as vector spaces over $E$.

  #hint([@exc:hom-field-extension])[
    Use @th:change-of-rings with $R=K$, $B=E$. A direct proof may be found in
    @bib:CurtisReiner1962[CR (29.5)].
  ]
] <exc:hom-field-extension>

#exercise[
  Prove that @eq:hom-field-extension remains valid even when $dim_K lr((A))$ is
  infinite, provided we assume that $M$ and $N$ are $A$-modules of finite
  dimension over $K$.

  #hint([@exc:hom-field-extension-finite-modules])[
    For each $a in A$, let $a_l$ denote left multiplication by $a$ on the
    $A$-module $M plus.o N$. Then $M$ and $N$ are $A_l$-modules, and
    $Hom_A lr((M,N)) = Hom_(A_l) lr((M,N))$. Further, $dim_K lr((A_l))$ is
    finite. Now use the preceding exercise with $A_l$ in place of $A$.
  ]
] <exc:hom-field-extension-finite-modules>

#exercise[
  Let $A$ be a $K$-algebra, where $K$ is a field, and let $M$ be a left
  $A$-module such that $dim_K lr((M))$ is finite. Let $E$ be any field
  containing $K$. Prove that there is an isomorphism of $E$-algebras:
  $ End_(A^E) lr((M^E)) tilde.equiv E times.o_K End_A lr((M)). $
  <eq:endomorphism-field-extension>
] <exc:endomorphism-field-extension>

#exercise[
  Given a pushout diagram @eq:pushout-diagram, show that the pushout $X$ has the
  following universal mapping property: for every commutative diagram
  #commutative-square($T$, $M_1$, $M_2$, $V$, $f_1$, $f_2$, $h_1$, $h_2$)
  there is a unique $A$-homomorphism $h: X -> V$ such that
  #pushout-universal
  commutes.
] <exc:pushout-universal>

#exercise[
  Given a pullback diagram @eq:pullback-diagram, show that the pullback $Y$ has
  the following
  #source(61)
  universal mapping property: for every commutative diagram
  #commutative-square($W$, $M_1$, $M_2$, $U$, $h_1$, $h_2$, $f_1$, $f_2$)
  there is a unique $A$-homomorphism $h: W -> Y$ such that
  #pullback-universal
  commutes.
] <exc:pullback-universal>

#exercise[
  Let
  #factorization-initial
  be a commutative diagram of left $A$-modules and $A$-homomorphisms, with exact
  rows. Let $X$ be the pushout of ${lambda,alpha_1}$, and let $Y$ be the
  pullback of ${nu,beta_2}$. Show that there exist maps $mu_i$ ($i=1,2,3$) and a
  commutative diagram
  #factorization-refined
  such that $mu_3 mu_2 mu_1 = mu$.

  #hint([@exc:map-factorization-pushout-pullback])[
    Use the previous two exercises.
  ]
] <exc:map-factorization-pushout-pullback>

#exercise[
  Let $R$ be a P.I.D., and let $overline(R) = R slash a R$, where $a$ is a
  nonzero element of $R$. Prove that $overline(R)$ is _self-injective_, that is,
  $overline(R)$ is an injective $overline(R)$-module.

  #hint([@exc:pid-quotient-self-injective])[
    Use @prop:injective-module-criteria (vi).
  ]
] <exc:pid-quotient-self-injective>
