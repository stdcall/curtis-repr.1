#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/04-dedekind.typ": *

== Dedekind Domains <sec:dedekind-domains>

#source(95)
=== Localization <ss:localization>

Throughout, $R$ denotes a commutative ring. A _multiplicative subset_#idx(
  "multiplicative subset",
) of $R$ is a subset $S$ of $R$ closed under multiplication, such that $1 in S$
and $0 in.not S$. For example, suppose that $P$ is an ideal of $R$, and let
$ R-P={x in R:x in.not P}. $
Then $R-P$ is a multiplicative subset of $R$ if and only if $P$ is a prime ideal
of $R$ (that is, a proper ideal such that $a b in P$, $a,b in R$, implies that
either $a in P$ or $b in P$). Given a (left) $R$-module $M$, define an
equivalence relation on the Cartesian product $M times S$ by writing
$(m,s) tilde (m',s')$ if and only if $t(s'm-s m')=0$ for some $t in S$. Let
$m/s$, or $s^(-1)m$, denote the equivalence class of the pair $(m,s)$, and let
$S^(-1)M$ be the set of all equivalence classes ${m/s}$.

In particular, $S^(-1)R$ can be made into a commutative ring by defining
$
  (a/s) plus.minus (b/t)=(t a plus.minus s b)/(s t), quad
  (a/s) dot (b/t)=(a b)/(s t)
$
for $a,b in R$, $s,t in S$. The map $R -> S^(-1)R$, defined by $a -> a/1$,
$a in R$, gives a ring homomorphism of $R$ into $S^(-1)R$. The kernel of this
homomorphism is
$ {a in R:s a=0 "for some" s in S}, $
the _$S$-torsion submodule_ of $R$. By virtue of this homomorphism, each
$S^(-1)R$-module becomes an $R$-module; in particular, $S^(-1)R$ is itself an
$R$-module, with $a in R$ acting as does $a/1$.

Likewise, for each $R$-module $M$ we may introduce an additive structure on
$S^(-1)M$ by setting
$
  (m/s) plus.minus (m'/s')=(s'm plus.minus s m')/(s s'), quad
  m,m' in M,s,s' in S.
$
There is an additive homomorphism $M -> S^(-1)M$, given by $m -> m/1$, whose
kernel is
$ {m in M:s m=0 "for some" s in S}, $
the _$S$-torsion submodule_ of $M$#idx("torsion submodule"). (This is clearly an
$R$-submodule of $M$.) Further, $S^(-1)M$ can be made into a (left)
$S^(-1)R$-module, by setting
$ (a/s)(m/t)=(a m)/(s t), quad a in R,m in M,s,t in S. $
The elements of $S$ _act invertibly_ on $S^(-1)M$, that is, for each $s in S$
the map $x -> s x$, $x in S^(-1)M$, is a bijection of $S^(-1)M$ onto itself. It
is easily verified (see @bib:Reiner1975[MO §~3b]) that there is an isomorphism
of $S^(-1)R$-modules:
$ S^(-1)M tilde.equiv S^(-1)R times.o_R M, $

#source(96)
given by $m/s -> (1/s) times.o m$, $m in M$, $s in S$. Hereafter, we shall
always identify these two modules.

We call $S^(-1)R$ a _ring of quotients_#idx("ring of quotients") of $R$, and
$S^(-1)M$ a _module of quotients_#idx("module of quotients"). Roughly speaking,
$S^(-1)R$ is the smallest ring into which $R$ maps in such a way that the
elements of $S$ become units in $S^(-1)R$. Likewise, $S^(-1)M$ is the smallest
module on which all elements of $S$ act invertibly.

For example, let $R$ be an integral domain, and set $S=R-{0}$. Then $S$ is a
multiplicative subset of $R$, and $S^(-1)R$ is precisely the field of quotients
of $R$. Further, for each $R$-module $M$, the module of quotients $S^(-1)M$ is a
vector space over the field $S^(-1)R$. The homomorphism $M -> S^(-1)M$ has as
kernel
$ {m in M:r m=0 "for some" r in R,r != 0}, $
the _torsion submodule_ of $M$#idx("torsion submodule"). In particular, call $M$
_$R$-torsionfree_ if this#idx("torsionfree") submodule is $0$. In that case,
there is an embedding of $M$ in the vector space $S^(-1)M$, given by $m -> m/1$,
$m in M$.

Let us return to the general case. The ring homomorphism $R -> S^(-1)R$ enables
us to view $S^(-1)R$ as an $R$-module. (Indeed, every $S^(-1)R$-module is then
also an $R$-module!) An important fact is that $S^(-1)R$ is a _flat_
$R$-module#idx("flat") (see @bib:Reiner1975[MO §~3c]), that is, for each exact
sequence
$ L arrow.r^f M arrow.r^g N $
of $R$-modules, the corresponding sequence of $S^(-1)R$-modules
$ S^(-1)L arrow.r^(f_*) S^(-1)M arrow.r^(g_*) S^(-1)N $
is also exact. Here, $f_* lr((x/s))=f(x)/s$, $x in L$, $s in S$, and $g_*$ is
defined analogously. The fact that $S^(-1)R$ is $R$-flat permits us to apply the
“Change of Rings”#idx("Change of Rings Theorem") Theorem~@th:change-of-rings and
Theorem~@th:ext-flat-change-of-rings. We have:

#proposition[
  Let $A$ be an $R$-algebra, and let $S$ be a multiplicative subset of the
  commutative ring $R$. Let $M,N$ be left $A$-modules such that $M$ is finitely
  presented. Then
  $
    S^(-1)R times.o_R Hom_A lr((M,N)) tilde.equiv
    Hom_(S^(-1)A) lr((S^(-1)M,S^(-1)N))
  $
  as $S^(-1)R$-modules. If we assume further that $A$ is left noetherian, then
  $
    S^(-1)R times.o_R op("Ext")_A^n lr((M,N)) tilde.equiv
    op("Ext")_(S^(-1)A)^n lr((S^(-1)M,S^(-1)N)), quad n >= 0,
  $
  as $S^(-1)R$-modules.
] <prop:localization-hom-ext>

#source(97)
Now let $P$ be a prime ideal of the commutative ring $R$; we may form the ring
of quotients $S^(-1)R$ relative to the multiplicative set $S=R-P$ in $R$. This
ring, denoted by $R_P$, is called the _localization_ of $R$#idx("localization")
at $P$. Likewise, each $R$-module $M$ has a localization $M_P$, and we always
identify $M_P$ with $R_P times.o_R M$. Generally speaking, it is easier to deal
with $R_P$-modules rather than $R$-modules, and localization techniques permit
us to pass from information about the set of _all_ localizations ${M_P}$ back to
information about $M$ itself. It usually suffices to let $P$ range over all
maximal ideals of $R$.

Let us state without proof a number of results on localizations; detailed proofs
may be found in @bib:Reiner1975[MO §~3d]. First of all, $R_P$ is a _local
ring_#idx("local ring"), that is, $R_P$ has a unique maximal ideal, namely
$P dot R_P$. If $P$ is a maximal ideal of $R$, then
$ R/P tilde.equiv R_P/(P dot R_P) $
as fields, and as $R_P$-modules. More generally, if $P$ is maximal and $r > 0$,
then $R/P^r$ may be viewed as an $R_P$-module, and
$ R/P^r tilde.equiv R_P/(P^r dot R_P) $
as $R_P$-modules.

Next, each $f in Hom_R lr((M,N))$ induces a map
$f_P in Hom_(R_P) lr((M_P,N_P))$, defined by $f_P lr((m/s))=f(m)/s$, $m in M$,
$s in R-P$. We have:

#proposition[
  Let $P$ range over all maximal ideals of $R$.
  #enum(
    numbering: "(i)",
    [For each $R$-module $M$, the map $M -> product_P M_P$ is injective.],
    [A sequence of $R$-modules $L arrow.r^f M arrow.r^g N$ is exact if and only
      if for each $P$,
      $ L_P arrow.r^(f_P) M_P arrow.r^(g_P) N_P $
      is exact. In particular, $f$ is injective if and only if each $f_P$ is
      injective, and $g$ is surjective if and only if each $g_P$ is surjective.
      Further,
      $
        ker f_P tilde.equiv (ker f)_P, quad
        "im" f_P tilde.equiv ("im" f)_P, quad
        "cok" f_P tilde.equiv ("cok" f)_P.
      $],
    [Let $A$ be an $R$-algebra, and let
      $ 0 -> L arrow.r^f M arrow.r^g N -> 0 $
      be an exact sequence of left $A$-modules, with $N$ finitely presented.
      Then the sequence is $A$-split if and only if for each $P$, the sequence
      $ 0 -> L_P arrow.r^(f_P) M_P arrow.r^(g_P) N_P -> 0 $
      #source(98)
      is $A_P$-split. In particular, $N$ is $A$-projective if and only if $N_P$
      is $A_P$-projective for each $P$.],
    [Let $R$ be an integral domain with field of quotients $K$, and view each
      $R_P$ as a subring of $K$. Then
      $ R=inter_P R_P, $
      where $P$ ranges over _all_ maximal ideals of $R$.],
  )
] <prop:localization-criteria>

A ring $A$ is _left hereditary_#idx("hereditary")#idx("left hereditary") if
every left ideal of $A$ is projective as left $A$-module. Hereditary rings are
important because a _Dedekind domain_ is precisely a hereditary integral domain.
Of course, every semisimple artinian ring is also hereditary. (Less trivially,
each maximal order over a Dedekind domain is hereditary; see
@th:maximal-orders-are-hereditary.) Part of the structure theorem for modules
over a principal ideal domain carries over to hereditary rings:

#proposition[
  For $A$ a left hereditary ring, every submodule of a free left $A$-module is
  isomorphic to an external direct sum of left ideals of $A$, and is therefore
  projective.
] <prop:hereditary-free-submodules>

#proof(head: emph[Sketch of Proof.])[
  For convenience, we treat only the most common case, where $N$ is a submodule
  of the free module $M=product_(i=1)^k A m_i$ on a finite basis. We must show
  that $N$ is isomorphic to a direct sum of ideals, and we use induction on $k$,
  the result being clear when $k=1$. Each $n in N$ is expressible as
  $n=sum r_i m_i$, $r_i in A$. Let $J$ be the set of all coefficients $r_1$
  which occur as $n$ ranges over all elements of $N$. Then $J$ is a left ideal
  of $A$, hence projective, and the correspondence $n -> r_1$ gives a surjection
  $N -> J$. The kernel $N'$ is given by
  $ N'=N inter product_(i=2)^k A m_i. $
  Then $N tilde.equiv N' plus.o J$, and $N'$ is isomorphic to a direct sum of
  ideals by the induction hypothesis. This completes the proof.
]

Finally, we remark (see @bib:Reiner1975[MO (3.24)]) that a left noetherian
$R$-algebra $A$ is left hereditary if and only if $A_P$ is left hereditary for
each maximal ideal $P$ of $R$.

=== Ideal Theory <ss:dedekind-ideal-theory>

Throughout, let $R$ be an integral domain with field of quotients $K$. We assume
that $R != K$, to avoid trivial cases. Call $R$ a _Dedekind domain_ if
“classical#idx("Dedekind domain") ideal theory” holds true in $R$, that is,
every proper nonzero ideal of
#source(99)
$R$ is uniquely expressible as a product of nonzero prime ideals, apart from
order of occurrence of the factors. Every P.I.D. (principal ideal domain) is
thus automatically a Dedekind domain, and from the standpoint of ideal theory,
the concept of a Dedekind domain is a natural generalization of that of a P.I.D.

Let $L$ be a finite extension of $K$; an element $x in L$ is called _integral
over_#idx("integral") $R$ if $x$ satisfies an equation of the form
$ x^n+a_1 x^(n-1)+dots+a_n=0, quad a_i in R. $
The set of all such $x$ is the _integral closure_#idx("integral closure") of $R$
in $L$, and is a ring $S$ in $L$ such that $K dot S=L$ (see
§@ss:algebras-integral-closure or @bib:CurtisReiner1962[CR §~17]). The basic
result here, which shows how Dedekind domains arise in practice, is as follows:

#proposition[
  Let $R$ be a P.I.D. (or more generally, a Dedekind domain) with field of
  quotients $K$. Let $L$ be a finite extension field of $K$, and let $S$ be the
  integral closure of $R$ in $L$. Then $S$ is a Dedekind ring with field of
  quotients $L$, and $K dot S=L$. Furthermore, if $L$ is a separable extension
  of $K$, then $S$ is finitely generated#footnote[
    This need not hold if $L/K$ is not separable. (See
    @bib:Kaplansky1970[Kaplansky (1970), Th.~100].)
  ] and torsionfree as $R$-module.
] <prop:integral-closure-dedekind>#idx(
  "Dedekind domain",
  target: [@prop:integral-closure-dedekind],
)

In particular, suppose that $L$ is an _algebraic number field_#idx(
  "algebraic number field",
), that is, a finite extension of the rational field $QQ$. The integral closure
of $ZZ$ in $L$, denoted by $"alg. int." {L}$, is called the ring of _algebraic
integers_#idx("algebraic integer = alg. int.") in $L$. This ring may be
determined quite explicitly, once the field $L$ is given. For example, we have
(@bib:CurtisReiner1962[CR (21.13)]):

#proposition[
  Let $L=QQ(omega)$, where $omega$ is a primitive $n$-th root of $1$. Then
  $"alg. int." {L}=ZZ[omega]$, and
  $ "min. pol."_QQ omega=Phi_n lr((X)), $
  the _cyclotomic polynomial_ of order $n$ and degree $phi(n)$.
] <prop:cyclotomic-integers>

In order to prove @prop:integral-closure-dedekind, other characterizations of
Dedekind domains are needed. We have

#proposition[
  The following assertions about a commutative integral domain $R$ are
  equivalent:
  #enum(
    numbering: "(i)",
    [$R$ is a Dedekind domain, that is, every proper nonzero ideal of $R$ is
      uniquely a product of nonzero prime ideals (up to order of occurrence),
      and if $J subset.eq J'$ is an inclusion of ideals, then the factors of
      $J'$ are a subset of those of $J$.],
    [#source(100)
      $R$ is noetherian, integrally closed#idx("integrally closed")#footnote[
        This means that each element of the quotient field of $R$, which is
        integral over $R$, must lie in $R$.
      ], and every nonzero prime ideal of $R$ is maximal.],
    [$R$ is hereditary.],
  )
] <prop:dedekind-domain-criteria>#idx(
  "Dedekind domain",
  target: [@prop:dedekind-domain-criteria],
)

The implication (ii)$arrow.r.double$(i) is proved in @bib:CurtisReiner1962[CR
  §~18]; for (ii)$arrow.r.double$(iii), see Exercise~@exc:dedekind-hereditary.
In van der Waerden~@bib:VanDerWaerden1959, (i)$arrow.r.double$(ii) is
established. A proof that (iii)$arrow.r.double$(ii) is given in
@bib:Auslander1974[Auslander–Buchsbaum (1974), Ch.~13]. In connection with (i),
see also (45.2) of Volume~II.

From here on, let $R$ be a Dedekind domain. A _fractional $R$-ideal_#idx(
  "fractional ideal",
)#idx("ideal", "fractional"), or “$R$-ideal in $K$”, is a nonzero f.g.
$R$-submodule of $K$. Every nonzero ideal of $R$ is such, since $R$ is
noetherian; nonzero ideals of $R$ are called _integral ideals_#idx(
  "ideal",
  "integral",
). For a fractional ideal $J$, we set
$ J^(-1)={x in K:x J subset.eq R}. $
Then (@bib:CurtisReiner1962[CR §~18]) the $R$-ideals in $K$ form a free abelian
group generated by the nonzero prime ideals of $R$, with identity element $R$,
and inverse given as above. From the factorizations of a pair of fractional
ideals $J,J'$ into products of powers of prime ideals:
$ J=product P_i^(a_i), quad J'=product P_i^(b_i), $
one can at once compute their sum $J+J'$ and intersection $J inter J'$, namely,
$
  J+J'=product P_i^(min(a_i, b_i)), quad
  J inter J'=product P_i^(max(a_i, b_i)).
$
If $J$ and $J'$ are integral ideals such that $J+J'=R$, call them _relatively
prime_#idx("relatively prime"). One version of the Chinese Remainder
Theorem#idx("Chinese Remainder Theorem") (@bib:CurtisReiner1962[CR §~18]) is as
follows: _If $A_1,dots,A_n$ are pairwise relatively prime ideals of $R$, then
there is a ring isomorphism_
$ R/(A_1 dots.c A_n) tilde.equiv product_(i=1)^n R/A_i. $
<eq:chinese-remainder-ideals>

A slightly more general version of this can be stated in terms of localizations.
For each maximal ideal $P$ of $R$, we may form the localization $R_P$.
Explicitly,
$ R_P={a/b:a in R,b in R-P}. $
By §@ss:localization, we know that $R_P$ has a unique maximal ideal, namely
$P dot R_P$. Furthermore (see @bib:CurtisReiner1962[CR §~19]) $R_P$ is a P.I.D.,
and all nonzero ideals in $R_P$ are powers of $P dot R_P$. Then we have
(@bib:CurtisReiner1962[CR §~18]):

#source(101)
#theorem(name: "Strong Approximation Theorem")[
  Let $P_1,dots,P_n$ be distinct maximal ideals of $R$, and let
  $a_1,dots,a_n in K$, $r_1,dots,r_n in ZZ$. Then there exists an $x in K$ such
  that
  $ x-a_i in P_i^(r_i) dot R_(P_i), quad 1 <= i <= n, $
  $ x in R_P "for each" P != P_1,dots,P_n. $
] <th:strong-approximation>#idx(
  "Strong Approximation Theorem",
  target: [@th:strong-approximation],
)

Now let $L$ be a finite separable extension of $K$, and let $S$ be the integral
closure of $R$ in $L$. Given a maximal ideal $P$ of $R$, let
$ P dot S=product_(i=1)^g P_i^(e_i), quad e_i > 0, $
<eq:prime-ideal-factorization>
where the ${P_i}$ are distinct prime ideals of $S$. Call $e_i$ the _ramification
index_#idx("ramification index") of $P_i$ relative to the extension $L/K$, and
write $e_i=e(P_i,L/K)$. On the other hand, the residue class field $S/P_i$ is an
extension of the field $R/P$, since $P_i inter R=P$. Let
$ f_i=f(P_i,L/K)=dim_(R/P) S/P_i, $
the _residue class degree_#idx("residue class degree") of $P_i$ for $L/K$. We
call $P_i$ _unramified_ in $L/K$#idx("unramified") if $e_i=1$ and $S/P_i$ is
separable over $R/P$; otherwise, $P_i$ is _ramified_#idx("ramified"). (If $R/P$
is a finite field, as is certainly the case when $L$ is an algebraic number
field, then $S/P_i$ is automatically separable over $R/P$; hence in this case
$P_i$ ramifies if and only if $e_i > 1$.) The fundamental relationship relating
the ${e_i}$ and ${f_i}$ is as follows (see @bib:CurtisReiner1962[CR (20.18)],
@bib:Reiner1975[MO (4.30)]):
$ sum_(i=1)^g e_i f_i=dim_K L. $ <eq:ramification-residue-degree>

This shows incidentally that each $f_i$ is finite. It is a key result in many
parts of algebraic number theory, and is used in the proof of
@prop:cyclotomic-integers, for example.

We next turn to a brief review of norms, different and discriminant. For
$a in L$, let $"min. pol."_K lr((a))$ be the monic polynomial in $K[X]$ of least
degree, which vanishes at $a$; it is obviously irreducible. On the other hand,
consider the $K$-linear transformation $x -> a x$, $x in L$; the characteristic
polynomial of this transformation is denoted by $"char. pol."_(L/K) lr((a))$.
Clearly (see @bib:Reiner1975[MO §~1])
$ "char. pol."_(L/K) a=("min. pol."_K a)^m, quad m=dim_(K(a)) L. $
<eq:characteristic-minimal-polynomial>

We define _trace_#idx("trace map") $T:L -> K$ and _norm_#idx("norm") $N:L -> K$
by the equation
$ "char. pol."_(L/K) lr((a))=X^n-T(a)X^(n-1)+dots+(-1)^n N(a), quad a in L, $
where $n=dim_K L$. By §@ss:algebras-integral-closure, $T$ is a $K$-linear map,
and $N$ is multiplicative. It
#source(102)
follows from @eq:characteristic-minimal-polynomial that
$
  T(a)=m alpha,N(a)=beta^m, quad "where"
  "min. pol."_K a=X^r-alpha X^(r-1)+dots+(-1)^r beta,
$
with $r=n/m$.

Since $R$ is a Dedekind domain, it is integrally closed in $K$. Hence Gauss's
Lemma holds#idx("Gauss' Lemma"): a monic polynomial which factors in $K[X]$
already factors in $R[X]$ (see @lem:gauss-integrally-closed). It follows at once
that $a in S$ if and only if $"min. pol."_K lr((a)) in R[X]$; for each such $a$,
we conclude that $T(a)$ and $N(a)$ lie in $R$.

For a subset $S_0$ of $S$, let $T(S_0)={T(x):x in S_0}$. We now define the
_inverse different_#idx("inverse different")
$ tilde(S)={x in L:T(x S) subset.eq R}. $
Then $tilde(S)$ is an $S$-ideal in $L$ containing $S$ (@bib:Reiner1975[MO
  §~4d]). The _different_#idx("different") of $S$ with respect to $R$ is then
defined by
$ D(S/R)=tilde(S)^(-1), $
an integral ideal of $S$. By @bib:Reiner1975[MO (4.37)], a maximal ideal $P_i$
of $S$ is unramified in the extension $L/K$ if and only if
$P_i divides.not D(S/R)$.

Above, we have defined the norm of an element of $L$; we wish to extend this
concept to ideals. Keeping the notation of @eq:prime-ideal-factorization and
@eq:ramification-residue-degree, we define
$ "norm of" P_i=N(P_i)=P^(f_i). $
The norm of an arbitrary $S$-ideal in $L$ is then computed from the above, by
requiring the norm to be multiplicative on ideals. By @bib:Reiner1975[MO
  Ex.~4.9], we have
$ N(S a)=R dot N(a),a in L. $
In the special case where $K=QQ$, and $R=ZZ$ it turns out that for each integral
ideal $J$ in $S$, the norm $N(J)=ZZ dot frak(N)(J)$, where $frak(N)(J)$ is the
number of elements in the residue class ring $S/J$. We call $frak(N)(J)$ the
_absolute norm_#idx("absolute norm") or _counting norm_#idx("counting norm") of
$J$.

The _discriminant_#idx("discriminant") of $S/R$ is defined by
$ d(S/R)=N{D(S/R)}, $
the norm of the different; it is a nonzero ideal of $R$. If $S$ has a free
$R$-basis, say $S=product_(i=1)^n R x_i$, where $n=dim_K L$, then
(@bib:Reiner1975[MO (4.35)]) we have
$ d(S/R)=R dot det(T(x_i x_j))_(1 <= i,j <= n). $
A maximal ideal $P$ of $R$ is said to _ramify_#idx("ramified") in $L$ if some
$P_i$ of $S$ dividing $P$
#source(103)
ramifies in $L/K$. Then by @bib:Reiner1975[MO (4.37)] we know that $P$ ramifies
in $L$ if and only if $P$ divides $d(S/R)$. We say that $S$ is _unramified
over_#idx("unramified") $R$ if no maximal ideal of $R$ ramifies in $L$. It
follows at once that $S$ is unramified over $R$ if and only if $d(S/R)=R$.

Finally, we remark that in the special case where $S=R[a]$, the discriminant
$d(S/R)$ is precisely the principal ideal $R dot d(a)$, where $d(a)$ is
discriminant#idx("discriminant") of the element $a$. (Recall that
$ d(a)=product (a_i-a_j)^2,1 <= i < j <= n, $
where $a_1,dots,a_n$ are the distinct zeros of $"min. pol."_K lr((a))$ in an
algebraic closure of $K$.)

=== Valuations, Completions, Localizations <ss:valuations-completions>

Let $RR^+$ be the set of nonnegative real numbers. A _valuation_#idx(
  "valuation",
) on a field $K$ is a map $phi:K -> RR^+$ such that for all $a,b in K$,
$
  cases(
    phi(a)=0 "if and only if" a=0,
    phi(a b)=phi(a)phi(b),
    phi(a+b) <= phi(a)+phi(b).
  )
$
A _non-archimedean_#idx("non-archimedean") valuation is one which satisfies the
stronger condition:
$ phi(a+b) <= "Max"(phi(a),phi(b)). $
A _discrete_ valuation is one for which the _value group_#idx("value group")
${phi(a):a in K,a != 0}$, is an infinite cyclic group; it is necessarily
non-archimedean. We exclude always the _trivial_ valuation defined by
$phi(0)=0$, $phi(a)=1$ for $a in K-{0}$.

Each valuation $phi$ gives rise to a metric on the space $K$, by choosing as
neighborhoods of an element $a in K$ the open spheres
$ {x in K:phi(x-a) < epsilon}, $
with $epsilon$ ranging over all positive real numbers. Two valuations are called
_equivalent_ if they yield#idx("equivalent valuations") the same topology on
$K$. By a _prime_#idx("prime of K") of $K$ we mean an equivalence class of
valuations of $K$.

Given a non-archimedean prime $phi$ on $K$, let
$ R={a in K:phi(a) <= 1}, quad P={a in K:phi(a) < 1}. $
Then $R$ is a ring, the _valuation ring_#idx("valuation ring") of $phi$, and $P$
is the unique maximal ideal of $R$. If $phi$ is discrete, then $P=R pi$ is a
principal ideal, generated by any element $pi in P$ for which $phi(pi)$
generates the value group of $phi$. In this case, the ring $R$ is called a
_discrete valuation ring_#idx("d. v. r. = discrete valuation ring")#idx(
  "discrete ring",
)#idx("discrete valuation ring") (abbreviation d.v.r.); each nonzero ideal of
$R$ is of the form $pi^k R$, for some $k >= 0$.

#source(104)
Discrete valuations arise in the following manner. Let $R$ be any Dedekind
domain, with quotient field $K$, and let $P$ be a maximal ideal of $R$. For each
$a in K$, let $v_P lr((a))$ denote the exponent to which $P$ occurs in the
factorization of $R a$ into a product of prime ideal powers, and set
$v_P lr((0))=+infinity$. Now choose a real number $kappa > 1$, and define
$ phi_P lr((a))=kappa^(-v_P lr((a))),a in K, $
with $phi_P lr((0))=0$. Then $phi_P$ is a discrete non-archimedean valuation on
$K$, called the _$P$-adic valuation_#idx("P-adic valuation") of $K$. (Changing
the value of $kappa$ does not change the equivalence class of the valuation.)
The valuation ring of $phi_P$ is precisely
$ R_P={x/s:x in R,s in R-P}, $
that is, the localization of $R$ at $P$. We have remarked in §@ss:localization
that residue class fields are unchanged in the passage from $R$ to $R_P$:
$ R/P tilde.equiv R_P/(P dot R_P). $

Keeping the above notation, let $J$ be an $R$-ideal in $K$; its localization
$J_P$ is then an $R_P$-ideal in $K$. Let $v_P lr((J))$ be the exponent to which
$P$ occurs in the factorization of $J$ into prime ideal powers. It is easily
shown (@bib:CurtisReiner1962[CR §~19]) that
$
  J_P=(P dot R_P)^(v_P lr((J))), "and"
  v_P lr((J))="Min"{v_P lr((a)):a in J}.
$
Thus, we can recover $J$ from its localizations; in fact, we have
$ J=inter_P J_P. $

Now let $L/K$ be a finite separable extension, and let $S$ be the integral
closure of $R$ in $L$. For each maximal ideal $P$, we may form the localization
$S_P$ since $S$ is an $R$-module. We leave it as an exercise for the reader to
verify that $S_P$ is the integral closure of $R_P$ in $L$. Furthermore, keeping
the notation of @eq:prime-ideal-factorization and
@eq:ramification-residue-degree, we have
$
  P dot S_P=product_(i=1)^g (P_i dot S_P)^(e_i), quad
  S_P/(P_i dot S_P) tilde.equiv S/P_i,1 <= i <= g.
$
Thus, the maximal ideals of $S_P$ dividing $P$ are precisely the $g$ ideals
${P_i dot S_P}$. In the passage from $R$ to $R_P$, and from $S$ to $S_P$, the
ramification indices ${e_i}$ and residue class degrees ${f_i}$ are unchanged.

Likewise, it is easily verified that norms, differents and discriminants behave
properly under localization:
$
  N(J_P)={N(J)}_P, D(S_P/R_P)={D(S/R)}_P,
  d(S_P/R_P)={d(S/R)}_P
$
for each $P$ and each $S$-ideal $J$ in $L$.

#source(105)
We are now ready to consider the process of completion. Starting with any
(nontrivial) valuation $phi$ on $K$, not necessarily non-archimedean, we have
seen above that $K$ may be made into a metric space. We may then form the
completion $hat(K)$ of this metric space in the usual way, namely, the elements
of $hat(K)$ are equivalence classes of Cauchy sequences from $K$. Then $hat(K)$
is a field, called the _$phi$-adic completion_#idx("P-adic completion")#idx(
  "completion",
) of $K$, and $K$ is embedded in $hat(K)$. The valuation $phi$ extends uniquely
to a valuation $hat(phi)$ on $hat(K)$, and $hat(K)$ is complete with respect to
its $hat(phi)$-adic metric#idx("P-adic topology"). If $phi$ is an archimedean
valuation, then so is $hat(phi)$, and $hat(K)$ is either $RR$ or $CC$, with
$hat(phi)$ equivalent to the usual absolute value (see @bib:Weiss1963[Weiss
  (1963), §~1.8]). On the other hand, if $phi$ is non-archimedean so is
$hat(phi)$, and $hat(phi)$ has the same value group as $phi$ (thus, if $phi$ is
a discrete valuation, so is $hat(phi)$).

Now let $phi$ be a discrete valuation on $K$, $hat(phi)$ its extension to the
$phi$-adic completion $hat(K)$, and set
$
  hat(R)={a in hat(K):hat(phi)(a) <= 1}, quad
  hat(P)={a in hat(K):hat(phi)(a) < 1}.
$
Thus $hat(R)$ is the discrete valuation ring associated with $hat(phi)$, and
$hat(P)$ is its unique maximal ideal. Then (@bib:Weiss1963[Weiss (1963), §~1.9])
we have an isomorphism of fields: $R/P tilde.equiv hat(R)/hat(P)$, where $R$ is
the valuation ring of $phi$ and $P$ is the maximal ideal of $R$. Indeed, more
generally, there is a ring isomorphism
$ hat(R)/hat(P)^k tilde.equiv R/P^k,"for each" k >= 1. $
We may observe further that
$ hat(P)=P dot hat(R),P=hat(P) inter R. $
Keeping the above notation, let $P=R pi$ and let $frak(S)$ be a full set of
representatives of the residue classes in $R/P$, with $0 in frak(S)$. Then each
nonzero element of $hat(K)$ is uniquely expressible as a Laurent series
$ pi^(-k)(a_0+a_1 pi+a_2 pi^2+dots),a_j in frak(S),a_0 != 0,k in ZZ. $
For further reading on completions, see @bib:CurtisReiner1962[CR §~19],
@bib:Weiss1963[Weiss (1963), §~1.7], or the elementary introduction by
Bachmann~@bib:Bachmann1964.

Now let $K$ be an algebraic number field. An _infinite prime_#idx(
  "infinite prime",
)#idx("prime of K") of $K$ is an equivalence class of archimedean valuations on
$K$. Such primes $P$ arise from embeddings of $K$ in the real field $RR$ or the
complex field $CC$. If the completion $K_P$ coincides with $RR$, we call $P$ a
_real prime_#idx("real prime") of $K$. On the other hand, if $K_P=CC$ we call
$P$ a _complex prime_#idx("complex prime") of $K$. Let $K=QQ(a)$, and write
$ "min. pol."_QQ lr((a))=product_(j=1)^n (X-a_j),a_j in CC. $
Let $a_1,dots,a_r$ be real, and let the remaining zeros be arranged in nonreal
conjugate pairs $a_(r+j),overline(a)_(r+j)$, $1 <= j <= s$. Then there are $r$
real primes of $K$, given
#source(106)
by the embeddings
$ theta_j:QQ(a) -> RR,"where" theta_j lr((a))=a_j,1 <= j <= r. $
Likewise, there are $s$ complex primes of $K$, given by the embeddings
$ theta_j:QQ(a) -> CC,"where" theta_j lr((a))=a_j,r+1 <= j <= r+s. $

=== Modules over Dedekind Domains <ss:modules-dedekind-domains>

Throughout, $R$ denotes a Dedekind domain with field of quotients $K$. The
_torsion submodule_#idx("torsion submodule") of an $R$-module $M$ is defined by
$ t(M)={m in M:r m=0 "for some nonzero" r in R}. $
By §@ss:localization, $t(M)$ is the kernel of the homomorphism
$M -> K times.o_R M$. Call $M$ _$R$-torsionfree_ if $t(M)=0$#idx(
  "torsionfree",
)\; in that case, this homomorphism is an embedding. We shall always identify
$M$ with its image $1 times.o M$ in $K times.o_R M$, assuming that $t(M)=0$;
then $K times.o_R M=K(1 times.o M)=K M$, the set of $K$-linear combinations of
elements of $M$. It is clear that for each $v in K M$, there exists a nonzero
$r in R$ such that $r v in M$.

An _$R$-lattice_#idx("R-lattice")#idx("lattice") is a finitely generated
$R$-torsionfree $R$-module. Each $R$-lattice $M$ may be embedded in a finite
dimensional $K$-space $V$ such that $K M=V$ (namely, choose $V=K times.o_R M$),
and we call $M$ a _full_ $R$-lattice#idx("full lattice") in $V$. If $M$ and $N$
are a pair of full $R$-lattices in $V$, then for each $m in M$ there is some
nonzero $r in R$ such that $r m in N$. Since $M$ is finitely generated as
$R$-module, it follows at once that there exist nonzero $r,s in R$ such that
$ r N subset.eq M subset.eq s^(-1) N. $
In particular, we may choose $N=product R v_i$, where ${v_i}$ is a $K$-basis of
$V$. It follows that every $R$-lattice $M$ is squeezed between a pair of free
$R$-modules on $n$ generators, where $n=dim_K K M$, the _$R$-rank_#idx("rank")
of $M$. Since $R$ is hereditary, $M$ is $R$-projective by
@prop:hereditary-free-submodules.

Let $M$ be an $R$-lattice, and let $L$ be a sublattice of $M$; we call $L$ an
_$R$-pure_#idx("pure") sublattice of $M$ if $M/L$ is $R$-torsionfree. But then
$M/L$ is $R$-projective, so the sequence
$ 0 -> L -> M -> M/L -> 0 $
is $R$-split, that is, $L$ is a direct summand of $M$. Conversely, each direct
summand of $M$ is $R$-pure in $M$. The importance of purity arises from the
following result, whose proof is left to the reader:

#proposition[
  Let $M$ be an $R$-lattice. The correspondence $N <-> W$ is bijective and
  inclusion-preserving, where $N$ ranges over all $R$-pure sublattices of $M$,
  and $W$ ranges over all $K$-subspaces of the $K$-space $K M$.
] <prop:pure-sublattices-subspaces>

#source(107)
Now let $M$ be an $R$-lattice of rank $n$; since $M$ may be embedded in a free
$R$-lattice, it follows from @prop:hereditary-free-submodules not only that $M$
is $R$-projective, but also that $M$ is isomorphic to an external direct sum
$product J_i$ of ideals of $R$. There must be $n$ summands, since $M$ has rank
$n$. The next result tells us when two such sums are isomorphic (for a proof,
see @bib:CurtisReiner1962[CR §~22]):

#theorem(name: "Steinitz’ Theorem")[
  Each $R$-lattice $M$ is $R$-projective, and
  $M tilde.equiv product_(i=1)^n J_i$, where the $J_i$ are ideals of $R$ and
  where $n$ is the $R$-rank of $M$. Further, the external direct sums
  $product_(i=1)^n J_i$ and $product_(i=1)^m J'_i$ are isomorphic if and only if
  $m=n$ and the products (in $K$) $J_1 dots.c J_n$ and $J'_1 dots.c J'_n$ are in
  the same _ideal class_#idx("ideal class").#footnote[
    Two $R$-ideals $J,J'$ are in the same _ideal class_ if $J'=J x$ for some
    nonzero $x in K$.
  ] This ideal class is called the _Steinitz class_#idx("Steinitz class") of the
  lattice.
] <th:steinitz>#idx("Steinitz' Theorem", target: [@th:steinitz])

The invariant factor theorem for lattices over principal ideal domains extends
readily to Dedekind domains (see @bib:CurtisReiner1962[CR §~22]), and we have

#theorem(name: "Invariant Factor Theorem")[
  Let $M,N$ be $R$-lattices such that $N subset.eq K M$. Then there exist
  elements ${m_i}$ in $M$, and fractional $R$-ideals ${J_i}$ and ${E_i}$, such
  that
  $
    M=op("⨁", limits: #true)_(i=1)^r J_i m_i,
    N=op("⨁", limits: #true)_(i=1)^s E_i J_i m_i
    quad ("internal direct sums"),
  $
  where $r=R$-rank of $M$, $s=R$-rank of $N$, $s <= r$, and where
  $ E_1 supset.eq E_2 supset.eq dots supset.eq E_s. $
  Further, if $N subset.eq M$ then each $E_i$ is an integral ideal, that is,
  $E_i subset.eq R$.
] <th:invariant-factors-dedekind>#idx(
  "Invariant Factor Theorem",
  target: [@th:invariant-factors-dedekind],
)

The ideals ${E_i}$ are called the _invariant factors_ of the pair $M,N$; they
are uniquely determined by the inclusion $N subset.eq K M$. If $N subset.eq M$,
then
$
  M/N tilde.equiv product_1^s J_i/(E_i J_i) plus.o
  product_(s+1)^r J_i.
$
However, for any fractional ideal $J$ and any integral ideal $E$ of $R$, there
is an $R$-isomorphism (see @bib:CurtisReiner1962[CR (18.24)])
$ J/(E J) tilde.equiv R/E. $ <eq:fractional-ideal-quotient>

Since every f.g. $R$-module is a homomorphic image of a free module of finite
rank, the above discussion yields the following structure theorem:

#source(108)
#proposition[
  Every f.g. $R$-module is isomorphic to an external direct sum of fractional
  ideals and cyclic#footnote[
    A module $M$ is _cyclic_#idx("cyclic module") if it is of the form $R x$ for
    some $x in M$.
  ] modules $R/E$, where $E$ denotes an integral ideal.
] <prop:dedekind-module-structure>

We shall now define the _order ideal_#idx("order ideal") $"ord" X$ of a f.g.
$R$-module $X$. Set $"ord" X=R$ if $X=0$, and $"ord" X=0$ if $X$ is not an
$R$-torsion#footnote[
  $X$ is an _$R$-torsion_ module#idx("torsion module") if $r X=0$ for some
  nonzero $r in R$.
] module. If $X$ is a nonzero torsion module, it has an $R$-composition series;
the composition factors are given by ${R/P_i}$, with the $P_i$ maximal ideals of
$R$. We set $"ord" X=product P_i$, a nonzero proper ideal of $R$. It is easily
seen that $"ord" X$ is well defined. If $X$ is a f.g. torsion $ZZ$-module, then
obviously $"ord"_ZZ X$ is the principal ideal $ZZ dot "card" X$. Thus, for
$R$-modules the order ideal measures their “size” in some sense. We have at once
(see @bib:Reiner1975[MO (4.17)]):

#proposition[
  If $L subset.eq M$ are f.g. $R$-modules, then
  $ "ord" M=("ord" L)("ord" M/L). $
  Further, for each ideal $J$ of $R$ we have
  $ "ord" R/J=J. $
] <prop:order-ideal-multiplicative>

An immediate consequence is:

#corollary[
  Let $R subset.eq S$ be an inclusion of Dedekind domains. Then for every f.g.
  $R$-module $X$, we have
  $ "ord"_S lr((S times.o_R X))=S times.o_R "ord" X. $
  <eq:order-extension-dedekind>
] <cor:order-extension-dedekind>

#proof[
  By @eq:fractional-ideal-quotient and @prop:dedekind-module-structure, it
  suffices to verify the result for $X=J$ and for $X=R/J$, where $J$ is an ideal
  of $R$. For the latter case, we start with the $R$-exact sequence
  $0 -> J -> R -> R/J -> 0$. Since $S$ is $R$-flat by
  Exercise~@exc:dedekind-torsionfree-flat, we obtain an $S$-exact sequence
  $ 0 -> S times.o J -> S -> S times.o (R/J) -> 0, $
  where $times.o$ means $times.o_R$. The image of $S times.o J$ in $S$ is
  precisely $J S$, and
  $ S times.o J tilde.equiv J S,S times.o (R/J) tilde.equiv S/(J S). $
  Thus
  $
    "ord"_S lr((S times.o (R/J)))="ord"_S lr((S/(J S)))=J S
    =S times.o "ord"(R/J),
  $
  as desired. On the other hand, when $X=J$ we see that $S times.o J$ is
  $S$-torsionfree, so both sides of @eq:order-extension-dedekind are zero. This
  completes the proof.
]

#source(109)
In particular, for each maximal ideal $P$ of $R$, and each f.g. $R$-module $X$,
we have
$ "ord" X_P=("ord" X)_P. $ <eq:order-localization>

We shall deduce from this:

#proposition-suffix(base: [@eq:order-localization], suffix: "a")[
  Let $f$ be an $R$-endomorphism of the $R$-lattice $M$. Then
  $ "ord" M/f(M)=R dot det(f) $
  where $det(f)$ is computed by extending $f$ to a $K$-endomorphism of $K M$.
] <prop:order-endomorphism-cokernel>

#proof[
  If $det f=0$, then $M/f(M)$ has positive $R$-rank, so its order ideal is
  $0=R dot det f$; hence we may assume that $det f != 0$. By
  @eq:order-localization, it suffices to prove the result when $R$ is replaced
  by $R_P$, and so we may assume that $R$ is a principal ideal domain. In this
  case, both $M$ and $f(M)$ have free $R$-bases, say
  $
    M=op("⨁", limits: #true)_(i=1)^r R m_i,
    f(M)=op("⨁", limits: #true)_(j=1)^r R n_j,
    "where" n_j=sum a_(i j)m_i,a_(i j) in R.
  $
  Changing $R$-bases in $M$ and $f(M)$, we may assume that the matrix
  $(a_(i j))$ is diagonal. Note that $det f=det(a_(i j))$, and that this change
  does not affect the ideal $R dot det f$. But if $(a_(i j))$ is a diagonal
  matrix, then
  $
    "ord" M/f(M)=product "ord" R/(R a_(i i))
    =product R a_(i i)=R dot det(a_(i j)),
  $
  as desired.
]

Now let $M$ be a f.g. $R$-module, and let $P$ be a maximal ideal of $R$. We have
denoted by $M_P$ the _localization_ of $M$#idx("localization") at $P$, that is,
$ M_P={m/s:m in M,s in R-P} tilde.equiv R_P times.o_R M. $
On the other hand, we may form the $P$-adic completion $hat(K)_P$ of the field;
let $hat(R)_P$ be the valuation ring of the $P$-adic valuation on $hat(K)_P$,
and $hat(P)$ its maximal ideal. Let us set
$
  hat(M)_P=hat(R)_P times.o_R M tilde.equiv
  hat(R)_P times.o_(R_P) M_P,
$
the _$P$-adic completion_#idx("completion") of $M$. (We may also view $hat(M)_P$
as the completion of $M$, where $M$ is topologized by requiring that
${P^k M:k=0,1,2,dots}$ be a basis for the open neighborhoods of $0$. See
@bib:Reiner1975[MO (6.16)].) We shall state without proof a number of properties
of completions of modules, generalizing results given above in
§@ss:valuations-completions about completions of rings; the module results
follow readily from those about rings, by use of
@prop:dedekind-module-structure.

#source(110)
#proposition[
  Let $M$ be a f.g. $R$-module. Then
  #enum(
    numbering: "(i)",
    [$M$ is dense in $hat(M)_P$.],
    [For each $k >= 1$, there are ring isomorphisms
      $ hat(R)/hat(P)^k tilde.equiv R_P/(P^k R_P) tilde.equiv R/P^k, $],
    [The map $M_P -> hat(M)_P$ is always injective.],
    [For $k >= 0$,
      $ M_P inter hat(P)^k hat(M)_P=P^k M_P. $],
    [Let $V$ be a f.d. $K$-space, and set $hat(V)_P=hat(K)_P times.o_K V$. There
      is a bijection $M <-> T$ which preserves inclusions, where $M$ ranges over
      all $R_P$-lattices in $V$ for which $K M=V$, and $T$ ranges over all
      $hat(R)_P$-lattices in $hat(V)_P$ for which $hat(K)_P T=hat(V)_P$.],
    [For each $R$-lattice $M$, we have $M_P=K M inter hat(M)_P$ for each $P$,
      and
      $ M=inter_P (K M inter M_P)=inter_P (K M inter hat(M)_P). $],
    [Let $V$ be a f.d. $K$-space, and let $M$ be a full#footnote[
        This means that $K M=V$.
      ] $R$-lattice in $V$. Suppose that for each $P$, there is given a full
      $R_P$-lattice $X(P)$ in $V$, such that $X(P)=M_P$ a.e.#idx(
        "a. e. (= almost everywhere)",
      )#footnote[
        “a.e.” means “almost everywhere,” that is, for all but a finite number
        of $P$'s.
      ] Define
      $ N=inter_P X(P), $
      the intersection being formed within $V$. Then $N$ is a full $R$-lattice
      in $V$, and
      $ N_P=X(P) "for each" P. $],
    [Keeping the above notation, suppose that for each $P$ there is given a full
      $hat(R)_P$-lattice $Y(P)$ in $hat(V)_P$, such that $Y(P)=hat(M)_P$ a.e.
      Define
      $ L=inter_P {V inter Y(P)}. $
      Then $L$ is a full $R$-lattice in $V$, and $hat(L)_P=Y(P)$ for all $P$.],
  )
] <prop:localization-completion-lattices>

Proofs may be found in @bib:Reiner1975[MO §~4b and §~5a].

#source(111)
=== Duals of Lattices <ss:duals-lattices>

Let $R$ be a Dedekind domain with field of quotients $K$, and let $V$ be an
$n$-dimensional $K$-space. Given a nondegenerate bilinear symmetric form
$tau:V times V -> K$, we can form duals with respect to $tau$. If ${x_i}$ is a
$K$-basis of $V$, the _dual basis_#idx("dual basis") ${y_j}$ is the $K$-basis of
$V$ determined by the condition
$ tau(x_i, y_j)=delta_(i j),1 <= i,j <= n. $
Clearly, the dual of the basis ${y_j}$ is the original basis ${x_i}$.

Now let $M$ be a full $R$-lattice in $V$, and define the _dual_ of $M$ (with
respect to $tau$) by
$ tilde(M)={x in V:tau(x, M) subset.eq R}. $ <eq:dual-lattice>#idx(
  "dual lattices",
  target: [@eq:dual-lattice],
)#idx("dual of module", target: [@eq:dual-lattice])
We have at once (if $M$ is $R$-free)
$ M=product_1^n R x_i => tilde(M)=product_1^n R y_i, $
<eq:dual-free-lattice>
where ${y_j}$ is a dual basis for ${x_i}$. Hence $tilde(tilde(M))=M$ whenever
$M$ is $R$-free; also, $tilde(M)$ is a full $R$-lattice in $V$.

#proposition[
  For any full $R$-lattice $M$ in $V$, its dual $tilde(M)$ is also a full
  $R$-lattice in $V$. Further, $tilde(tilde(M))=M$.
] <prop:dual-lattice-involution>

#proof[
  We may choose free full $R$-lattices $N_1,N_2$ in $V$ such that
  $N_1 subset.eq M subset.eq N_2$. Then
  $tilde(N)_2 subset.eq tilde(M) subset.eq tilde(N)_1$, whence $tilde(M)$ is
  also a full $R$-lattice in $V$.

  In order to verify that $tilde(tilde(M))=M$, we observe first that the process
  of localization (at a maximal ideal $P$ of $R$) commutes with formation of
  duals:
  $ (tilde(M))_P="dual of" M_P. $
  It thus suffices to verify that $tilde(tilde(M))_P=M_P$ for each $P$; but this
  is clear, since $M_P$ is a full free $R_P$-lattice in $V$.
]

Keeping the above notation, we define the _discriminant ideal_#idx(
  "discriminant ideal",
) of a full $R$-lattice $M$ in $V$ as the $R$-ideal in $K$ generated by all
elements
$ alpha=det[tau(x_i, x_j)]_(1 <= i,j <= n),x_1,dots,x_n in M. $
<eq:lattice-discriminant-generators>
If we denote this ideal by $d(M)$, then clearly
$ {d(M)}_P=d(M_P) $
#source(112)
for each maximal ideal $P$ of $R$. Since $tau$ is nondegenerate, $d(M) != 0$.
Furthermore, if $M=product_1^n R x_i$, then $d(M)=alpha R$, with $alpha$ given
by @eq:lattice-discriminant-generators. Obviously, if $N$ is also a full
$R$-lattice in $V$, then
$ N subset.eq M => d(N) subset.eq d(M). $

#proposition[
  Let $N subset.eq M$, where $M$ and $N$ are full $R$-lattices in $V$. Then
  $ d(N)={"ord" M/N}^2 d(M), $
  where $"ord"(M/N)$ denotes the $R$-order ideal defined in
  §@ss:modules-dedekind-domains. Therefore $M=N$ if and only if $d(M)=d(N)$.
] <prop:lattice-discriminant-index>

#proof[
  It suffices to establish the result after replacing $R$ by its localization
  $R_P$ at an arbitrary maximal ideal of $R$. Changing notation, assume
  hereafter that $R$ is a P.I.D. Then we may find $x_1,dots,x_n in M$ and
  $alpha_1,dots,alpha_n in R$ such that
  $
    M=R x_1 plus.o dots plus.o R x_n,
    N=R alpha_1 x_1 plus.o dots plus.o R alpha_n x_n.
  $
  Then (as in the proof of @prop:order-endomorphism-cokernel)
  $ "ord" M/N=product "ord" R/(R alpha_i)=product R alpha_i. $
  On the other hand, $d(M)=alpha R$ with $alpha$ as in
  @eq:lattice-discriminant-generators, while
  $d(N)=alpha dot product alpha_i^2 dot R$. This establishes the relation
  between $d(M)$ and $d(N)$. Finally, if $d(M)=d(N)$ then $"ord" M/N=R$, whence
  $M=N$.
]

Suppose now that $Lambda$ is an $R$-algebra which acts from the left on the
$R$-lattice $M$, in such a way that
$
  lambda dot alpha m=alpha dot lambda m "for all"
  lambda in Lambda,alpha in R,m in M.
$
We call $M$ a _left $Lambda$-lattice_ to indicate that the $R$-lattice $M$ is a
left $Lambda$-module. We can make $V$ into a left $Lambda$-module by writing
$V=K times.o_R M$, and then defining
$
  lambda(alpha times.o m)=alpha times.o lambda m "for"
  lambda in Lambda,alpha in K,m in M.
$
Next, the nondegenerate form $tau:V times V -> K$ enables us to define the
transpose $attach(f, tl: t)$ of an arbitrary $f in End_K lr((V))$. This
transpose also lies in $End_K lr((V))$, and is defined by the condition
$ tau(attach(f, tl: t) x, y)=tau(x, f y) "for all" x,y in V. $
We use this idea to define a right $Lambda$-module structure on $V$, as follows:
for
#source(113)
each $lambda in Lambda$ and $x in V$, let $x lambda in V$ be the element defined
by the identity
$ tau(x lambda, y)=tau(x, lambda y) "for all" y in V. $
Let us show that the dual $tilde(M)$ is a right $Lambda$-lattice in $V$. This
follows at once from the fact that for any $x in tilde(M)$ and
$lambda in Lambda$,
$ tau(x lambda, M)=tau(x, lambda M) subset.eq tau(x, M) subset.eq R. $
The above discussion shows that there is a $1$–$1$ inclusion-reversing
correspondence $M <-> tilde(M)$, which associates to each left $Lambda$-lattice
$M$ its dual $tilde(M)$. Then $tilde(M)$ is a right $Lambda$-lattice, and there
is a left $Lambda$-isomorphism $tilde(tilde(M)) tilde.equiv M$. (Indeed,
$tilde(tilde(M))=M$.)

Now let $K'$ be a field containing $K$, and set $V'=K' times.o_K V$. The form
$tau$ extends to a nondegenerate bilinear form $tau':V' times V' -> K'$, where
$tau'=1 times.o tau$. Let $R'$ be the integral closure of $R$ in $K'$. Each full
$R$-lattice $M$ in $V$ gives rise to a full $R'$-lattice $M'$ in $V'$, defined
by $M'=R' times.o_R M$. It is easily verified that the dual of $M'$ (with
respect to $tau'$) is precisely $R' times.o_R tilde(M)$, and further that
$ d(M')=R' dot d(M), $
where $d(M')$ is the discriminant computed relative to $tau'$.

We shall use this fact to establish an important property of unramified
extensions:

#theorem-suffix(base: [@prop:lattice-discriminant-index], suffix: "a")[
  Let $L$ be a finite separable extension of $K$, and let $S$ be the integral
  closure of $R$ in $L$. Assume that $S$ is unramified over $R$. Let $K'$ be any
  finite extension of $K$, and $R'$ the integral closure of $R$ in $K'$. Then
  #enum(
    numbering: "(i)",
    [$K' times.o_K L tilde.equiv product_(i=1)^t F_i$, where each $F_i$ is a
      finite separable extension field of $K'$.],
    [$R' times.o_R S tilde.equiv product_(i=1)^t R_i$, where $R_i$ is the
      integral closure of $R'$ in $F_i$.],
    [Each $R_i$ is unramified over $R'$.],
  )
] <th:unramified-base-extension>

#proof[
  Assertion (i) is obvious, once we write $L=K[x] slash (f(x))$, with
  $f(x) in K[x]$ separable and irreducible; for then
  $
    K' times.o_K L tilde.equiv K'[x] slash (f(x)) tilde.equiv
    product_i K'[x] slash (g_i lr((x))),
  $
  where $f(x)=product g_i lr((x))$ is the factorization of $f(x)$ into
  irreducible factors in $K'[x]$.

  #source(114)
  We observe next that $R' times.o S subset.eq product R_i$, and that the
  discriminant $d(R' times.o S)$, relative to the bilinear form
  $1 times.o T_(L/K)$, is equal to $R' dot d(S/R)$. This follows from the
  remarks preceding the theorem. But $d(S/R)=R$ since $S/R$ is unramified, so
  $d((R' times.o S)/R')=R'$. On the other hand, by
  @prop:lattice-discriminant-index
  $
    d((R' times.o S)/R')=
    {"ord"_(R') ((product R_i)/(R' times.o S))}^2 dot
    product_(i=1)^t d(R_i/R').
  $
  Therefore each factor on the right must equal $R'$, which establishes both
  (ii) and (iii), and completes the proof.
]

=== Ideal Class Groups; Global Fields <ss:ideal-class-groups-global-fields>

Let $R$ be a Dedekind domain with field of quotients $K$. An _$R$-ideal in $K$_
is a nonzero f.g. $R$-submodule of $K$; such ideals are also called _fractional
$R$-ideals_#idx("fractional ideal")#idx("ideal", "fractional"). For each
fractional $R$-ideal $J$, there exists a nonzero $alpha in R$ such that
$alpha J$ is an ordinary ideal of the domain $R$. Two $R$-ideals $J,J'$ are
called _equivalent_ if $J'=J x$ for some nonzero $x in K$; thus, $J,J'$ are
equivalent if and only if $J tilde.equiv J'$ as $R$-modules. The _ideal
class_#idx("ideal class") $[J]$ is defined as the set of all fractional ideals
equivalent to $J$.

We may define multiplication of ideal classes by the formula
$ [J][J']=[J J'], $
where $J J'$ is the $R$-ideal consisting of all finite sums $sum x_i y_i$,
$x_i in J$, $y_i in J'$. This multiplication is well defined, and the ideal
class $[R]$ is the unity element for multiplication. The ideals in the class
$[R]$ are called _principal ideals_#idx("ideal", "principal")#idx(
  "principal ideal",
)\; they are of the form $R x$, with $x in K$, $x != 0$.

Given a fractional $R$-ideal $J$, define its _inverse_#idx(
  "ideal",
  "inverse",
)#idx("inverse ideal") as
$ J^(-1)={x in K:x J subset.eq R}. $
Then $J^(-1)$ is also a fractional $R$-ideal, and
$ J J^(-1)=J^(-1)J=R. $
Thus $[J^(-1)][J]=[R]$, and so the ideal classes form an abelian multiplicative
group, hereafter denoted by $"Cl"(R)$, the _ideal class group_ of $R$. The order
of this group is called the _ideal class number_#idx("class number")#idx(
  "ideal class number",
) of $R$, and is usually denoted by $h(R)$. Thus, $h(R)=1$ if and only if $R$ is
a principal ideal domain.

A _global field_#idx("global field") is either an _algebraic number field_ (that
is,#idx("algebraic number field") a finite extension of the rational field
$QQ$), or else a _function field_#idx("function field") (that is, a finite
extension of a simple transcendental extension $k(X)$ of a finite field $k$.)
One of the basic facts about global fields is as follows:

#theorem[
  Let $R$ be a Dedekind domain whose field of quotients $K$ is a global field.
  Then the ideal class group of $R$ is finite.
] <th:global-field-class-group-finite>

#source(115)
The theorem is proved in @bib:CurtisReiner1962[CR (20.6)] for the case where $K$
is an algebraic number field and $R="alg. int." {K}$.

In a later section (§@sec:jordan-zassenhaus) we shall state the
Jordan–Zassenhaus Theorem, which generalizes the above result to the case of
non-commutative rings of integers.

=== Primary Decompositions <ss:primary-decompositions>

Throughout this subsection, $R$ denotes a Dedekind domain with quotient field
$K$, and $P,P_1$, etc., denote maximal ideals of $R$. For an $R$-module $M$,
$M_P$ is the localization of $M$ at $P$.

#definition[
  The _$P$-primary submodule_ of an $R$-module $M$ is defined as
  $ {m in M:P^e m=0 "for some integer" e >= 0}. $
  A _$P$-primary_ module is one which coincides with its $P$-primary submodule.
] <def:primary-submodule>#idx(
  "primary submodule",
  target: [@def:primary-submodule],
)

#proposition[
  Let $M$ be a f.g. $P$-primary $R$-module. Then $M tilde.equiv M_P$.
] <prop:primary-module-localization>

#proof[
  For $alpha in R-P$ we have $alpha R+P=R$, whence $alpha R+P^e=R$ for each
  $e >= 0$. Since $M$ is $P$-primary and f.g., we may choose $e$ so that
  $P^e M=0$. But then $alpha$ acts invertibly on $M$, whence
  $(R-P)^(-1)M tilde.equiv M$ as claimed.
]

#proposition[
  Let $M$ be a f.g. $P$-primary $R$-module, and let $Q$ be a maximal ideal of
  $R$ distinct from $P$. Then $M_Q=0$.
] <prop:primary-module-other-localizations>

#proof[
  We have $Q+"ann"_R M=R$, so $M_Q=0$ by
  Exercise~@exc:localization-zero-annihilator.
]

An $R$-module $M$ is called a _torsion module_#idx("torsion module") if each
$m in M$ is annihilated by some nonzero element of $R$. We now prove

#theorem(name: "Primary Decomposition Theorem")[
  Let $M$ be a f.g. torsion $R$-module. Then $M_P=0$ a.e., and $M$ is
  expressible as a finite direct sum
  $ M=op("⨁", limits: #true)_P M_P. $
  Further, for each $P$, $M_P$ is the $P$-primary submodule of $M$.
] <th:primary-decomposition-dedekind>#idx(
  "Primary Decomposition Theorem",
  target: [@th:primary-decomposition-dedekind],
)

#proof[
  Since $M$ is f.g. and a torsion module, we have $a M=0$ for some nonzero
  $a in R$. Let
  $ R a=product_(i=1)^n P_i^(e_i) $
  be the factorization of $R a$ into powers of distinct maximal ideals of $R$.
  #source(116)
  Then by @eq:chinese-remainder-ideals we have
  $ R/(R a) tilde.equiv product R/P_i^(e_i). $
  But $M$ may be viewed as $(R/(R a))$-module, and thus
  $
    M=(R/(R a))M tilde.equiv product (R/P_i^(e_i))M
    =product M/(P_i^(e_i)M).
  $
  Now $M/(P_i^(e_i)M)$ is $P_i$-primary, so by @prop:primary-module-localization
  and @prop:primary-module-other-localizations we have
  $
    (M/(P_i^(e_i)M))_P tilde.equiv
    cases(
      M/(P_i^(e_i)M) & "if" P=P_i,
      0 & "if" P != P_i.
    )
  $
  Clearly $M/(P_i^(e_i)M)$ is the $P_i$-primary submodule of $M$. But
  $ M_P tilde.equiv product (M/(P_i^(e_i)M))_P, $
  so we obtain $M/(P_i^(e_i)M)=M_(P_i)$ for $1 <= i <= n$. Therefore
  $M=product M_P$ as claimed, and $M_P=0$ except when $P$ is one of
  $P_1,dots,P_n$. This completes the proof.
]

=== Cyclotomic Fields <ss:cyclotomic-fields>

Let $omega_m$ denote a primitive $m$-th root of $1$ over the rational field
$QQ$, and let
$ K_m=QQ(omega_m),R_m=ZZ[omega_m]="alg. int." {K_m} $
<eq:cyclotomic-field-integers>#idx(
  "cyclotomic field",
  target: [@eq:cyclotomic-field-integers],
) (see @prop:cyclotomic-integers). Then
$ "min. pol."_QQ lr((omega_m))=Phi_m lr((x)), $
the cyclotomic polynomial of order $m$#idx("cyclotomic polynomial") and degree
$phi(m)$, where $phi$ is the Euler $phi$-function. From @bib:CurtisReiner1962[CR
  §~21], we know that $Phi_m lr((x))$ is irreducible in $QQ[x]$, and
$ Phi_m lr((x))=product_(1 <= k <= m, (k,m)=1) (x-omega_m^k). $
<eq:cyclotomic-polynomial-roots>
These ${omega_m^k}$ are a full set of primitive $m$-th roots of $1$ over $QQ$.

Now let $p$ be a fixed rational prime. We wish to describe the factorization of
$p R_m$ into a product of prime ideal powers. This is essentially an exercise in
the use of Kummer's Theorem (see @bib:Weiss1963[Weiss (1963), Th.~4.9-1]),
though we shall give a self-contained discussion below. Let us begin with the
case where $p divides.not m$.

#proposition[
  Let $p divides.not m$, and let $P$ be a prime ideal of $R_m$ containing $p$.
  Set $overline(R)_m=R_m/P$, $overline(ZZ)=ZZ/(p ZZ)$, and let bars denote
  images in $overline(R)_m$ or $overline(ZZ)$, according to the context.
  #enum(
    numbering: "(i)",
    [#source(117)
      The $phi(m)$ elements
      $ {overline(omega)_m^k:1 <= k <= m,(k,m)=1} $
      are a full set of $phi(m)$ distinct primitive $m$-th roots of $1$ over
      $overline(ZZ)$. They are the zeros of $overline(Phi)_m lr((x))$ in
      $overline(R)_m$.],
    [Let $f$ be the _order_ of $p mod m$, that is, the least positive integer
      such that $p^f equiv 1 (mod m)$. Then
      $
        "min. pol."_(overline(ZZ)) lr((overline(omega)_m))=
        product_(j=0)^(f-1) (x-overline(omega)_m^(p^j)) in overline(ZZ)[x].
      $
      <eq:cyclotomic-residue-minimal-polynomial>
      Denoting this polynomial by $F_1 lr((x))$, we have
      $
        overline(R)_m=overline(ZZ)[x] slash (F_1 lr((x)))=
        "field extension of" overline(ZZ) "of degree" f.
      $],
    [The prime $p$ is unramified in $R_m$, that is, $p R_m$ is a product of
      distinct prime ideals of $R_m$. Let
      $
        overline(Phi)_m lr((x))=product_(i=1)^g F_i lr((x)),
        F_i lr((x)) "irreducible in" overline(ZZ)[x].
      $
      <eq:cyclotomic-modular-factorization>
      Then the ${F_i}$ are distinct, and we have
      $
        p R_m=product_(i=1)^g P_(m i), "where"
        P_(m i)=(p,F_i lr((omega_m)))="prime ideal of" R_m.
      $
      <eq:cyclotomic-unramified-factorization>],
  )
] <prop:cyclotomic-unramified-primes>

#proof[
  The notation $(p,F_i lr((omega_m)))$ is somewhat confusing at first, and
  should be interpreted as follows: pick any polynomial $G_i lr((x)) in ZZ[x]$
  such that $overline(G)_i=F_i$ in $overline(ZZ)[x]$. Then the ideal
  $(p,G_i lr((omega_m)))$ of $R_m$, generated by $p$ and $G_i lr((omega_m))$,
  does not depend on the choice of $G_i lr((x))$. We are denoting this ideal by
  $(p,F_i lr((omega_m)))$.

  To begin the proof, we deduce from @eq:cyclotomic-polynomial-roots that
  $ overline(Phi)_m lr((x))=product_k (x-overline(omega)_m^k). $
  Since $overline(Phi)_m lr((x))$ divides $x^m-1$ in $overline(ZZ)[x]$, and the
  latter has no repeated factors because $p divides.not m$, it follows that the
  $phi(m)$ elements ${overline(omega)_m^k}$ are distinct. This implies at once
  that $overline(omega)_m$ is a primitive $m$-th root of $1$ over
  $overline(ZZ)$, and that the $phi(m)$ elements ${overline(omega)_m^k}$ are a
  full set of primitive $m$-th roots of $1$ over $overline(ZZ)$.

  Next, since $R_m=ZZ[omega_m]$ we have
  $overline(R)_m=overline(ZZ)[overline(omega)_m]$, and we must compute the
  minimum polynomial of $overline(omega)_m$ over $overline(ZZ)$. The Galois
  group of $overline(ZZ)(overline(omega)_m)$ over $overline(ZZ)$ is generated by
  the Frobenius automorphism#idx("Frobenius automorphism") $theta$ defined by
  $theta(a)=a^p$, $a in overline(ZZ)(overline(omega)_m)$.
  #source(118)
  But
  $ theta^n lr((overline(omega)_m))=overline(omega)_m^(p^n),n=1,2,dots. $
  Thus $theta^n=1$ if and only if $p^n equiv 1 (mod m)$. This shows that $theta$
  has order $f$, and establishes @eq:cyclotomic-residue-minimal-polynomial. It
  proves also that
  $overline(R)_m tilde.equiv overline(ZZ)[x] slash (F_1 lr((x)))$.

  Finally, let @eq:cyclotomic-modular-factorization be the factorization of
  $overline(Phi)_m lr((x))$ over $overline(ZZ)$. Since $overline(Phi)_m lr((x))$
  has no repeated zeros, the ${F_i}$ are distinct. Each $F_i$ has degree $f$,
  since if $omega$ is any zero of $F_i lr((x))$, then the distinct zeros of
  $F_i lr((x))$ are given by
  $ {omega^(p^j):0 <= j <= f-1}. $
  Now we have
  $
    R_m/(p R_m) tilde.equiv ZZ[x] slash (p,Phi_m lr((x)))
    tilde.equiv overline(ZZ)[x] slash (overline(Phi)_m lr((x)))
    tilde.equiv product_(i=1)^g overline(ZZ)[x] slash (F_i lr((x))),
  $
  with each summand $overline(ZZ)[x] slash (F_i lr((x)))$ a field extension of
  $overline(ZZ)$ of degree $f$. Therefore $p R_m$ has no repeated prime ideal
  factors. Further, the maximal ideals of $R_m$ containing $p R_m$ are precisely
  the inverse images, under the map $R_m -> R_m/(p R_m)$, of the maximal ideals
  of the above direct sum $product overline(ZZ)[x] slash (F_i lr((x)))$. This
  gives the formulas for the ${P_(m i)}$ listed in
  @eq:cyclotomic-unramified-factorization. We remark that the originally
  specified prime ideal $P$ is given by $(p,F_1 lr((omega_m)))$. This completes
  the proof of the proposition.
]

The other extreme case is that where $m=p^b$ for some $b >= 1$ and some prime
$p$:

#proposition[
  Let $m=p^b$, where $p$ is prime, and let $P$ be a prime ideal of $R_m$
  containing $p$. Set $overline(R)_m=R_m/P$, $overline(ZZ)=ZZ/(p ZZ)$.
  #enum(
    numbering: "(i)",
    [We have $overline(R)_m=overline(ZZ)$, and
      $ overline(Phi)_m lr((x))=(x-1)^(phi(m)) "in" overline(ZZ)[x]. $
      <eq:prime-power-cyclotomic-reduction>
      Further, $P$ is the principal ideal $(1-omega_m)R_m$.],
    [$p$ is completely ramified in $R_m$, that is, $p R_m=P^(phi(m))$.],
  )
] <prop:prime-power-cyclotomic-ramification>

#proof[
  Every $m$-th root of $1$ over $overline(ZZ)$ equals $1$, since $m=p^b$; this
  gives @eq:prime-power-cyclotomic-reduction at once. Therefore
  $
    R_m/(p R_m) tilde.equiv ZZ[x] slash (p,Phi_m lr((x)))
    tilde.equiv overline(ZZ)[x] slash ((1-x)^(phi(m))).
  $
  #source(119)
  Thus there is a unique prime ideal $P$ of $R_m$ containing $p$, namely
  $P=(p,1-omega_m)$. Further, we have
  $R_m/P tilde.equiv overline(ZZ)[x] slash (1-x)=overline(ZZ)$, and
  $p R_m=P^(phi(m))$. Finally,
  $ N_(K_m/QQ) lr((1-omega_m))=Phi_m lr((1))=p, $
  where $N$ denotes the norm. This shows that $p$ is a multiple of $1-omega_m$
  in $R_m$, whence $P=(1-omega_m)R_m$. This completes the proof.
]

Turning to the general case, we now prove

#theorem[
  Let $m=p^b s$, where $p$ is prime and $p divides.not s$. Let $f$ be the order
  of $p mod s$. Let ${P_(m i)}$ range over the prime ideals of $R_m$ containing
  $p$, and ${P_(s i)}$ over those of $R_s$. Put $overline(ZZ)=ZZ/(p ZZ)$, and
  let
  $
    overline(Phi)_s lr((x))=product_(i=1)^g F_i lr((x)),
    F_i lr((x)) "irreducible in" overline(ZZ)[x].
  $
  #enum(
    numbering: "(i)",
    [The ${F_i}$ are distinct, and we have (with suitable numbering)
      $
        p R_s=product_(i=1)^g P_(s i), quad
        P_(s i)R_m=(P_(m i))^(phi(p^b)) "for each" i.
      $],
    [For $1 <= i <= g$,
      $R_s/P_(s i) tilde.equiv overline(ZZ)[x] slash (F_i lr((x)))$, a field
      extension of $overline(ZZ)$ of degree $f$. Further,
      $ R_m/P_(m i) tilde.equiv R_s/P_(s i) "for each" i. $],
    [In $overline(ZZ)[x]$ we have
      $overline(Phi)_m lr((x))={overline(Phi)_s lr((x))}^(phi(p^b))$.],
  )
  In brief, in the extension $K_s/QQ$, the prime $p$ splits into $g$ distinct
  primes ${P_(s i):1 <= i <= g}$ and $p$ is unramified in this extension. In the
  extension $K_m/K_s$, each of the primes $P_(s i)$ is completely ramified.
] <th:cyclotomic-prime-factorization>

#proof[
  Let $omega$ range over the $phi(s)$ primitive $s$-th roots of $1$, and $zeta$
  over the $phi(p^b)$ primitive $p^b$-th roots of $1$. Then $omega zeta$ ranges
  over a full set of $phi(m)$ primitive $m$-th roots of $1$. Therefore
  $
    Phi_m lr((x))=product_(omega,zeta) (x-omega zeta),
    Phi_s lr((x))=product_omega (x-omega).
  $
  But $overline(zeta)=overline(1)$ in $overline(ZZ)$ by
  @prop:prime-power-cyclotomic-ramification, whence
  $
    overline(Phi)_m lr((x))=product_(omega,zeta)
    (x-overline(omega)overline(zeta))
    = {product_omega (x-overline(omega))}^(phi(p^b))
    ={overline(Phi)_s lr((x))}^(phi(p^b)).
  $
  #source(120)
  We now have
  $
    R_m/(p R_m) tilde.equiv overline(ZZ)[x] slash (overline(Phi)_m lr((x)))
    tilde.equiv overline(ZZ)[x] slash (overline(Phi)_s lr((x))^(phi(p^b))).
  $
  Since
  $
    overline(ZZ)[x] slash (overline(Phi)_s lr((x))^(phi(p^b))) tilde.equiv
    product_(i=1)^g overline(ZZ)[x] slash (F_i lr((x))^(phi(p^b))),
  $
  it follows at once that there are $g$ distinct prime ideals ${P_(m i)}$ of
  $R_m$ containing $p$. Further, we have
  $ R_m/P_(m i) tilde.equiv overline(ZZ)[x] slash (F_i lr((x))),1 <= i <= g. $
  On the other hand,
  $
    R_m/(p R_m)=R_m/(product_i P_(s i)R_m)
    tilde.equiv product_(i=1)^g R_m/(P_(s i)R_m).
  $
  Comparing this with the previous formula, we obtain
  $P_(s i)R_m=P_(m i)^(phi(p^b))$, and $R_m/P_(m i) tilde.equiv R_s/P_(s i)$ for
  each $i$. This completes the proof.
]

#exercises-heading

#exercise[
  Prove that every Dedekind domain $R$ is hereditary.

  #hint([@exc:dedekind-hereditary])[
    Let $J$ be an ideal of $R$. Since $J J^(-1)=R$, we may write
    $1=sum_(i=1)^n x_i y_i$, $x_i in J$, $y_i in J^(-1)$. Define maps
    $alpha,beta$, where
    #ideal-splitting-diagram
    by
    $
      alpha(r_1, dots, r_n)=sum r_i x_i,
      beta(x)=(x y_1,dots,x y_n).
    $
    Then $alpha beta=1_J$, whence $J$ is a direct summand of $R^((n))$. See also
    @lem:dual-basis.
  ]
] <exc:dedekind-hereditary>

#exercise[
  Let $L$ be a sublattice of the $R$-lattice $M$, where $R$ is any integral
  domain. Prove that $L$ is $R$-pure in $M$ if and only if $L inter r M=r L$ for
  each nonzero $r in R$.
] <exc:pure-lattice-intersection>

#exercise[
  Let $R$ be a Dedekind domain. Show that every torsionfree $R$-module is
  $R$-flat.

  #hint([@exc:dedekind-torsionfree-flat])[
    Use @prop:flat-from-finitely-generated-submodules and the fact that every
    $R$-lattice is projective.
  ]
] <exc:dedekind-torsionfree-flat>

#exercise[
  Keeping the notation of @eq:prime-ideal-factorization, show that
  $N_(L/K) lr((P_i))="ord"_R S/P_i$. Deduce that for each integral ideal $J$ of
  $S$, $N_(L/K) lr((J))="ord"_R S/J$.

  #source(121)
  #hint([@exc:norm-ideal-order])[
    See @bib:Reiner1975[MO (4.31iii)].
  ]
] <exc:norm-ideal-order>

#exercise[
  Let $P$ be a maximal ideal of the commutative ring $R$, and let $M$ be a
  finitely generated $R$-module. Set
  $ "ann"_R M={r in R:r M=0}. $
  Prove that the localization $M_P$ is $0$ if and only if $P+"ann"_R M=R$.
] <exc:localization-zero-annihilator>

#exercise[
  Let $R'=S^(-1)R$, where $S$ is a multiplicative subset of the commutative ring
  $R$. Show that for each $R'$-module $M$, there is an $R'$-isomorphism
  $mu:R' times.o_R M tilde.equiv M$ defined by setting $mu(r' times.o m)=r'm$,
  $r' in R'$, $m in M$.

  #hint([@exc:localized-module-tensor])[
    Each element of $R' times.o_R M$ is expressible as a finite sum
    $sum s^(-1)r_i times.o m_i$, where $s in S$, $r_i in R$, $m_i in M$. If this
    element lies in the kernel of $mu$, then $sum r_i m_i=0$, whence also
    $sum s^(-1)r_i times.o m_i
    =s^(-1) times.o sum r_i m_i=0$.
  ]
] <exc:localized-module-tensor>

#exercise[
  Let $R$ be a Dedekind domain with quotient field $K$, and let $M$ and $N$ be a
  pair of full $R$-lattices in a f.d. $K$-space $V$. Show that $M_P=N_P$ a.e.,
  as $P$ ranges over all maximal ideals of $R$.

  #hint([@exc:lattices-localizations-almost-everywhere])[
    Choose nonzero $r,s in R$ such that $r M subset.eq N subset.eq s^(-1) M$.
    Then $M_P=N_P$ whenever $r s in.not P$.
  ]
] <exc:lattices-localizations-almost-everywhere>

#exercise[
  Let $L$ be a finite separable extension of the field $K$, and let $S$ be the
  integral closure of $R$ in $L$, where $R$ is a Dedekind domain with field of
  quotients $K$. Let $T$ be the trace map $T_(L/K)$, and let $D$ be the
  different $D(S/R)$ as in §@ss:dedekind-ideal-theory. Put
  $ J=T_(L/K) lr((S))={T(s):s in S}. $
  Show that $J$ is the smallest ideal of $R$ such that $J S$ divides $D$.

  #hint([@exc:trace-ideal-different])[
    Clearly $T_(L/K) lr((S))$ is a nonzero ideal of $R$. For any nonzero ideal
    $I$ of $R$, we have
    $
      T(S) subset.eq I <=> T(I^(-1)S) subset.eq R <=>
      I^(-1)S subset.eq D^(-1) <=> D subset.eq I S.
    $
    Then $J$ is the smallest such $I$.
  ]
] <exc:trace-ideal-different>

#exercise[
  Let the subscript $P$ denote localization at a maximal ideal $P$ of $R$. Show
  that
  $ T_(L/K) lr((S_P))={T_(L/K) lr((S))}_P. $
] <exc:trace-localization>

#exercise[
  Keep the notation of @eq:prime-ideal-factorization and the discussion
  following it, and let $overline(R)=R/P$, $overline(S)_i=S/P_i$, and let
  $phi_i:S -> overline(S)_i$ be the canonical surjection, $1 <= i <= g$. For
  each $a in S$, let $f(X)="char. pol."_(L/K) lr((a)) in R[X]$, and let
  $overline(f)(X)$ be its image in $overline(R)[X]$. Then $a$ acts on the
  $overline(R)$-module $overline(S)_i$ as multiplication by $phi_i lr((a))$. Let
  $
    h_i lr((X))="char. pol."_(overline(S)_i/overline(R)) lr((phi_i lr((a)))),
    1 <= i <= g.
  $
  #source(122)
  Show that
  $ overline(f(X))=product_(i=1)^g {h_i lr((X))}^(e_i). $
  Deduce from this that
  $
    overline(T_(L/K) lr((a)))=
    sum_(i=1)^g overline(e)_i T_i lr((phi_i lr((a)))),
  $
  <eq:trace-residue-fields>
  where $T_i$ denotes the trace from $overline(S)_i$ to $overline(R)$.

  #hint([@exc:characteristic-polynomial-residue-fields])[
    If we replace $R$ by its localization $R_P$, and $S$ by $S_P$, then the
    hypotheses and conclusions are unchanged. Changing notation, assume now that
    $R$ is a P.I.D., and let $S=op("⨁", limits: #true)_1^n R x_i$. Set
    $ a x_j=sum_i a_(i j)x_i,a_(i j) in R, $
    so $f(X)$ is the characteristic polynomial of the $n times n$ matrix
    $(a_(i j))$. Then $S/(P S)=op("⨁", limits: #true) overline(R)overline(x)_i$,
    so $overline(f(X))$ is the characteristic polynomial of $a$ acting on the
    $overline(R)$-space $S/(P S)$.

    Now $S/(P S) tilde.equiv product_(i=1)^g S/P_i^(e_i)$ by
    @eq:prime-ideal-factorization, and each $S/P_i^(e_i)$ has an $S$-composition
    series
    $
      S/P_i^(e_i) supset P_i/P_i^(e_i) supset P_i^2/P_i^(e_i)
      supset dots supset P_i^(e_i)/P_i^(e_i)=0.
    $
    Each of the $e_i$ composition factors is isomorphic to $overline(S)_i$ (see
    @bib:CurtisReiner1962[CR (18.24)]). Therefore the characteristic polynomial
    of $a$ acting on $S/P_i^(e_i)$ is ${h_i lr((X))}^(e_i)$, which gives the
    formula for $overline(f(X))$. This formula implies @eq:trace-residue-fields
    at once.
  ]
] <exc:characteristic-polynomial-residue-fields>

#exercise[
  Keep the above notation. Show that $P_i^(e_i-1)$ divides the different
  $D(S/R)$ for each $i$. Prove also that
  $
    P S divides D <=> T_(L/K) lr((S)) subset.eq P <=>
    overline(e)_i T_i lr((overline(S)_i))=0 "for" 1 <= i <= g.
  $
  <eq:different-trace-ramification>

  #hint([@exc:different-ramification-bound])[
    Since each $phi_i lr((a))=0$ for $a in P_1 dots.c P_g$,
    @eq:trace-residue-fields gives
    $ T(P_1 dots.c P_g) subset.eq P, $
    whence $P^(-1)P_1 dots.c P_g subset.eq D^(-1)$. Therefore
    $D subset.eq product P_i^(e_i-1)$. The first equivalence in
    @eq:different-trace-ramification follows from
    Exercise~@exc:trace-ideal-different, the second from
    @eq:trace-residue-fields.
  ]
] <exc:different-ramification-bound>

#exercise[
  Keeping the above notation, call the maximal ideal $P_i$ _tamely ramified_
  over $R$#idx("ramified", "tamely")#idx("tamely ramified") if
  $overline(e)_i T_i$ is not the zero map on $overline(S)_i$. Show that $P_i$ is
  tamely ramified if and only if
  $ overline(e)_i != 0 "and" overline(S)_i "is separable over" overline(R). $
  Show further that $T_(L/K) lr((S)) subset.eq.not P$ if and only if there
  exists at least one maximal ideal $P_i$ of $S$ containing $P$ such that $P_i$
  is tamely ramified over $R$.
] <exc:tame-ramification-trace>

#source(123)
#exercise[
  We call $S$ _tamely ramified_#idx("ramified", "tamely")#idx(
    "tamely ramified",
  )#footnote[
    Some authors reserve this terminology for the case where every maximal ideal
    $P_i$ of $S$ is tamely ramified over $R$; we shall not take this point of
    view here, since for our purposes the crucial question will be whether
    $T_(L/K) lr((S))=R$.
  ] over $R$ if for each maximal ideal $P$ of $R$, there exists at least one
  maximal ideal $P_i$ of $S$ such that
  $ P_i supset.eq P,P_i "is tamely ramified over" R. $
  Show that $S$ is tamely ramified over $R$ if and only if $T_(L/K) lr((S))=R$.

  #hint([@exc:tame-extension-trace-surjective])[
    $T_(L/K) lr((S))=R$ if and only if $T_(L/K) lr((S)) subset.eq.not P$ for
    each $P$.
  ]
] <exc:tame-extension-trace-surjective>

#exercise[
  Keep the notation of @eq:cyclotomic-field-integers, and let $m=p^b$ where $p$
  is an odd prime and $b >= 1$. Show that $R_m$ is tamely ramified over $ZZ$ if
  and only if $b=1$. What is the corresponding result when $p=2$?

  #hint([@exc:tame-cyclotomic-prime-powers])[
    Use @th:cyclotomic-prime-factorization with $b=1$.
  ]
] <exc:tame-cyclotomic-prime-powers>

#exercise[
  Let $R$ be a Dedekind domain with quotient field $K$, and let $S$ be the
  integral closure of $R$ in a finite Galois extension $L$ of $K$ with Galois
  group $G$. View $S$ as left $R G$-module, by setting
  $
    (sum_(sigma in G) a_sigma sigma)s=sum_(sigma in G) a_sigma sigma(s),
    a_sigma in R.
  $
  Show that if $T_(L/K) lr((S))=R$, then $S$ is a projective $R G$-module.

  #hint([@exc:trace-surjective-galois-projective])[
    Let $X$ be any $R G$-module, and let $theta:X -> S$ be an $R G$-surjection.
    Since $S$ is $R$-projective, there exists an $R$-homomorphism $psi:S -> X$
    such that $theta psi="identity map"$ on $S$. Put
    $ psi'=sum_(sigma in G) sigma dot psi_(s_0) dot sigma^(-1), $
    where $s_0$ is an element of $S$ of trace $1$. Then $psi'$ is an
    $R G$-homomorphism from $S$ to $X$ such that $theta psi'="identity map"$ on
    $S$. Thus, every $R G$-surjection $theta:X -> S$ is $R G$-split, so $S$ is
    $R G$-projective.
  ]
] <exc:trace-surjective-galois-projective>
