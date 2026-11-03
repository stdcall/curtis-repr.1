#import "main-defs.typ": *

#source(639)
#heading(level: 1)[
  Local and Global Theory of Integral Representations
] <ch:local-global-integral-representations>

In these introductory remarks, let $Lambda$ be an $R$-order in a f.d. separable
$K$-algebra $A$, where $R$ is a Dedekind domain with quotient field $K$. In
Chapter~@ch:integral-representations, the basic idea was to study a
$Lambda$-lattice $M$ by relating it to the $A$-module $K M$ which it generates.
This led naturally to the problem of describing $M$ as an extension of a
$Lambda$-lattice $N$ by another $Lambda$-lattice $L$. The extension problem was
treated by introducing the $R$-module $op("Ext")_Lambda^1 lr((N,L))$, which
could be calculated from the behavior of the localizations ${N_P}$ and ${L_P}$
at some finite set of maximal ideals $P$ of $R$.

The preceding remark suggests that the knowledge of the localizations ${M_P}$ of
a $Lambda$-lattice $M$ will provide more information about $M$ than does the
$A$-module $K M$. We also expect that some finite set of $P$'s will play a basic
role in the relationship between $M$ and the ${M_P}$, and it is the study of
this relationship which is the central theme of
Chapter~@ch:local-global-integral-representations.

As a first step in this program, §@sec:local-theory is devoted to a closer look
at the local situation, where $R$ is a d.v.r. with maximal ideal $P$. Parts of
the discussion in Chapter~@ch:modular-representations, where $Lambda$ is the
group ring $R G$ of a finite group $G$, anticipate some of the results of
§@sec:local-theory. In general, however, the point of view here is considerably
different from that in Chapter~@ch:modular-representations, and we are
interested in $Lambda$-lattices themselves, rather than merely in using them as
an intermediate tool for relating ordinary and modular representations of $G$.
We shall continue to use the notation of Chapter~@ch:integral-representations,
denoting a maximal ideal of $R$ by $P$, rather than $frak(p)$ as in
Chapter~@ch:modular-representations. Further, $k$ will now be used as an index,
rather than for the residue class field of $R$.

Section~@sec:local-theory begins with a review of relevant material from the
Introduction, especially
§§@sec:radicals–@sec:idempotents-krull-schmidt-projective-covers. We then
consider properties of a $Lambda$-lattice $M$, where $Lambda$ is an arbitrary
$R$-order. For example, we shall see that projective $Lambda$-lattices are
completely determined by their behavior mod $P$. Maranda's Theorems generalize
this fact to show that an arbitrary $Lambda$-lattice $M$ is determined by its
behavior mod $P^k$, for some sufficiently large $k$ which depends on $Lambda$,
but not on $M$.

In §@ss:extension-ground-ring-local-theory we introduce the technique of
extension of the ground ring. This is a natural idea, in view of the importance
of ground field extension and
#source(640)
splitting fields in the theory of representations of algebras. The results of
§@ss:extension-ground-ring-local-theory were already needed in
Chapter~@ch:modular-representations, and will be used again later in this
Chapter.

Section~@sec:genus introduces the concept of genus, which is of decisive
importance for all further discussion of integral representations. If $Lambda$
is an $R$-order, where $R$ is a Dedekind domain, we place two $Lambda$-lattices
$M$ and $N$ in the same genus if they are locally isomorphic (that is,
$M_P tilde.equiv N_P$ as $Lambda_P$-lattices, for each $P$). Only finitely many
$P$'s are of significance in this definition. Many properties of a
$Lambda$-lattice $M$, especially those relating to decomposability and direct
sums, depend only on the genus of $M$, rather than the $Lambda$-isomorphism
class of $M$. This circle of ideas leads naturally to the concept of the locally
free class group $"Cl" Lambda$ of an order $Lambda$. We interpret this class
group in terms of ideles, and postpone until Chapter~11 of Volume~II the deeper
study of this class group.

In §@sec:projective-lattices we prove Swan's celebrated theorem that every
projective $ZZ G$-lattice is in the same genus as a free $ZZ G$-lattice.

We call an order $Lambda$ of _finite representation type_ if the number of
isomorphism classes of indecomposable $Lambda$-lattices is finite. In
§@sec:finite-representation-type, we begin by proving Jones' Theorem, which
tells us that the question, as to whether $Lambda$ has finite representation
type, can always be reduced to the case in which the ground ring $R$ is a
complete d.v.r. We then sketch a proof of the Jacobinski, Drozd-Roiter Theorem
which gives necessary and sufficient conditions that a commutative order have
finite representation type.

Section~@sec:examples-integral-representations is devoted to calculations of
indecomposable representations of various groups and orders. Here we use much of
the machinery developed in §§@sec:extensions-lattices, @sec:twisted-group-rings.
The remaining sections of this chapter are of interest in themselves, but they
will be used infrequently in later chapters. In §@sec:invertible-ideals we prove
the beautiful theorem of Dade-Taussky-Zassenhaus, using a surprising result due
to Fröhlich. Section~@sec:krull-schmidt-discrete-valuations is devoted to a
discussion as to whether the K-S-A Theorem holds for $Lambda$-lattices, where
$Lambda$ is an order over a non-complete d.v.r. As we shall see, this is the
case in certain very special situations, but counterexamples are known in many
other cases.

Finally, §@sec:bass-gorenstein-orders contains an introduction to the theory of
Bass and Gorenstein orders. This theory may be viewed as a generalization of the
theory of hereditary orders. Since every integral group ring is a Gorenstein
order (=weakly self-injective order), the ideas in §@sec:bass-gorenstein-orders
are sometimes helpful. They form the cornerstone of the Drozd-Roiter approach to
the problem of finite representation type.
