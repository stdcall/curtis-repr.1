#import "main-defs.typ": *

#heading(level: 1)[
  Integral Representations: Orders and Lattices
] <ch:integral-representations>

#source(542)
This is the first of several chapters on integral representation theory, and it
may be worthwhile to begin with a broad description of this theory. We may think
of it as a refinement of ordinary and modular representation theory, as well as
a generalization of certain parts of algebraic number theory. Many of the key
results are obtained by applying number-theoretic techniques to problems in
ordinary representation theory. At the same time, concepts and methods from
homological algebra play a significant role in the theory. In a rough sense, we
may regard integral representation theory as a central core which connects
various topics in ordinary and modular representation theory, algebraic number
theory, and algebraic $K$-theory.

The deeper aspects of the study of algebraic number fields depend on knowledge
of the _rings of integers_ in these fields. Basic results from field theory thus
appear as rough versions of deeper facts about rings of integers. For example,
let $R=op("alg. int."){K}$, where $K$ is an algebraic number field. Let $E$ be a
finite extension field of $K$ of degree $n$, and $S=op("alg. int."){E}$. Then
the trivial result that $E$ has a $K$-basis of $n$ elements is a consequence of
the deeper fact that $S$ is isomorphic (as $R$-module) to an external direct sum
of $n$ ideals of $R$.

We have already observed in Chapter~@ch:modular-representations that if
$(K,R,k)$ is a $p$-modular system, and $G$ is a finite group, then the
$R G$-lattices play an intermediate role in the passage from $K G$-modules to
$k G$-modules. Thus, given a f.g. $K G$-module $V$, we choose an $R G$-lattice
$M$ whose elements span $V$, and then form the $k G$-module
$overline(M)=M slash P M$, where $P$ is the maximal ideal#footnote[
  In Chapters @ch:integral-representations and
  @ch:local-global-integral-representations, we revert to the notation used in
  §@sec:dedekind-domains, and denote a maximal ideal of $R$ by $P$ rather than
  $frak(p)$.
] of the d.v.r. $R$. This procedure allows us to define the decomposition map,
which is the starting point of modular representation theory.

In another sense, the study of $K G$-modules and $k G$-modules is just a first
approximation to the investigation of $R G$-lattices. Indeed, given an
$R G$-lattice $M$, we first consider the $K G$-module $K M$ spanned by $M$. Once
this is known,
#source(543)
we may then turn to more delicate questions, such as those involving the
connections between $M$ and the modules $M slash P^t M$, $t >= 1$. For example,
it turns out that $M$ is projective $R G$-lattice if and only if $M slash P M$
is a projective $k G$-module, and that in this case the isomorphism class of $M$
is determined by that of $M slash P M$. On the other hand, a non-projective
lattice $M$ is determined by its behavior mod $P^t$ for some sufficiently large
$t$.

The general framework of integral representation theory is as follows. Given a
$K G$-module $V$, we first consider all $R G$-lattices $M$ in $V$. By the
Jordan-Zassenhaus Theorem, there are finitely many isomorphism classes of such
lattices. In the case where $R=op("alg. int."){K}$, these isomorphism classes
are then partitioned into genera by means of congruence properties.
Specifically, two $R G$-lattices $M,N$ spanning $V$ are placed in the same genus
if for every maximal ideal $P$ of $R$, the $P$-adic completions $hat(M)_P$ and
$hat(N)_P$ are $hat(R)_P G$-isomorphic. Equivalently, this occurs if for each
$P$, the lattices $M$ and $N$ mod $P^t$ are isomorphic for large enough $t$. The
concept of genus is central to the entire theory, since it leads to a natural
generalization of the ideal class group occurring in algebraic number theory.
This new class group $op("Cl") R G$ turns out to be intimately connected with
the $K$-theory of $R G$, and has important applications to topology, since
certain topological invariants have values in this class group.

Next, we note that any $K G$-submodule $W$ of a $K G$-module $V$ must be a
direct summand of $V$. The analogous statement fails for $R G$-lattices, just as
it fails for $k G$-modules if $k$ is a field and $char k$ divides $|G|$. In
studying sublattices $L$ of an $R G$-lattice $M$, one often begins by picking
out those $L$'s for which the quotient $M slash L$ is also a lattice (rather
than an arbitrary $R G$-module). Assuming that both $L$ and $M slash L$ are
known, it then becomes necessary to study the group
$op("Ext")_(R G)^1 lr((M slash L,L))$ which classifies extensions of $M slash L$
by $L$. We shall give a number of examples in which these extension groups are
calculated and used to determine all $R G$-lattices.

Just as the theory of $K G$-modules depends on the more general theory of
modules over semisimple artinian rings, the theory of $R G$-lattices depends on
the more general investigation of lattices over $R$-orders. Certain $R$-orders,
especially the maximal orders, have special properties which make them easier to
handle. One technique, used repeatedly in integral representation theory, is to
embed a given $R$-order $Lambda$ in a maximal order $Lambda'$, and then to study
$Lambda$-lattices $M$ by first investigating the corresponding $Lambda'$-lattice
$Lambda'M$ spanned by $M$. This procedure is a refinement of the step from $M$
to $K M$, and often yields useful information.

The first section of this chapter introduces the concepts of orders acting on
lattices, and the following section is devoted to the fundamental
Jordan-Zassenhaus Theorem. In Section~@sec:extensions-lattices, we consider the
technique of forming extensions of one lattice by another, and here the
discussion of Ext in §@ss:ext-tor will play a basic role. Section
@sec:maximal-hereditary-orders deals with maximal orders in separable algebras.
In Sections @sec:group-rings-maximal-orders and @sec:twisted-group-rings, we
concentrate on properties of integral
#source(544)
group rings and their twisted analogues. The chapter concludes with a discussion
of projective endomorphisms and annihilators of Ext of a pair of lattices.

In keeping with the spirit of this book, we shall concentrate on general results
rather than detailed calculations, although numerous illustrative examples will
be given. This chapter inevitably overlaps parts of @bib:CurtisReiner1962[CR]
and of “Maximal Orders” (Reiner~@bib:Reiner1975), and it is not feasible to
duplicate here any large part of these earlier works. We shall occasionally list
results from these books without proof. These books will hereafter be cited
simply as CR and MO, respectively.
