#import "main-defs.typ": *

#heading(level: 1)[
  Introduction to Modular Representations
] <ch:modular-representations>

#source(423)
This chapter contains an introduction to Brauer’s theory of modular
representations, to be followed in Chapter~9 of Volume~II by an account of the
theory of blocks. Let $G$ be a finite group, and $p$ a rational prime number
dividing the order of $G$. The _$p$-local structure_#idx("p-local structure") of
$G$ is the family of $p$-subgroups of $G$, together with their normalizers. The
$p$-local structures of $G$, for various primes $p$, determine the structure of
$G$ to a considerable extent, and have played a central role in the problem of
classifying finite simple groups.

A main objective of Brauer’s theory has been to relate the character theory of
$G$ over the complex field to the $p$-local structures of $G$ for primes $p$
dividing $|G|$. The theory began with Brauer’s work on representations of a
finite group $G$ over a modular field $k$ of characteristic $p$. In its present
form, it is the study of the representation theories of $G$ over three rings
$R$, $K$, and $k$, and their interrelationships. Here, the ring $R$ is a
discrete valuation ring (d.v.r.) with quotient field $K$, maximal ideal
$frak(p)$ and residue class field $k=R slash frak(p)$ of characteristic $p$.
Given an $R G$-lattice $M$, we form the $K G$-module $K M=K times.o_R M$, and
the $k G$-module $overline(M)=M slash frak(p)M$, and study the connections among
$M$, $K M$, and $overline(M)$. The most important situation is that where $K$ is
an algebraic number field which is a splitting field for $G$. We can then relate
$K G$-modules and their characters to the structure of $R G$-lattices and
$k G$-modules, and to the $p$-local structure of $G$.

The study of $R G$-lattices and $k G$-modules offers many new challenges. The
behavior of $R G$-lattices, studied in this chapter by the methods of Brauer and
Green, provides a useful introduction to the general theory of integral
representations, to be considered in greater detail in Chapters
@ch:integral-representations and @ch:local-global-integral-representations. On
the other hand, since $k G$-modules need not be semisimple, the machinery of
semisimple rings and modules cannot be applied directly to the investigation of
$k G$-modules. Instead, we shall use the theory of artinian rings with radical,
and our results will often be stated in terms of Grothendieck groups and Brauer
characters.
