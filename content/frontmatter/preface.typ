#import "../main-defs.typ": *

#heading(level: 1, numbering: none)[Preface] <ch:preface>

#source(5)
In the past 20 years, representation theory of finite groups and associative
algebras has enjoyed a period of vigorous development. The foundations have been
strengthened and reorganized from new points of view. The applications and
connections with other parts of mathematics, while already substantial, have
grown in depth and variety and now include powerful results in directions only
dimly perceived 20 years ago. It therefore seemed worthwhile and challenging to
attempt a survey of the developments since the appearance of our first book
(Curtis and Reiner @bib:CurtisReiner1962), in the hope that such an effort might
encourage the continuation of work already begun, and might lead to further
applications.

Representation theory is concerned with the following kind of situation. We are
given an action of a finite group on some object, such as a set, a vector space
or module over a commutative ring, a simplicial complex, or an algebraic
variety. We then introduce a ring (usually a group algebra or a twisted group
algebra over an appropriate commutative ring), and we consider modules over the
ring, which capture some features of the group action. The next step is to
classify the modules so obtained, in terms of the structure of the group
algebra, the endomorphism algebras of the modules, the extension problem for the
modules, and their character theory. The aim of these efforts is to obtain
algebraic or number-theoretical information which may yield new insight about
the structure of the finite groups considered, or about their actions on the
objects studied initially.

The most extensively developed part of the subject has been the application of
representation theory and character theory to the structure of finite groups.
This area has been dominated, during the period of our survey, by the work of
Richard Brauer (1901–1977). The strength and originality of his own work,
combined with the friendly encouragement and inspiration he provided to younger
colleagues and students, make his place in the subject a special one. He lived
to see the near completion of the work that he and his predecessors Frobenius,
Burnside, and Schur all viewed as the grand task to which character theory could
make a central contribution, namely, the complete classification of finite
simple groups. It is perhaps not too much to hope that new ideas from
representation theory, combined with the extraordinary achievements of the past
decade on the structure of finite groups, will lead to #source(6)
simplifications of proofs and a better understanding of this classification
problem.

Another subject, algebraic $K$-theory, has recently approached maturity, and
exerts a strong influence on integral representation theory. This area of
research, guided by parallels with certain constructions in topology, has
suggested new problems of major importance in representation theory. Their
solution, in turn, has led to fresh applications to topology and algebraic
number theory.

A second interaction between representation theory and geometry has occurred in
the representation theory of finite groups of Lie type. In the examples where
character tables were known, there were certain representations that were
elusive and difficult to construct by standard methods. In a dramatic
breakthrough, Deligne and Lusztig discovered general methods for constructing
these and other representations through a systematic study of actions of the
groups on algebraic varieties.

Our objective in this volume, and in Volume II, is to give an essentially
self-contained account of the three main branches of representation theory:
ordinary, modular, and integral representation theory. We exhibit here numerous
interrelationships among these three subjects, thereby obtaining deeper
understanding of each of them. Our approach is not intended to be encyclopedic,
but each topic is considered in sufficient depth that the reader may obtain a
clear idea of some of the major results in the area. Our selection of topics,
from what has now become a vast subject, was guided by our aim of preparing the
reader for further work in representation theory and its applications as
described above.

As in our first book (hereafter referred to as @bib:CurtisReiner1962[CR]), we
have concentrated on general methods. However, the present book also contains
considerably sharper and more powerful computational techniques, some of which
have been developed in the past few decades. The reader will also find a greater
emphasis on methods from homological algebra and commutative ring theory, and
somewhat less on purely ring-theoretic considerations.

We have attempted to make this book relatively self-contained, and do not
presuppose familiarity with all of the contents of our previous book
@bib:CurtisReiner1962[CR]. On the other hand, we occasionally omit details of
some of the more elementary results and refer instead to material in
@bib:CurtisReiner1962[CR] for background and further information. While it has
not been possible to include in this work all of the results in
@bib:CurtisReiner1962[CR], the reader will find that most of the contents of
@bib:CurtisReiner1962[CR] are treated here in greater depth and generality.
Furthermore, in many areas we go far beyond the contents of
@bib:CurtisReiner1962[CR].

In a few of the sections in this book, we have also inserted references to the
book on _Maximal Orders_ (see Reiner @bib:Reiner1975), which we cite as
@bib:Reiner1975[MO] for brevity. In particular, some of the introductory
material in Chapter~@ch:integral-representations, especially in
§§~@sec:jordan-zassenhaus and @sec:maximal-hereditary-orders, would have
required much longer discussion had we included the relevant proofs from
@bib:Reiner1975[MO]. We have tried to include enough of the material from
@bib:Reiner1975[MO], however, so that the reader will not feel compelled to
refer back to @bib:Reiner1975[MO] during a first reading of
Chapter~@ch:integral-representations.

#source(7)
Generally speaking, we assume that the reader has a good general background in
algebra, with no more familiarity with representation theory than what is
contained in the usual first year graduate course in algebra. Where this
approach results in overlapping between this book and @bib:CurtisReiner1962[CR],
we have tried always to give either new proofs or a revised presentation.

This volume begins with a substantial @ch:introduction[Introduction]
(§§~@sec:background-algebras-groups–@sec:ext-tor-cohomology) which covers the
background from group theory, algebraic number theory, commutative and
noncommutative ring theory, modules, and homological algebra, needed for both
this volume and the next. Here some topics (such as the Morita theorems) are
treated in detail, while others are surveyed without proofs, with appropriate
references. Many readers will no doubt be familiar with substantial parts, at
least, of the @ch:introduction[Introduction], and in any case can omit (at a
first reading) whatever is not essential for those parts of the book they wish
to study.

Chapters~@ch:group-representations-character-theory and
@ch:modular-representations provide a comprehensive survey of ordinary and
modular representation theory. At least the first parts of most sections are
essential for a good understanding of the theory. Two of the main themes of
Chapter~@ch:group-representations-character-theory are the orthogonality
relations for characters, and the theory of induced modules and characters. Our
treatment of the latter, in §~@sec:clifford-theory-hecke-algebras, includes the
Conlon-Tucker-Ward extension of Clifford’s theory to describe the decomposition
of modules induced from normal subgroups, and the accompanying theory of
projective representations and twisted group algebras. We have tried to include
in §§~@sec:clifford-theory-hecke-algebras and @sec:artin-brauer-induction a
fairly complete survey of known cases where invariant characters of normal
subgroups can be extended to the group, including Gallagher’s result on
characters of normal Hall subgroups. The decomposition of induced modules from
non-normal subgroups is treated from the point of view of Hecke algebras, and
prepares the way for applications to finite groups of Lie type in Chapter 7.
There are also sections on tensor induction and transfer, special classes and
exceptional characters, and the Brauer Induction Theorem. Applications include
Mackey’s results on the decomposition of symmetric and skew-symmetric squares,
Suzuki’s CA-group Theorem, the Brauer-Suzuki Theorem on generalized quaternion
Sylow $2$-subgroups, and G. Higman’s illustration of the problem of classifying
simple groups in terms of centralizers of involutions.

Chapter~@ch:modular-representations introduces modular representation theory
through the study of the Cartan-Brauer triangle. Here, to some extent, we have
followed Serre’s elegant treatment of this subject. We then give a detailed
account of Green’s theory of vertices and sources of $R G$-lattices, including a
new proof due to Conlon and Ward of Green’s Indecomposability Criterion. We also
discuss the Green correspondence, and Thompson’s application of it to the
character theory of a group with a self-centralizing cyclic Sylow $p$-subgroup.

Chapters~@ch:integral-representations and
@ch:local-global-integral-representations are fundamental for the theory of
integral representations and can be read independently of
Chapters~@ch:group-representations-character-theory and
@ch:modular-representations, although there are many connections among all four
chapters.

In Chapter~@ch:integral-representations the following sections are of special
importance, both in this volume and the next: the introductory
§~@sec:lattices-orders; §~@sec:jordan-zassenhaus on the Jordan-Zassenhaus
#source(8) theorem; the introductory section on maximal orders, including
Theorems~@th:maximal-orders-are-hereditary,
@th:maximal-orders-wedderburn-components–@th:hereditary-orders-localization; the
beginning of §§~@sec:group-rings-maximal-orders and @sec:twisted-group-rings,
especially Theorems~@prop:group-ring-maximality,
@th:twisted-group-ring-maximality, and @th:twisted-group-ring-heredity; and the
first half of §~@sec:annihilator-ext.

In Chapter~@ch:local-global-integral-representations the following sections are
fundamental: §~@sec:local-theory on the local theory; the relation between
global and local theory in §~@sec:genus; and the results in
§~@sec:projective-lattices on projective lattices over integral group rings.

These chapters also contain numerous examples of integral representations of
group rings and orders. Here the basic sections are: §~@sec:twisted-group-rings
on twisted group rings; §§~@sec:finite-representation-type and
@sec:examples-integral-representations on finite representation type and
explicit calculations; and §~@sec:bass-gorenstein-orders on Bass and Gorenstein
orders. The results in §~@sec:invertible-ideals will be important in our
discussion of Picard groups in Chapter 11. The material in
§~@sec:bass-gorenstein-orders is a brief introduction to a rich circle of ideas
in representation theory.

In most cases, we have tried to carry each topic in this volume to the point
where further research and extensions of the methods can be considered.

The material in this volume has been used by us as a basis for full year courses
on ordinary and modular representation theory, and integral representation
theory. We have included exercises after almost every section, to increase the
book’s usefulness in connection with graduate courses or for self-study, and to
present examples and auxiliary results that should prove useful to the
researcher.

The bibliography lists only the books and articles referred to in the text of
this volume. References are listed according to the last two digits of the year
in which they appeared. More extensive bibliographies, and surveys of current
research, are available in @bib:CurtisReiner1962[CR] and also in the books
listed on the first page of the bibliography.

There remain major parts of the subject to be discussed in Volume II. These
include:

#list(
  marker: none,
  [Burnside rings and representation rings (Chapter 5).],
  [Rationality properties of group representations (Chapter 6).],
  [Representations of finite groups of Lie type (Chapter 7).],
  [Indecomposable modules (Chapter 8).],
  [Blocks (Chapter 9).],
  [Algebraic $K$-theory (Chapter 10).],
  [Class groups (Chapter 11).],
)

We have profited enormously from the generous suggestions, criticisms, and
encouragement that we have received from students, friends, and colleagues. In
particular, we wish to acknowledge the help of David Gluck, Michael Fry, Gerald
Janusz, Robert Kilmoyer, and Gary Seitz.

We wish to acknowledge the support we have received from the National Science
Foundation for our own research reported on in these volumes.

#source(9)
From the beginning, we have benefited from the continued interest of Beatrice
Shube, editor of Wiley-Interscience, and at a later stage from the assistance
and attention of David B. Kaplan, associate editor for mathematics, and the
production staff at Wiley-Interscience.

It is a pleasure to thank the very capable office staff, in particular Melody
Armstrong, Hilda Britt, Karen Cagle, Lillie Douglas, Mabel Jones, and Janet
Largent, who cheerfully kept the project moving ahead.

The entire work required the constant support, affection, and understanding of
our wives, Betsy and Irma.

Charles W. Curtis \
Irving Reiner

Eugene, Oregon \
Urbana, Illinois \
June 1981
