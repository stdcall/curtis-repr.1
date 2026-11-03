#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/07-separable.typ": *

#heading(level: 2)[
  Separable Algebras and Splitting Fields
] <sec:separable-algebras-splitting-fields>

Throughout this section, $K$ denotes a field. The underlying vector spaces of
$K$-algebras $A$ and $A$-modules $M$ are assumed to be finite dimensional. For
extension fields $E$ of $K$, we shall use the notations $A^E$, $M^E$, etc., for
the algebras $E times.o_K A$ and modules $E times.o_K M$ obtained by extension
of the ground field from $K$ to $E$ (see @bib:CurtisReiner1962[CR §~12]). We do
not require $dim_K E$ to be finite.

=== Separable Algebras and Modules <ss:separable-algebras-modules>

#definition[
  Let $A$ be a $K$-algebra, and $M$ a left $A$-module. We call $A$ a _separable
  $K$-algebra_#idx("separable algebra") if for every extension field $E$ over
  $K$, including $K$ itself, $A^E$ is a semisimple $E$-algebra. Similarly, $M$
  is a _separable $A$-module_#idx("separable module") if $M^E$ is a semisimple
  $A^E$-module for every extension field $E$ over $K$.
] <def:separable-algebra-module>

#remarks(numbered: false)[
  #enum(
    numbering: "(i)",
    [$A$ is a separable $K$-algebra if and only if the left regular module
      $attach(A, bl: A)$ is a separable $A$-module (by
      @prop:semisimple-ring-criteria).],
    [Every module $M$ over a separable algebra $A$ is separable (again by
      @prop:semisimple-ring-criteria).],
  )
]

#lemma[
  The following statements concerning a $K$-algebra $A$ are equivalent:
  #enum(
    numbering: "(i)",
    [$A$ is a separable $K$-algebra.],
    [#source(165)
      $A^E$ is a split semisimple $E$-algebra for some finite extension field
      $E$ over $K$.],
    [$A^Omega$ is a split semisimple $Omega$-algebra, where $Omega$ is an
      algebraic closure of $K$.],
  )
] <lem:separable-split-extension>

#proof[
  (i)$arrow.r.double$(iii). By the definition of separability, $A^Omega$ is a
  semisimple $Omega$-algebra, and hence is split semisimple, from
  §@ss:semisimple-algebras-fields (see, in particular, the remark following
  @def:split-semisimple-algebra).

  (iii)$arrow.r.double$(ii). Let ${e_(j k)^i}$ be a set of matrix units in
  $A^Omega$ such that for each fixed $i$, ${e_(j k)^i}_(j k)$ is an
  $Omega$-basis for a Wedderburn component of $A^Omega$ (see
  Exercise~@exc:matrix-units-split-algebra). The matrix units ${e_(j k)^i}$ can
  be expressed as $Omega$-linear combinations of a fixed $K$-basis of $A$, in
  such a way that only a finite number of elements of $Omega$ are involved.
  These coefficients generate a finite algebraic extension $E$ of $K$, and the
  matrix units ${e_(j k)^i}$ then belong to $A^E$, and form an $E$-basis of
  $A^E$. It follows from Exercise~@exc:matrix-units-split-algebra that $A^E$ is
  a split semisimple $E$-algebra.

  (ii)$arrow.r.double$(i). Let $A^E$ be a split semisimple $E$-algebra for some
  finite extension field $E$ of $K$. Suppose that $A^F$ is not semisimple for
  some other extension field $F$ of $K$, and let $L$ be a composite field
  extension of $E$ and $F$ over $K$ (see
  Exercise~@exc:composite-field-extension). Then there are $K$-embeddings
  $sigma:E -> L$ and $tau:F -> L$, which we shall view as inclusions, such that
  $L=E dot F$. Then $A^L$ is a split semisimple $L$-algebra, since
  $A^L=(A^E)^L$. On the other hand, $rad A^F != 0$ since $A^F$ is not semisimple
  (see @th:artinian-semisimple-radical-zero). But then $L times.o_F rad A^F$ is
  a nonzero nilpotent two-sided ideal in $A^L$, which contradicts our previous
  statement that $A^L$ is semisimple. We have thus shown that $A^F$ is
  semisimple for every $F$ over $K$, which completes the proof.
]

#lemma[
  A $K$-algebra $A$ is separable if and only if $A^E$ is semisimple for all
  extension fields $E$ of $K$ such that $dim_K E$ is finite.
] <lem:separable-finite-extensions>

#proof[
  One way is clear. For the other, suppose that $A^E$ is semisimple for every
  finite extension $E$ of $K$, and let $Omega$ be an algebraic closure of $K$.
  Let $E$ range over all fields such that
  $ K subset.eq E subset.eq Omega, quad dim_K E "finite". $
  For each such $E$, $(rad A^Omega) inter A^E$ is a nilpotent ideal of $A^E$,
  hence is $0$ since $rad A^E=0$ by hypothesis. But every element of $A^Omega$
  lies in $A^E$ for some $E$, which shows that $rad A^Omega=0$. The first part
  of the proof of @lem:separable-split-extension then implies that $A$ is
  separable, and the lemma is established.
]

Let $E$ be a finite extension field of $K$ of degree $n$. We call $E$ a
_separable extension_#idx("separable extension field") of $K$ if there exist $n$
distinct embeddings ${sigma_1,dots,sigma_n}$ of $E$ into some algebraic closure
$Omega$ of $K$, such that each $sigma_i$ fixes $K$ elementwise (see
Lang~@bib:Lang1965, VII, §4). Equivalently, $E$ is separable over $K$ if
$E tilde.equiv K[x] slash (f(x))$, where $f(x) in K[x]$ is a monic separable
polynomial which is irreducible in $K[x]$.

#source(166)
#proposition[
  Let $E$ be a finite extension field of $K$. Then $E$ is separable as an
  extension field of $K$ if and only if $E$ is a separable $K$-algebra.
] <prop:separable-field-algebra>

#proof[
  Assume $E$ is a separable field extension of $K$, and let $Omega$ be an
  algebraic closure of $K$. Let ${sigma_1,dots,sigma_n}$ be the distinct
  $K$-embeddings of $E$ into $Omega$. By Artin's Theorem (see
  Exercise~@exc:artin-embeddings-independent), ${sigma_1,dots,sigma_n}$ are
  linearly independent over $Omega$. Now let ${w_1,dots,w_n}$ be a $K$-basis of
  $E$, and put
  $ xi_i=(sigma_i lr((w_1)),dots,sigma_i lr((w_n))), quad 1 <= i <= n. $
  Then the vectors $xi_1,dots,xi_n$ in $Omega^((n))$ are linearly independent
  over $Omega$. It follows that the $n times n$ matrix $(sigma_i lr((w_j)))$ is
  invertible, and so its columns are also linearly independent over $Omega$. Let
  $eta_i$ be the transpose of the $i$-th column, that is,
  $ eta_i=(sigma_1 lr((w_i)),dots,sigma_n lr((w_i))), quad 1 <= i <= n. $
  Then the vectors ${eta_i}$ are linearly independent over $Omega$.

  View each $eta_i$ as an element of the _algebra_
  $Omega^((n))=Omega plus.o dots.c plus.o Omega$. Then for $1 <= i,j <= n$,
  $
    w_i w_j=sum alpha_(i j k)w_k, quad alpha_(i j k) in K
    => eta_i eta_j=sum alpha_(i j k)eta_k.
  $
  Let $phi:Omega times.o_K E -> Omega^((n))$ be the map defined by
  $
    phi lr({sum_(i=1)^n c_i lr((1 times.o w_i))})=sum_(i=1)^n c_i eta_i,
    c_i in Omega,1 <= i <= n.
  $
  Then $phi$ gives an isomorphism of $Omega$-algebras. But $Omega^((n))$ is a
  split semisimple $Omega$-algebra, whence so is $Omega times.o_K E$. This shows
  that $E^Omega$ is split semisimple, whence $E$ is a separable $K$-algebra by
  Lemma~@lem:separable-split-extension.

  Conversely, suppose that $E$ is a separable $K$-algebra, and let $Omega$ be an
  algebraic closure of $K$, as above. Then $Omega times.o_K E$ is a commutative
  split semisimple $Omega$-algebra (by @lem:separable-split-extension), since
  $E$ is a separable $K$-algebra. Hence there exists an isomorphism of
  $Omega$-algebras
  $
    phi:Omega times.o_K E tilde.equiv Omega^((n))
    =Omega plus.o dots.c plus.o Omega.
  $
  For each $a in Omega times.o_K E$, let us write
  $ phi(a)=(omega_1 lr((a)),dots,omega_n lr((a))) in Omega^((n)). $
  For each $i$, the map $a -> 1 times.o a -> omega_i lr((1 times.o a))$,
  $a in E$, gives a $K$-embedding of $E$ into $Omega$. For $i != j$ the
  embeddings are distinct, since otherwise $omega_i lr((a))=omega_j lr((a))$ for
  all $a in Omega times.o_K E$, contradicting the fact that $phi$ is an
  $Omega$-isomorphism. This completes the proof.
]

#source(167)
We now seek a criterion for a semisimple left $A$-module $M$ to be separable,
where $A$ is an arbitrary f.d. $K$-algebra. We note first that submodules of
separable modules are separable, and direct sums of separable modules are
separable. Moreover, if $M$ is a separable left $A$-module, then $M^E$ is a
separable left $A^E$-module for every extension $E$ of $K$. The main result is
the following theorem from Bourbaki~@bib:Bourbaki1958, for which we supply a new
proof, based on the Morita theorem and its applications to tensor products in
§@ss:tensor-simple-algebras-modules.

#theorem[
  A semisimple left $A$-module $L$ is separable if and only if for every simple
  submodule $M$ of $L$, the center of the division algebra $End_A lr((M))$ is a
  finite separable extension field of $K$.
] <th:separable-module-centralizer-center>

#proof[
  By the remarks preceding the statement of the theorem, it suffices to prove
  that a simple left $A$-module $M$ is separable if and only if the center $F$
  of $End_A lr((M))$ is separable over $K$. By
  Lemma~@lem:separable-finite-extensions, we can test for separability by using
  finite extension fields $E$ over $K$. Let $times.o$ denote $times.o_K$ for
  this proof, and let $E$ be a finite extension field of $K$. Then $E times.o M$
  is a left $(E times.o A)$-module. Put
  $
    D={End_A lr((M))}^circle.small, quad
    E={End_E lr((E))}^circle.small tilde.equiv E,
  $
  so $D$ is a division algebra with center $F$. View $M$ as an $(A,D)$-bimodule,
  and $E$ as $(E,E)$-bimodule. By Prop.~@prop:tensor-simple-module-centralizers,
  the lattice of $(E times.o A)$-submodules of $E times.o M$ is isomorphic to
  the lattice of left ideals in $E times.o D$.

  Next, $E times.o M$ is semisimple if and only if $rad(E times.o M)=0$ by
  Exercise~@exc:artinian-module-radical-zero. Further, by §@sec:radicals, the
  radical of a module is the intersection of its maximal submodules. Hence the
  vanishing of the radical is preserved under a lattice isomorphism, which shows
  that $E times.o M$ is semisimple if and only if $E times.o D$ is semisimple.
  Thus, $M$ is separable over $K$ if and only if $E times.o D$ is semisimple for
  each finite extension field $E$ of $K$.

  We have set $F="center of" D$; then $E$ and $D$ are finite dimensional simple
  $K$-algebras, with centers $E$ and $F$, respectively. By
  Theorem~@th:tensor-simple-algebras(ii), it follows that $E times.o D$ is
  semisimple if and only if $E times.o F$ is semisimple. But $E times.o F$ is
  semisimple for all $E$ (finite over $K$) if and only if $F$ is a separable
  field extension of $K$, by @prop:separable-field-algebra. This completes the
  proof of the theorem.
]

#corollary[
  Let $A$ be a semisimple $K$-algebra. A necessary and sufficient condition for
  $A$ to be separable is that the centers of the division algebras associated
  with the Wedderburn components of $A$ are separable extension fields of $K$.
] <cor:separable-algebra-wedderburn-centers>

#proof[
  From the Wedderburn Theorems in §@ss:semisimple-modules-rings, the division
  algebras associated with the Wedderburn components coincide with the division
  algebras ${End_A lr((M))}$, where $M$ ranges over the simple submodules of the
  left regular module $attach(A, bl: A)$. The result now follows from
  @th:separable-module-centralizer-center because of the fact, noted earlier,
  that $A$ is a separable $K$-algebra if and only if the left regular module is
  separable.
]

#source(168)
We now give a number of useful applications of the main theorem.

#proposition[
  Let $A$ and $B$ be $K$-algebras, let $M$ and $N$ be semisimple modules over
  $A$ and $B$, and assume that $N$ is separable over $K$. Then $M times.o_K N$
  is a semisimple $(A times.o_K B)$-module.
] <prop:tensor-semisimple-separable-modules>

#proof[
  First consider the case where both $M$ and $N$ are simple, and $N$ is
  separable. Let $D={End_A lr((M))}^circle.small$,
  $E={End_B lr((N))}^circle.small$, and let $S=c(D)$ and $T=c(E)$ be the centers
  of the division algebras $D$ and $E$. By
  Theorem~@th:separable-module-centralizer-center, $T$ is a separable extension
  field of $K$, and by Proposition~@prop:separable-field-algebra,
  $S times.o_K T$ is a semisimple $K$-algebra. By
  Theorem~@th:tensor-simple-algebras, $D times.o_K E$ is a semisimple
  $K$-algebra, and by Proposition~@prop:tensor-simple-module-centralizers(iii),
  it follows that $M times.o_K N$ is a semisimple $(A times.o_K B)$-module.

  In the general case we have $M=plus.o M_i$, $N=plus.o N_j$, with ${M_i}$ and
  ${N_j}$ simple submodules of $M$ and $N$. Moreover, the submodules $N_j$ are
  all separable, as submodules of a separable module. Then
  $M times.o_K N=op("⨁", limits: #true)_(i,j) M_i times.o_K N_j$. By the first
  part of the proof all the modules $M_i times.o_K N_j$ are semisimple, and
  hence $M times.o_K N$ is semisimple, as required.
]

#corollary[
  #enum(
    numbering: "(i)",
    [Let $A$ be a semisimple $K$-algebra and $B$ a separable $K$-algebra. Then
      $A times.o_K B$ is a semisimple algebra.],
    [Let $M$ be a semisimple left $A$-module, and $E$ a finite separable
      extension field of $K$. Then $M^E$ is a semisimple $A^E$-module.],
  )
] <cor:separable-extension-semisimplicity>

#theorem[
  Let $A$ be a $K$-algebra, $E$ an extension field of $K$, and suppose that for
  each simple $A$-module $M$, the $A^E$-module $M^E$ is semisimple. (This
  hypothesis certainly holds whenever $E$ is a finite separable extension of
  $K$.) Then
  #enum(
    numbering: "(i)",
    [$(A slash (rad A))^E tilde.equiv A^E slash (rad A)^E$, and
      $rad(A^E)=(rad A)^E$.],
    [Let ${M_1,dots,M_s}$ be a basic set of simple left $A$-modules, and let
      $
        (M_i)^E tilde.equiv product_(j=1)^(r_i) N_(i j), quad
        N_(i j)="simple left" A^E "-module".
      $
      Then every simple $A^E$-module is isomorphic to some $N_(i j)$. Further,
      $N_(i j) tilde.equiv N_(i' j')$ implies that $i=i'$, that is, there is no
      overlap between the sets of simple $A^E$-modules which come from different
      simple $A$-modules.],
  )
] <th:separable-extension-radical-simples>

#proof[
  We may write $A slash (rad A) tilde.equiv product M$, with $M$ ranging over a
  collection of simple left $(A slash (rad A))$-modules, viewed as simple
  $A$-modules. Each $M_i$ occurs at least once in this decomposition. Therefore
  $ (A slash (rad A))^E tilde.equiv product M^E, $
  #source(169)
  and $product M^E$ is a semisimple $A^E$-module by virtue of the hypotheses.
  Since $rad(A^E)$ annihilates every semisimple $A^E$-module, it follows that
  $rad(A^E)$ annihilates $(A slash (rad A))^E$, that is,
  $ rad(A^E) dot {A^E slash (rad A)^E}=0. $
  This gives $rad(A^E) subset.eq (rad A)^E$; the reverse inclusion is clear, so
  (i) is established. Further, we have
  $ A^E slash rad(A^E) tilde.equiv product M^E, $
  which shows that _every_ simple $A^E$-module is a direct summand of some
  $(M_i)^E$. Finally, for $i != j$ we have (by
  Exercise~@exc:hom-field-extension)
  $
    Hom_(A^E) lr(((M_i)^E,(M_j)^E))
    tilde.equiv E times.o_K Hom_A lr((M_i,M_j))=0,
  $
  so $M_i^E$, $M_j^E$ have no common summand.
]

#theorem[
  Let $K$ be an arbitrary field, and $G$ a finite group. Then
  $K G slash (rad K G)$ is a separable $K$-algebra.
] <th:group-algebra-separable-radical-quotient>

#proof[
  By Maschke's Theorem~@th:maschke, the result holds if either $char K=0$ or
  $char K divides.not |G|$. Thus, we may hereafter assume that $char K=p > 0$;
  it will not matter whether $p divides.not |G|$ or not, in the rest of the
  proof. The prime field $k$ in $K$ is the field $FF_p$ of $p$ elements, and is
  a perfect field. Hence every finite extension field $E$ of $k$ is separable
  over $k$, so $rad E G=(rad k G)^E$ by
  @th:separable-extension-radical-simples(i). Then, by
  @th:separable-extension-radical-simples(i) again,
  $ (k G slash (rad k G))^E=E G slash (rad k G)^E=E G slash (rad E G), $
  and hence $(k G slash (rad k G))^E$ is semisimple for each finite extension
  field $E$ over $k$. Therefore $k G slash (rad k G)$ is a separable
  $k$-algebra, by Lemma~@lem:separable-finite-extensions. But then
  $(k G slash (rad k G))^K$ is semisimple, and hence $rad K G=(rad k G)^K$.
  Finally, if $F$ is any extension field of $K$, then
  $
    (K G slash (rad K G))^F & tilde.equiv F G slash (rad K G)^F \
                            & tilde.equiv F G slash ((rad k G)^K)^F
                              tilde.equiv (k G slash (rad k G))^F,
  $
  and the last is semisimple. This completes the proof that
  $K G slash (rad K G)$ is a separable $K$-algebra. Notice that the proof
  depends only on the fact that a group algebra $K G$ has a distinguished basis
  consisting of the elements of $G$, so that $K G$ is obtained from $k G$ by
  extension of the base field from $k$ to $K$, where $k=FF_p$.
]

#source(170)
The above discussion allows us to prove a stronger version of
@th:separable-extension-radical-simples(ii) for a field $K$ of nonzero
characteristic, as follows:

#corollary[
  Let $char K=p > 0$, let $E$ be any extension field of $K$, and let $G$ be a
  finite group. Then for each simple left $K G$-module $V$, the module $V^E$ is
  a direct sum of simple $E G$-modules, no two of which are isomorphic.
] <cor:group-algebra-multiplicity-free-extension>

#proof[
  Let $k$ be the prime field $FF_p$ of $K$, so
  $ K G slash (rad K G) tilde.equiv (k G slash (rad k G))^K $
  by the preceding proof. Now we may write
  $ k G slash (rad k G) tilde.equiv product_(i=1)^s M_(n_i) lr((k_i)), $
  where each $k_i$ is a division algebra over $k$. Then each $k_i$ is a finite
  skewfield, so by Wedderburn's Theorem (see @bib:CurtisReiner1962[CR (68.9)]),
  each $k_i$ is a _field_, and is finite and separable over $k$. Therefore by
  @cor:separable-extension-semisimplicity(i), $K times.o_k k_i$ is a direct sum
  of fields, so
  $
    K G slash (rad K G) tilde.equiv product M_(n_i) lr((K times.o_k k_i))
    tilde.equiv product M_(n_j) lr((K_j)),
  $
  with each $K_j$ a separable field extension of $K$, by
  Exercise~@exc:separable-field-base-extension(i).

  Now let $V$ be a simple left $K G$-module; then $V$ is a simple
  $(K G slash (rad K G))$-module, and can therefore be viewed as a simple module
  relative to one of the Wedderburn components of $K G slash (rad K G)$.
  Denoting this component by $M_n lr((F))$, where $F$ is some finite separable
  extension of $K$, we then have
  $ M_n lr((F)) tilde.equiv V^((n)) quad (n "copies of" V) $
  as $K G$-modules. Therefore, if $E$ is any extension field of $K$, we obtain
  $
    E times.o_K M_n lr((F)) tilde.equiv M_n lr((E times.o_K F))
    tilde.equiv (V^E)^((n)),
  $
  where $V^E=E times.o_K V$. But $E times.o_K F$ is a direct sum of fields
  $product E_i$ (say), so
  $ M_n lr((E times.o_K F)) tilde.equiv product_i M_n lr((E_i)). $
  If $W_i$ denotes a simple left $M_n lr((E_i))$-module, then
  $M_n lr((E_i)) tilde.equiv W_i^((n))$, and we obtain
  $ product_i W_i^((n)) tilde.equiv (V^E)^((n)). $
  Therefore $V^E tilde.equiv product_i W_i$ by the Jordan-Hölder
  Theorem~@th:module-jordan-holder. Since the ${W_i}$ are
  #source(171)
  simple modules belonging to different Wedderburn components of
  $E G slash (rad E G)$, it follows that these ${W_i}$ are non-isomorphic simple
  $E G$-modules. This shows that $V^E$ is a direct sum of non-isomorphic simple
  $E G$-modules, as required.
]

=== Splitting Fields <ss:splitting-fields>

#definition[
  Let $A$ be a finite dimensional algebra over a field $K$, and let $E$ be an
  extension field of $K$ (possibly of infinite dimension over $K$). Put
  $A^E=E times.o_K A$. We call $E$ a _splitting field_#idx("splitting field")
  for $A$ over $K$, and write $E$ _splits_ $A slash K$, if every simple left
  $A^E$-module is absolutely simple.
] <def:splitting-field>

#remarks(numbered: false)[
  #enum(
    numbering: "(i)",
    [The simple left $A$-modules coincide with the simple left
      $(A slash (rad A))$-modules, by §@sec:radicals.],
    [For a $K$-algebra $A$, every algebraically closed field containing $K$
      splits $A slash K$, by @prop:algebraically-closed-simple-centralizer and
      @th:absolute-simplicity-centralizer.],
    [An extension field $E$ of $K$ is a splitting field for $A$ over $K$ if and
      only if $A^E slash rad(A^E)$ is a split semisimple $E$-algebra (see
      §@ss:semisimple-algebras-fields).],
    [If $E$ is a splitting field for $A slash K$, then so is every extension
      field $F$ containing $E$.],
  )
]

#proposition[
  Every f.d. $K$-algebra $A$ has a splitting field $E$ over $K$ such that
  $dim_K E$ is finite.
] <prop:finite-splitting-field>

#proof[
  Let $Omega$ be an algebraic closure of $K$. By
  §@ss:semisimple-algebras-fields, we know that $A^Omega slash rad(A^Omega)$ is
  a split semisimple $Omega$-algebra. Let
  $phi:A^Omega -> A^Omega slash rad(A^Omega)$ be the natural surjection. Choose
  an $Omega$-basis ${b_1,dots,b_n}$ of $A^Omega$ such that
  $
    rad A^Omega=op("⨁", limits: #true)_(i=1)^r Omega b_i
    quad ("where" 0 <= r < n),
  $
  and such that the elements ${phi(b_j):r+1 <= j <= n}$ are an $Omega$-basis of
  $A^Omega slash rad(A^Omega)$, consisting of matrix units in the various
  Wedderburn components of $A^Omega slash rad(A^Omega)$. Let
  $ b_i b_j=sum_k beta_(i j k)b_k, quad beta_(i j k) in Omega. $

  Next, we know that any $K$-basis ${a_1,dots,a_n}$ of $A$ gives rise to an
  $Omega$-basis ${1 times.o a_1,dots,1 times.o a_n}$ of $A^Omega$; note also
  that $dim_K A=dim_Omega A^Omega=n$. We may therefore write
  $ b_i=sum_j alpha_(i j)(1 times.o a_j), quad alpha_(i j) in Omega. $
  #source(172)
  Now let $E=K({beta_(i j k)},{alpha_(i j)})$, a finite extension field of $K$.
  Viewing $A^E$ as $E$-subspace of $A^Omega$, it follows that each $b_i$ lies in
  $A^E$, and so $A^E=op("⨁", limits: #true)_(i=1)^n E b_i$. Since the
  ${beta_(i j k)}$ lie in $E$, $A^E$ is indeed an $E$-algebra. Put
  $N=op("⨁", limits: #true)_(i=1)^r E b_i$, a nilpotent two-sided ideal of
  $A^E$, so $N subset.eq rad(A^E)$. On the other hand, $A^E slash N$ is a split
  semisimple $E$-algebra. Therefore $N=rad(A^E)$, and so $A^E slash rad(A^E)$ is
  a split semisimple $E$-algebra. Hence $E$ is a splitting field for $A$ over
  $K$, as claimed.
]

_Caution._ In the above proof, we have _not_ shown that
$(A slash (rad A))^E tilde.equiv A^E slash rad(A^E)$, nor that
$E times.o_K rad A=rad(A^E)$. We can assert only that
$E times.o rad A subset.eq rad A^E$; see @th:separable-extension-radical-simples
in this connection.

#corollary[
  Let $A$ be a f.d. algebra over a perfect field $K$. There exists a splitting
  field $F$ of $A$ over $K$ such that $F$ is a finite Galois extension of $K$.
  Furthermore,
  $ F times.o_K (A slash (rad A)) tilde.equiv A^F slash rad(A^F), $
  and $A^F slash rad(A^F)$ is a split semisimple $F$-algebra.
] <cor:perfect-field-galois-splitting-field>

#proof[
  By @prop:finite-splitting-field, there exists a finite extension $E$ of $K$
  which splits $A slash K$. Let $F$ be a finite normal extension of $K$
  containing $E$. Then $F$ is separable over $K$ (since $K$ is perfect), and so
  $F$ is a finite Galois extension of $K$. Since $F supset.eq E$, the remarks
  following @def:splitting-field show that $F$ splits $A$ over $K$. The
  remaining assertion is clear from @th:separable-extension-radical-simples.
]

#proposition[
  Let $A$ be a f.d. $K$-algebra, and let $E$ be any extension field of $K$. The
  following statements are equivalent:
  #enum(
    numbering: "(i)",
    [$E$ is a splitting field for $A$ over $K$.],
    [For each simple $A^E$-module $M$, $End_(A^E) lr((M))=E dot 1_M$.],
    [There exists a finite separable extension field $F$ of $E$ such that $F$
      splits $A slash K$, and such that every simple $A^F$-module $N$ is of the
      form $M^F$ $(=F times.o_E M)$ for some simple $A^E$-module $M$.],
  )
] <prop:splitting-field-criteria>

#proof[
  Assertions (i) and (ii) are equivalent by @th:absolute-simplicity-centralizer
  and the definition of a splitting field. Clearly (i) implies (iii), by
  choosing $F=E$. Finally, assume that (iii) holds. Let ${M_i}$ be a basic set
  of simple $A^E$-modules. By @th:separable-extension-radical-simples, the
  direct summands of the $A^F$-modules ${M_i^F}$ include a basic set of simple
  $A^F$-modules. Since we are assuming (iii), it follows that each $M_i^F$ is a
  simple $A^F$-module. Now
  $
    F times.o_E End_(A^E) lr((M_i)) tilde.equiv
    End_(A^F) lr((M_i^F)) tilde.equiv F dot 1_(M_i),
  $
  #source(173)
  the first by @eq:hom-localization, the second since $M_i^F$ is an absolutely
  simple $A^F$-module. Thus $End_(A^E) lr((M_i))$ has dimension $1$ over $E$,
  hence coincides with $E dot 1_(M_i)$, which implies that $M_i$ is absolutely
  simple. Therefore $E$ is a splitting field for $A$ over $K$, as desired, and
  the Proposition is established.
]

#remarks(numbered: false)[
  Parts (ii) and (iii) provide useful tests for splitting fields. For example,
  in @bib:CurtisReiner1962[CR §~27], it is shown that
  $End_(QQ S_n) lr((M))=QQ dot 1_M$ for each simple $QQ S_n$-module $M$;
  Proposition~@prop:splitting-field-criteria(ii) then implies that the rational
  field $QQ$ is a splitting field for the symmetric group $S_n$.

  Part (iii) is often used in the theory of group representations as follows.
  Suppose an algebraic number field $F$ has been found which is a splitting
  field for a group algebra of a finite group $QQ G$. Let
  ${bold(T)_1,dots,bold(T)_s}$ be a basic set of irreducible matrix
  representations $bold(T)_i:G -> G L_(n_i) lr((F))$. Suppose that for suitably
  chosen bases in the $F G$-modules affording ${bold(T)_1,dots,bold(T)_s}$, all
  of the entries of the matrices ${bold(T)_i lr((x)),x in G,1 <= i <= s}$ belong
  to a field $E$, with $QQ subset.eq E subset.eq F$. Then (iii) of
  Proposition~@prop:splitting-field-criteria implies that $E$ is a splitting
  field for $QQ G$. In this situation, we say that the $F$-representations
  ${bold(T)_i}$ are _realized_ in the field $E$.
]

We conclude this section with an important result on the behavior of a simple
$A$-module $U$, upon extension of the base field to a finite Galois extension
which is a splitting field for $A$ (as in
Corollary~@cor:perfect-field-galois-splitting-field). Let $A$ be a $K$-algebra
with $K$-basis ${a_1,dots,a_n}$, and $E$ a finite Galois extension field of $K$.
Then we have structure equations
$ a_i a_j=sum alpha_(i j k)a_k, "with" alpha_(i j k) in K, $
and these also become the structure equations for the algebra $A^E$, relative to
the $E$-basis ${1 times.o a_i}_(1 <= i <= n)$:
$ (1 times.o a_i)(1 times.o a_j)=sum alpha_(i j k)(1 times.o a_k). $
Now let $sigma$ be an element of the Galois group $G_(E slash K)$, and define a
map $sigma times.o 1:A^E -> A^E$ by
$
  (sigma times.o 1) lr((sum_(i=1)^n xi_i times.o a_i))
  =sum_(i=1)^n sigma(xi_i) times.o a_i, xi_i in E,a_i in A.
$
Then $sigma times.o 1$ is an automorphism of the _ring_ $A^E$, but is not an
$E$-automorphism of the $E$-algebra $A^E$. Indeed, we have instead
$
  (sigma times.o 1)(xi y)=sigma(xi)(sigma times.o 1)y
  "for" xi in E,y in A^E.
$
Now $K$ is the subfield of $E$ fixed by $G_(E slash K)$, that is
$ K={xi in E:sigma(xi)=xi "for all" sigma in G_(E slash K)}. $

#source(174)
It follows readily that for $y in A^E$,
$ (sigma times.o 1)y=y "for all" sigma in G_(E slash K) <=> y in A. $
Let $bold(T)$ be a matrix representation of $A^E$ by matrices over $E$, so
$ bold(T):A^E -> M_n lr((E)) $
is a homomorphism of $E$-algebras. For each $sigma in G_(E slash K)$, let
$attach(bold(T), tl: sigma)$ be the map defined by composition of $K$-algebra
homomorphisms
#galois-conjugate-representation-diagram
where the last map $sigma$ is given by the action of $sigma$ on the entries of
the matrices over $E$. Thus
$ attach(bold(T), tl: sigma)=sigma bold(T)(sigma^(-1) times.o 1). $
<eq:galois-conjugate-representation>
Then $attach(bold(T), tl: sigma)$ is also a homomorphism of $E$-algebras, since
for $xi in E$, $a in A$, we have
$
  attach(bold(T), tl: sigma)(xi times.o a)
  &=sigma bold(T)(sigma^(-1)xi times.o a)
  =sigma{sigma^(-1)xi bold(T)(1 times.o a)} \
  &=xi sigma bold(T)(1 times.o a)
  =xi dot attach(bold(T), tl: sigma)(1 times.o a).
$
We say that the representation $attach(bold(T), tl: sigma)$ is _conjugate_ to
$bold(T)$. Clearly
$
  attach(attach(bold(T), tl: sigma), tl: tau)
  =attach(bold(T), tl: tau sigma), quad sigma,tau in G_(E slash K).
$
Furthermore, if $M$ is a left $A^E$-module affording the matrix representation
$bold(T)$ relative to some $E$-basis of $M$, then change of $E$-basis replaces
$bold(T)$ by $bold(P) bold(T) bold(P)^(-1)$ for some invertible matrix
$bold(P)$, where
$
  (bold(P) bold(T) bold(P)^(-1))(y)
  =bold(P) bold(T)(y)bold(P)^(-1),y in A^E.
$
Then $attach(bold(T), tl: sigma)$ is replaced by
$attach((bold(P) bold(T) bold(P)^(-1)), tl: sigma)$, and we have for $xi in E$,
$a in A$:
$
  attach((bold(P) bold(T) bold(P)^(-1)), tl: sigma)(xi times.o a)
  &=sigma{(bold(P) bold(T) bold(P)^(-1))(sigma^(-1)xi times.o a)} \
  &=sigma{bold(P) bold(T)(sigma^(-1)xi times.o a)bold(P)^(-1)} \
  &=sigma(bold(P)) dot attach(bold(T), tl: sigma)(xi times.o a)
  dot sigma(bold(P))^(-1).
$
Hence, change of basis in $M$ has the effect of replacing
$attach(bold(T), tl: sigma)$ by an equivalent matrix representation of $A^E$
over $E$. There is thus a left $A^E$-module, unique up to isomorphism, which
affords the conjugate representation $attach(bold(T), tl: sigma)$; we denote
this module by $attach(M, tl: sigma)$#idx("conjugate module").

#source(175)
#remarks(numbered: false)[
  #enum(
    numbering: "(i)",
    [The conjugacy operation permutes the simple modules.],
    [Let $A=K G$ for a finite group $G$, and let $E$, $G_(E slash K)$ be as
      above. If $bold(T):G -> G L_n lr((E))$ is an $E$-representation of $G$,
      then for $sigma in G_(E slash K)$, the conjugate
      $attach(bold(T), tl: sigma)$ is simply the $E$-representation of $G$
      obtained by applying $sigma$ to the entries of the matrices $bold(T)(x)$,
      $x in G$.],
  )
]

#lemma[
  Let $A^E$ be a semisimple $E$-algebra, and $M$ a simple left $A^E$-module. Let
  $e_M$ be a central primitive idempotent in $A^E$ which acts as identity
  operator on $M$. Then for $sigma in G_(E slash K)$, $(sigma times.o 1)e_M$ is
  a central primitive idempotent which acts as the identity on the conjugate
  simple $A^E$-module $attach(M, tl: sigma)$.
] <lem:conjugate-central-primitive-idempotent>

#proof[
  Let $M$ afford the representation $bold(T)$, and $attach(M, tl: sigma)$ afford
  $attach(bold(T), tl: sigma)$. From @eq:galois-conjugate-representation we have
  $
    attach(bold(T), tl: sigma)((sigma times.o 1)e_M)
    =sigma bold(T)((sigma^(-1) times.o 1)(sigma times.o 1)e_M)
    =sigma bold(T)(e_M)="identity matrix".
  $
  Since $e_M$ is a central primitive idempotent, so is $(sigma times.o 1)e_M$
  because $sigma times.o 1$ is a ring automorphism of $A^E$. This completes the
  proof.
]

#proposition[
  Let $U$ be a simple left $A$-module, and let $E$ be a finite Galois extension
  of $K$. Then $U^E$ is a semisimple $A^E$-module, and is a direct sum of
  conjugates of one simple $A^E$-module $M$. Moreover, all conjugates of $M$,
  under the action of Galois group $G_(E slash K)$, appear in $U^E$ with the
  same multiplicity.
] <prop:galois-orbit-simple-module-extension>

#proof[
  Let $e$ be a central primitive idempotent in $A slash (rad A)$, which acts as
  the identity on $U$. From @th:separable-extension-radical-simples, $U^E$ is a
  semisimple $A^E$-module, and by @th:separable-extension-radical-simples,
  $(A slash (rad A))^E tilde.equiv A^E slash rad(A^E)$. The idempotent $e$,
  viewed as an element in the semisimple $E$-algebra
  $A^E slash rad(A^E) tilde.equiv (A slash (rad A))^E$, is a sum of central
  primitive idempotents. Because $e$ is fixed by the automorphisms
  $sigma times.o 1$ for $sigma in G_(E slash K)$, it follows that the summands
  of $e$ are permuted by the automorphisms ${sigma times.o 1}$. We prove next
  that if $e=e_1+dots+e_m$, with ${e_i}$ central primitive idempotents in
  $(A slash (rad A))^E$, then $G_(E slash K)$ permutes the $e_i$ transitively.
  Otherwise, if there are several orbits relative to $G_(E slash K)$, we would
  have
  $ e=e'+e''+dots $
  where $e'$ is the sum of the idempotents in one orbit, $e''$ the sum of those
  in the next, etc. Then $e'$ is fixed by all automorphisms
  ${sigma times.o 1:sigma in G_(E slash K)}$, and hence belongs to
  $A slash (rad A)$. Similarly $e'' in A slash (rad A)$, etc., which contradicts
  the assumption that $e$ is primitive in the center of $A slash (rad A)$.

  Thus we have $e=e_1+dots+e_m$, where each $e_i=(sigma_i times.o 1)e_1$ for
  some $sigma_i in G_(E slash K)$. Let $e_1$ act as the identity operator on the
  simple $A^E$-module $M$. Then by @lem:conjugate-central-primitive-idempotent,
  for each $i$, $e_i$ acts as the identity operator on $attach(M, tl: sigma_i)$.
  Moreover, it follows from the characteristic property of central primitive
  idempotents (see
  #source(176)
  Exercise~@exc:central-primitive-idempotents) that each simple component of
  $U^E$ is associated with one of the idempotents ${e_i}$, and hence is a
  conjugate of $M$. Therefore
  $ U^E tilde.equiv plus.o (attach(M, tl: sigma_i))^((m_i)), $
  where $(attach(M, tl: sigma_i))^((m_i))$ is the external direct sum of $m_i$
  copies of $attach(M, tl: sigma_i)$. Finally, the automorphisms
  ${sigma times.o 1:sigma in G_(E slash K)}$ permute the summands of $U^E$
  transitively, and leave $U^E$ fixed (up to $A^E$-isomorphism). It follows from
  the K-S-A Theorem (§@sec:idempotents-krull-schmidt-projective-covers) that the
  multiplicities ${m_i}$ are all equal, and the theorem is proved.
]

#corollary[
  Let $A$ be a $K$-algebra, and $E$ a finite Galois extension of $K$ which is a
  splitting field for $A$. Let ${M_1,dots,M_r}$ be a basic set of absolutely
  simple $A^E$-modules. Then the Galois group $G_(E slash K)$ permutes the
  simple modules ${M_1,dots,M_r}$. The simple $A$-modules are in bijective
  correspondence with the $G_(E slash K)$-orbits in the set ${M_1,dots,M_r}$,
  and the simple $A$-module $U$ corresponding to an orbit $cal(O)$ satisfies
  $
    U^E tilde.equiv
    lr((op("⨁", limits: #true)_(i in cal(O)) M_i))^((m))
  $
  for some positive integer $m$.
] <cor:galois-orbits-simple-modules>

=== Splitting Fields for Division Algebras <ss:splitting-division-algebras>

The general results on splitting fields in §@ss:splitting-fields leave open the
question of how splitting fields are constructed. This gap is filled, to some
extent, by the main results of this section, which show that maximal subfields
of division algebras are splitting fields. _The assumptions stated at the
beginning of §@sec:separable-algebras-splitting-fields about finite
dimensionality of algebras and vector spaces remain in force._

#proposition[
  Let $D$ be a division algebra with center $K$, $M$ a left vector space over
  $D$, $A=End_D lr((M))$, and let $E$ be a maximal subfield of $D$. Then there
  is an isomorphism of $E$-algebras
  $ A^E tilde.equiv End_E lr((M)). $
] <prop:maximal-subfield-splits-endomorphism-algebra>

#proof[
  From Exercises~@exc:left-division-space-endomorphisms and
  @exc:matrix-ring-structure, we know that $A$ is a simple algebra with center
  $K$. By @cor:central-simple-field-extension, $A^E$ is a central simple
  $E$-algebra. Moreover, $A^E$ acts on $M$ according to the rule
  $(a times.o e)m=a(e m)$, $a in A$, $e in E$, $m in M$. Because $A^E$ is
  simple, there is an isomorphism of $E$-algebras from $A^E$ to the algebra of
  left multiplications $(A^E)_l$ on $M$ by elements of $A^E$. By
  Exercise~@exc:left-division-space-endomorphisms, $M$ is a simple left
  $A$-module, and hence a simple left $A^E$-module. Let
  $delta in End_(A^E) lr((M))$; then $delta in End_A lr((M))$, and hence
  $delta=d dot 1_M$ for some element $d in D$. The fact that $delta$ also
  commutes with the elements of $E dot 1_M$ implies that $d$ commutes with the
  #source(177)
  elements of $E$, and hence $E(d)$ is a subfield of $D$ containing $E$. Since
  $E$ is a maximal subfield of $D$, we have $delta in E dot 1_M$, and hence
  $End_(A^E) lr((M))=E dot 1_M$. Applying the Density Theorem~@th:density, and
  using the finite dimensionality of $M$ over $E$ as in
  @th:simple-artinian-structure, we have $(A^E)_l tilde.equiv End_E lr((M))$.
  Therefore $A^E tilde.equiv End_E lr((M))$ as required, because of the
  isomorphism $A^E tilde.equiv (A^E)_l$.
]

#corollary[
  Let $A$ be a central simple $K$-algebra, $M$ a simple left $A$-module,
  $D=End_A lr((M))$, and $E$ a maximal subfield of $D$. Then $E$ is a splitting
  field for $A$.
] <cor:maximal-centralizer-subfield-splits>

The proof is immediate from @prop:maximal-subfield-splits-endomorphism-algebra,
using Lemma~@lem:separable-split-extension and the fact that $End_E lr((M))$ is
a split semisimple $E$-algebra.

#corollary[
  Let $D$ be a division algebra with center $K$, and let $E$ be a maximal
  subfield of $D$. Then $E$ is a splitting field for $D$, and we have
  $ dim_E D=dim_K E, quad dim_K D=(dim_K E)^2. $
] <cor:maximal-subfield-degree>
#idx("splitting field", target: [@cor:maximal-subfield-degree])

#proof[
  The first statement follows from
  @prop:maximal-subfield-splits-endomorphism-algebra, with $M$ the left regular
  module $attach(D, bl: D)$; for then
  $End_D lr((M)) tilde.equiv D^circle.small$, and $E$ is a maximal subfield of
  $End_D lr((M))$. To prove the second statement, we observe that
  $ D^E tilde.equiv End_E lr((D)) $
  in the present situation. Therefore
  $ dim_K D=dim_E lr((D^E))=(dim_E D)^2. $
  But
  $ dim_K D=dim_E D dot dim_K E, $
  so comparing this with the preceding equation, we find that $dim_K E=dim_E D$.
  This completes the proof of the corollary.
]

Our next objective is to show that every division algebra $D$ with center $K$
contains a maximal subfield $E$ of $D$ such that $E$ is separable over $K$. (By
@cor:maximal-subfield-degree, this field $E$ will be a splitting field for $D$
over $K$.) The result is clear if $char K=0$, so suppose now that
$char K=p != 0$. Our proof of the lemma below follows the treatment in
Bourbaki~@bib:Bourbaki1958, §10, No.~4; for another proof, see
@bib:Reiner1975[MO §7b].

#lemma[
  Let $char K=p != 0$, and let $D$ be a division algebra with center $K$, where
  $D != K$. Then there exists a field $E$ such that $K subset E subset D$, with
  $E$ separable over $K$.
] <lem:noncentral-separable-subfield>

#source(178)
#proof[
  Recall that an element $delta in D$ is _purely inseparable_#idx(
    "purely inseparable",
  ) over $K$ if $"min. pol."_K lr((delta))=X^(p^e)-alpha$ for some $e >= 0$ and
  some $alpha in K$. Let us write $D-K={delta:delta in D,delta in.not K}$. If
  there exists an element $delta in D-K$ such that $delta$ is _not_ purely
  inseparable over $K$, then
  $ "min. pol."_K lr((delta))=f(X^(p^e)) $
  for some $e >= 0$ and some irreducible polynomial $f(X) in K[X]$ of degree
  $> 1$. Setting $gamma=delta^(p^e)$, it follows that $gamma in D-K$ and $gamma$
  is separable over $K$. Then $K(gamma)$ is a separable extension of $K$, and
  $K subset K(gamma) subset D$, as desired.

  We are thus left with the case where every element of $D-K$ is purely
  inseparable over $K$. Then there exists an element $delta in D-K$ such that
  $ "min. pol."_K lr((delta))=X^(p^(a+1))-alpha, $
  where $a >= 0$ and $alpha in K$. Setting $xi=delta^(p^a)$, we have $xi in D-K$
  and $xi^p in K$. Let $sigma$ be the automorphism of the $K$-space $D$ given by
  $sigma(x)=xi x xi^(-1)$, $x in D$. Then $sigma != 1$ since
  $xi in.not "center of" D$; on the other hand, $(sigma-1)^p=sigma^p-1=0$. Hence
  there exists a positive integer $r$ such that
  $ (sigma-1)^r != 0, quad (sigma-1)^(r+1)=0. $
  Choose $x in D$ such that $(sigma-1)^r x != 0$, and set
  $ y=(sigma-1)^(r-1)x, quad z=(sigma-1)y=(sigma-1)^r x. $
  Then $(sigma-1)z=0$, so $sigma z=z != 0$. Now put $gamma=z^(-1)y$; then
  $ sigma(gamma)=z^(-1)sigma(y)=z^(-1)(z+y)=1+gamma != gamma. $
  Thus $sigma(gamma) != gamma$, so $sigma$ is a $K$-automorphism of the field
  $K(gamma)$, and $sigma != 1$ on $K(gamma)$. It follows that $K(gamma)$
  contains a separable extension field $E$ of $K$ with $E != K$, which completes
  the proof of the lemma.
]

#proposition[
  Every division algebra $D$ with center $K$ contains a maximal subfield $E$
  which is separable over $K$.
] <prop:separable-maximal-subfield>

#proof[
  We may assume that $D != K$, and that $char K=p != 0$. We prove the result by
  induction on $dim_K D$. In Lemma~@lem:noncentral-separable-subfield we proved
  the existence of a separable field extension $E$ of $K$, with
  $K subset E subset D$. Let us set
  $ D'={x in D:x y=y x "for all" y in E}, $
  the centralizer of $E$ in $D$. Then $E subset.eq D' subset.eq D$, and $D'$ is
  also a division algebra; the inclusion $D' subset.eq D$ is proper, since
  otherwise $E$ lies in the center $K$ of $D$. By the induction hypothesis,
  there exists a maximal subfield $F$ of $D'$ such that $F$
  #source(179)
  is separable over $E$. Since separability is transitive, it follows that $F$
  is separable over $K$. It remains for us to verify that $F$ is a maximal
  subfield of $D$. If this is false, then $F$ is centralized by some element
  $delta in D-F$. Then $delta$ centralizes $E$, whence $delta in D'$, so
  $F(delta)$ is a subfield of $D'$ properly containing $F$. This contradicts our
  assumption that $F$ is a maximal subfield of $D'$. Hence $F$ is a maximal
  subfield of $D$ and $F$ is separable over $K$, which completes the induction
  argument and proves the proposition.
]

We may use the preceding result to strengthen our earlier theorems about
splitting fields for separable algebras. If $A$ is a separable $K$-algebra, then
by @lem:separable-split-extension there exists a splitting field $E$ for $A$
over $K$, that is, a field $E$ such that $E times.o_K A$ is a direct sum of full
matrix algebras over $E$. Our aim is to establish the following improvement:

#proposition[
  Let $A$ be a separable $K$-algebra. Then there exists a field $E$ which is a
  finite separable extension of $K$, such that $E$ is a splitting field for $A$
  over $K$.
] <prop:finite-separable-splitting-field>

#proof[
  Let $A=A_1 plus.o dots.c plus.o A_s$ be the Wedderburn decomposition of $A$
  into simple components $A_i$. Keep $i$ fixed for the moment, where
  $1 <= i <= s$. Let $K_i$ be the center of $A_i$, so $K_i$ is a finite
  separable extension of $K$ by @cor:separable-algebra-wedderburn-centers. We
  may choose a finite separable extension $E_i$ of $K_i$ which splits $A_i$ over
  $K_i$, so
  $ E_i times.o_(K_i) A_i tilde.equiv M_(n_i) lr((E_i)), $
  where $n_i^2=dim_(K_i) A_i$. We shall choose the desired field $E$ to be a
  finite normal extension of $K$ containing all the fields ${E_i:1 <= i <= s}$.

  For each $i$, $1 <= i <= s$, we may write
  $K_i tilde.equiv K[x] slash (f_i lr((x)))$, where $f_i lr((x))$ is an
  irreducible separable polynomial over $K$. Let $E'_i$ be a splitting field for
  $f_i lr((x))$ over $K$, so $E'_i$ is a finite separable extension of $K$ which
  contains all the zeros of $f_i lr((x))$. By
  Exercise~@exc:composite-field-extension, we can find a composite of the fields
  $E_1,dots,E_s,E'_1,dots,E'_s$ over $K$; let $E$ be its normal closure over
  $K$. This field $E$ is a finite separable extension of $K$ which contains the
  fields ${E_i}$ and ${E'_i}$ (or, more precisely, contains $K$-isomorphic
  copies of them.) Therefore
  $
    E times.o_K K_i tilde.equiv E[x] slash (f_i lr((x))) tilde.equiv product E,
  $
  with the number of summands on the right equal to $deg f_i lr((x))$. We now
  have
  $ E times.o_K A=op("⨁", limits: #true)_(i=1)^s E times.o_K A_i, $
  and
  $
    E times.o_K A_i tilde.equiv (E times.o_K K_i) times.o_(K_i) A_i
    tilde.equiv product E times.o_(K_i) A_i.
  $
  #source(180)
  Here the factors $E$ have the $K_i$-algebra structures given by all embeddings
  $K_i -> E$. Each embedding extends to $E_i -> E$, since $E$ is normal over
  $K$, so the following calculation applies to every factor. But
  $
    E times.o_(K_i) A_i
    tilde.equiv E times.o_(E_i) (E_i times.o_(K_i) A_i)
    tilde.equiv E times.o_(E_i) M_(n_i) lr((E_i))
    tilde.equiv M_(n_i) lr((E)).
  $
  This gives the desired result, and in fact we have shown that with this choice
  of $E$, we have
  $ E times.o_K A tilde.equiv product_(i=1)^s lr((product M_(n_i) lr((E)))), $
  where for each $i$, $1 <= i <= s$, the number of summands $M_(n_i) lr((E))$ is
  equal to $dim_K K_i$, and where $n_i^2=dim_(K_i) A_i$.
]

=== Reduced Norms <ss:reduced-norms>

Let $A$ be a $K$-algebra, and let $a in A$. As in
@eq:characteristic-minimal-polynomial, let $"char. pol."_(A slash K) lr((a))$ be
the characteristic polynomial of the $K$-linear map $x -> a x$, $x in A$. The
_trace map_#idx("trace map") $T_(A slash K)$ and _norm map_#idx("norm")
$N_(A slash K)$ are then defined by
$
  "char. pol."_(A slash K) a=X^m-(T_(A slash K) a)X^(m-1)
  +dots+(-1)^m N_(A slash K) a,
$
<eq:algebra-characteristic-trace-norm>
where $m=dim_K A$.

Suppose for the moment that $A=M_n lr((K))$, so each $bold(a) in A$ is a matrix
over $K$. If $n > 1$, $T_(A slash K) bold(a)$ is _not_ the trace of the matrix
$bold(a)$, nor is $N_(A slash K) bold(a)$ its determinant. Indeed, if $V$ is a
simple left $A$-module, then the matrix $bold(a)$ is the matrix describing the
linear transformation $v -> a v$, $v in V$, relative to a suitable $K$-basis of
$V$. Since $A tilde.equiv V^((n))$, we have at once
$ "char. pol."_(A slash K) bold(a)={"char. pol. of matrix" bold(a)}^n, $
whence
$
  T_(A slash K) bold(a)=n dot "trace of matrix" bold(a), quad
  N_(A slash K) bold(a)=(det bold(a))^n.
$
This suggests that $"char. pol."_(A slash K)$, $T_(A slash K)$ and
$N_(A slash K)$ may not be sufficiently delicate for certain types of
calculations. Instead, it is necessary to use “reduced” versions of them, which
we define below.

We now assume that $A$ is an arbitrary separable $K$-algebra. Let $E$ be a
splitting field for $A$ over $K$, so there is an isomorphism of $E$-algebras
$ h:E times.o_K A tilde.equiv product_(i=1)^s M_(n_i) lr((E)). $
<eq:reduced-norm-splitting-isomorphism>
For each $a in A$, let
$
  h(1 times.o a)=product phi_i lr((a)), "where"
  phi_i lr((a)) in M_(n_i) lr((E)),1 <= i <= s.
$
<eq:reduced-norm-matrix-components>

#source(181)
We now define the _reduced characteristic polynomial_#idx(
  "reduced characteristic polynomial",
) of $a$ by
$
  "red. char. pol."_(A slash K) a
  =product_(i=1)^s "char. pol." phi_i lr((a)), quad forall a in A,
$
<eq:reduced-characteristic-polynomial>
where $"char. pol." phi_i lr((a))$ is the characteristic polynomial of the
matrix $phi_i lr((a)) in M_(n_i) lr((E))$. As shown in @bib:Reiner1975[MO §9]
(see especially @bib:Reiner1975[Exercise~9.3]), this reduced characteristic
polynomial is independent of the choice of $E$ and of the isomorphism $h$ in
@eq:reduced-norm-splitting-isomorphism. Further, its coefficients all lie in the
ground field $K$.

The relation between $"char. pol."_(A slash K) lr((a))$ and
$"red. char. pol."_(A slash K) lr((a))$ may be obtained as follows. Let
$A^E=E times.o_K A$, where $E$ is a splitting field for $A$ over $K$, and let
${V_1,dots,V_s}$ be a basic set of simple left $A^E$-modules. Then for each $i$,
$1 <= i <= s$, $phi_i lr((a))$ is the matrix of the $E$-linear transformation
$v -> (1 times.o a)v$, $v in V_i$, relative to a suitable $E$-basis of $V_i$.
Since
$ A^E tilde.equiv product_(i=1)^s V_i^((n_i)) $
as left $A^E$-modules, we obtain
$
  "char. pol."_(A slash K) a="char. pol."_(A^E slash E) a
  =product_(i=1)^s {"char. pol." phi_i lr((a))}^(n_i)
$ <eq:characteristic-polynomial-reduced-factors>
for all $a in A$. This shows that $"red. char. pol."(a)$ and $"char. pol."(a)$
have the same irreducible factors, apart from multiplicities. We caution the
reader that $"red. char. pol."_(A slash K) lr((a))$ need not coincide with
$"min. pol."_(A slash K) lr((a))$, and is in fact a multiple of it. Further, we
have $dim_E V_i=n_i$ for each $i$, so $"red. char. pol."_(A slash K) lr((a))$
has degree $sum_i n_i$.

Now let us write
$
  "red. char. pol."_(A slash K) a
  =X^m-("tr"_(A slash K) a)X^(m-1)+dots+(-1)^m "nr"_(A slash K) a
$
<eq:reduced-trace-norm-coefficients>
for $a in A$. (Here, $m=sum n_i$.) We call $"tr"_(A slash K)$ the _reduced
trace_#idx(
  "reduced trace",
), and $"nr"_(A slash K)$ the _reduced norm_#idx("reduced norm"). It is easily
verified that $"tr"_(A slash K)$ is a $K$-linear map from $A$ to $K$, and the
following formulas hold true for all $a,b in A$ and all $alpha in K$:
$
  "tr" a b="tr" b a, quad "nr" a b=("nr" a)("nr" b), quad
  "nr" alpha a=alpha^m "nr" a.
$
<eq:reduced-trace-norm-identities>
We note next that reduced characteristic polynomial is unchanged by extension of
the ground field:
$
  "red. char. pol."_(A slash K) lr((a))
  ="red. char. pol."_((L times.o_K A) slash L) lr((1 times.o a))
$
<eq:reduced-characteristic-base-extension>
for all $a in A$ and all fields $L$ containing $K$. This follows easily from the
definition of $"red. char. pol."(a)$, by choosing the splitting field $E$ for
$A$ over $K$ so that $E supset.eq L$.

#source(182)
Let us consider in more detail the special case where $A$ is a simple algebra
whose center $L$ is separable over $K$. Put
$ dim_L A=m^2, quad dim_K L=n. $
As shown in the proof of @prop:finite-separable-splitting-field, we may choose a
field $E$ containing $L$, such that $E$ splits $A$ over $K$, and for such a
field $E$ we have
$ E times.o_K A tilde.equiv product M_m lr((E)) quad (n "summands"). $
From @eq:characteristic-polynomial-reduced-factors we obtain the important
relation
$
  "char. pol."_(A slash K) lr((a))
  ={"red. char. pol."_(A slash K) a}^m, quad forall a in A,
$
<eq:simple-algebra-characteristic-reduced-power>
valid for a simple $K$-algebra $A$ of dimension $m^2$ over its center. This
formula yields
$
  T_(A slash K) a=m dot "tr"_(A slash K) a, quad
  N_(A slash K) a=("nr"_(A slash K) a)^m, quad forall a in A.
$
<eq:simple-algebra-trace-norm-reduced-power>
We note finally (see @bib:Reiner1975[MO (9.14)] for proof)
$
  "tr"_(A slash K) a=T_(L slash K)("tr"_(A slash L) a), quad
  "nr"_(A slash K) a=N_(L slash K)("nr"_(A slash L) a)
$
<eq:reduced-trace-norm-center-transitivity>
for $a in A$. This result will play a vital role in proving Jacobinski's formula
for the conductor of a maximal order into an integral group ring (see
@th:jacobinski-conductor-formula).

We now give a number of examples to illustrate how to compute reduced norms and
traces, especially for group algebras.

#example[
  Let
  $
    A=QQ plus.o QQ i plus.o QQ j plus.o QQ k, quad
    i^2=j^2=-1, quad i j=k=-j i,
  $
  the skewfield of rational quaternions#idx("quaternions"). Then $A$ is a
  central simple $QQ$-algebra, and $E=QQ(i)$ is a maximal subfield of $A$. Each
  $a in A$ is uniquely expressible as $a=alpha+beta j$ with $alpha,beta in E$.
  There is then an $E$-isomorphism
  $
    f:E times.o_QQ A tilde.equiv M_2 lr((E)), "given by"
    f(1 times.o a)=mat(alpha, beta; -overline(beta), overline(alpha)),
  $
  where bars denote complex conjugation. Then
  $
    "red. char. pol."_(A slash QQ) a
    &="char. pol." mat(alpha, beta; -overline(beta), overline(alpha)) \
    &=X^2-(alpha+overline(alpha))X
    +(alpha overline(alpha)+beta overline(beta)),
  $
  #source(183)
  and
  $
    "tr"_(A slash QQ) a=alpha+overline(alpha), quad
    "nr"_(A slash QQ) a=alpha overline(alpha)+beta overline(beta).
  $
  Note that
  $ "char. pol."_(A slash QQ) a={"red. char. pol."_(A slash QQ) a}^2, $
  and
  $
    T_(A slash QQ) a=2 "tr"_(A slash QQ) a, quad
    N_(A slash QQ) a=("nr"_(A slash QQ) a)^2.
  $
] <exm:quaternion-reduced-norm>

#example[
  Let $A=K G$, where $char K=0$ and $G$ is abelian. Then
  $ K G tilde.equiv product_(i=1)^s K_i, $
  with each $K_i$ some cyclotomic extension field of $K$. In this case,
  $ "nr"_(A slash K)=N_(A slash K)=product_(i=1)^s N_(K_i slash K). $
] <exm:abelian-group-algebra-reduced-norm>

#example[
  Let $A=QQ G$, where
  $ G=lr(⟨ x, y: x^n=1, y^2=1, y x y^(-1)=x^(-1) ⟩), $
  the dihedral group#idx("dihedral group")#idx("group", "dihedral") $D_n$ of
  order $2n$. Let $d$ range over the positive divisors of $n$, and let $zeta_d$
  denote a primitive $d$-th root of $1$ over $QQ$. Let $K_d=QQ(zeta_d)$, so
  $dim_QQ K_d=phi(d)$. Let $E_d$ be the maximal real subfield of $K_d$, that is
  $ E_d={alpha in K_d:alpha=overline(alpha)}, $
  where bar denotes the complex conjugation. We have $dim_(E_d) K_d=2$ if
  $d > 2$, while $K_d=E_d=QQ$ if $d=1$ or $2$.

  We may view $K_d$ as a left $A$-module, on which $x$ acts as multiplication by
  $zeta_d$, and $y$ acts as complex conjugation. Note that the action of $A$ on
  $K_d$ is well defined, since (for $d$ dividing $n$)
  $ (zeta_d)^n=1,y^2 alpha=overline(overline(alpha))=alpha, $
  $
    (y x y^(-1))alpha=(y x)overline(alpha)
    =y(zeta_d overline(alpha))=overline(zeta)_d alpha=x^(-1)alpha,
    quad forall alpha in K_d.
  $
  Let us introduce the “twisted group algebra”#idx("twisted group algebra")
  $
    A_d=K_d circle lr(⟨ y ⟩)=K_d plus.o K_d y,
    y^2=1,y alpha=overline(alpha)y, quad alpha in K_d.
  $
  #source(184)
  The preceding discussion shows that $K_d$ is a simple left $A_d$-module, and
  that $K_d$ is a simple left $A$-module by virtue of the surjection
  $ A -> A_d, "defined by" x -> zeta_d,y -> y. $
  The center of $A_d$ is $E_d$ if $d > 2$, while $A_d$ is commutative if $d=1$
  or $2$. For $d=1$ or $2$ we have $A_d tilde.equiv QQ plus.o QQ$. On the other
  hand, for $d > 2$ the semisimple $E_d$-algebra $A_d$ has center $E_d$, and is
  not commutative. But $A_d$ is not a division algebra, since $y^2=1$ and
  $y != 1$. Therefore
  $ A_d tilde.equiv M_2 lr((E_d)),d > 2. $
  Next, we observe that
  $ A tilde.equiv product_(d divides n) A_d, $
  as is clear by comparing dimensions of both sides. Let us denote by $pi_d$ the
  projection map $A -> A_d$. For $a in A$, we have
  $
    "nr"_(A slash QQ) a=product_(d divides n) "nr"_(A_d slash QQ){pi_d lr((a))},
  $
  and it remains for us to compute $"nr"_(A_d slash QQ)$. For $d=1$ or $2$,
  $A_d$ is commutative and $"nr"_(A_d slash QQ)$ is the product of the two
  coordinate maps. Now let $d > 2$, and let us note that
  $ "nr"_(A_d slash QQ)=N_(E_d slash QQ) "nr"_(A_d slash E_d), $
  so we must describe the reduced norm map from $A_d$ to its center $E_d$. Each
  $a in A_d$ is representable by a $2 times 2$ matrix over $E_d$, and
  $"nr"_(A_d slash E_d)$ is the determinant of this matrix. A more convenient
  formulation is as follows: the map
  $
    alpha -> mat(alpha, 0; 0, overline(alpha)), quad
    y -> mat(0, 1; 1, 0), quad alpha in K_d,
  $
  gives an irreducible matrix representation of $A_d$ over the field $K_d$. It
  must come from the unique simple $A_d$-module by ground field extension. Hence
  for $alpha+beta y in A_d$, we have
  $
    "red. char. pol."_(A_d slash E_d) lr((alpha+beta y))
    &="char. pol. of the matrix"
    mat(alpha, beta; overline(beta), overline(alpha)) \
    &=X^2-(alpha+overline(alpha))X
    +(alpha overline(alpha)-beta overline(beta)).
  $
  Therefore
  $
    "nr"_(A_d slash E_d) lr((alpha+beta y))
    =alpha overline(alpha)-beta overline(beta), quad
    "tr"_(A_d slash E_d) lr((alpha+beta y))=alpha+overline(alpha),
  $
  #source(185)
  for all $alpha,beta in K_d$. Further,
  $
    "nr"_(A_d slash QQ) lr((alpha+beta y))
    =N_(E_d slash QQ)(alpha overline(alpha)-beta overline(beta)),
  $
  and a corresponding formula holds for reduced traces. A more general version
  of this calculation is given in
  Exercise~@exc:twisted-galois-matrix-representation.

  The reader should compare these results with those obtained in
  @exm:dihedral-group-characters, noting that
  $ CC G=CC times.o_QQ A tilde.equiv product_(d divides n) CC times.o_QQ A_d. $
  Here, $CC times.o_QQ A_d tilde.equiv CC plus.o CC$ if $d=1$ or $2$. For
  $d > 2$,
  $
    CC times.o_QQ A_d tilde.equiv CC times.o_QQ M_2 lr((E_d))
    tilde.equiv M_2 lr((CC times.o_QQ E_d)).
  $
  But $CC times.o_QQ E_d$ is isomorphic to a direct sum of $phi(d) slash 2$
  copies of $CC$, so
  $
    CC times.o_QQ A_d tilde.equiv
    product_(phi(d) slash 2 "copies") M_2 lr((CC)).
  $
] <exm:dihedral-group-algebra-reduced-norm>

#example[
  Let $A=QQ G$, where
  $ G=Q_m=lr(⟨ x, y: x^(2m)=1, y^2=x^m, y x y^(-1)=x^(-1) ⟩), $
  the generalized quaternion group#idx("generalized quaternion group")#idx(
    "group",
    "generalized quaternion",
  )#idx("quaternion group") of order $4m$. Put
  $ e_1=(1-x^m)/2, quad e_(-1)=(x^m+1)/2. $
  Then $e_1$ and $e_(-1)$ are orthogonal central idempotents in $QQ G$, so
  $ QQ G=QQ G dot e_1 plus.o QQ G dot e_(-1). $
  Since $x^m$ acts as $1$ on $QQ G dot e_(-1)$, we have
  $QQ G dot e_(-1) tilde.equiv QQ D_m$, with $D_m$ dihedral of order $2m$. On
  the other hand,
  $
    QQ G dot e_1 tilde.equiv QQ[x,y] slash
    (x^m+1,y^2-x^m,y x y^(-1)-x^(-1)).
  $
  Thus, in any representation of $QQ G dot e_1$, we must have
  $ x^m -> -1,y^2 -> -1,y x y^(-1)x -> 1. $

  _Case 1._ $m$ even, $m=2^r m_0$, $m_0$ odd, $r >= 1$. We form
  $
    K_d=QQ(zeta_d),E_d=QQ(zeta_d+zeta_d^(-1)),
    d=2^(r+1)d_0,d_0 divides m_0.
  $
  Now consider the quaternion skewfield
  $
    bb(H)_d=E_d plus.o E_d i plus.o E_d j plus.o E_d k
    =E_d times.o_QQ bb(H),
  $
  #source(186)
  with $bb(H)=QQ plus.o QQ i plus.o QQ j plus.o QQ k$. Then
  $K_d=E_d plus.o E_d i$, and we may write
  $
    bb(H)_d=K_d plus.o K_d j,"where" j^2=-1,
    j alpha=overline(alpha)j,quad forall alpha in K_d.
  $
  For each such $d$, we obtain a representation of $QQ G dot e_1$ by means of
  the map
  $ x -> zeta_d,y -> j. $
  (Note that $zeta_d^m=-1$, since we chose $d$ so that $d divides 2m$ but
  $d divides.not m$.) Hence we have
  $ QQ G dot e_1 tilde.equiv product_d bb(H)_d, $
  where $d=2^(r+1)d_0$, $d_0 divides m_0$. (The $QQ$-dimension of the right hand
  expression is
  $
    2sum_d phi(d)=2 dot 2^r sum_(d_0 divides m_0) phi(d_0)
    =2^(r+1)m_0=2m,
  $
  so we have enough simple summands of $QQ G dot e_1$.)

  We note that
  $
    CC G dot e_1 & tilde.equiv product_d CC times.o_QQ (E_d times.o_QQ bb(H))
                   =product_d (CC times.o_QQ E_d) times.o_QQ bb(H) \
                 & tilde.equiv product_d {M_2 lr((CC))}^(phi(d/2)),
  $
  since $CC times.o_QQ E_d$ is a direct sum of $phi(d/2)$ copies of $CC$.

  _Case 2._ $m$ odd. The analysis in this case is slightly different from that
  above. We now set $d=2d_0$, where $d_0 divides m$, and now
  $zeta_d=-zeta_(d_0)$. The representation of $QQ G dot e_1$ corresponding to
  the value $d_0=1$ is given by $x -> -1$, $y -> i$, and is afforded by the
  Wedderburn component $QQ(i)$ of $QQ G dot e_1$. For $d_0 > 1$, let
  $
    E_d=QQ(zeta_d+zeta_d^(-1)),quad K_d=QQ(zeta_d),quad
    bb(H)_d=K_d plus.o K_d j,
  $
  where $j^2=-1$ and $j alpha=overline(alpha)j$ for $alpha in K_d$. Then
  $bb(H)_d$ is a quaternion skewfield with center $E_d$, and is a Wedderburn
  component of $QQ G dot e_1$. Thus we obtain
  $
    QQ G dot e_1 tilde.equiv QQ(i) plus.o
    product_(d_0 divides m, d_0 > 1) bb(H)_d,
  $
  and both sides have dimension $2m$ over $QQ$.#ed-note[
    In Case 2 the printed field $K_d=E_d lr((i))$ must be replaced by
    $QQ(zeta_d)$; the two quadratic extensions need not agree. For example, when
    $m=3$, the quaternion component is $(-3,-1)$ over $QQ$, whereas the printed
    construction gives Hamilton's $(-1,-1)$. The corrected component is the
    cyclic algebra with complex conjugation and parameter $-1$; for this
    construction see Reiner~@bib:Reiner2003, (30.1).
  ]

  In either case, we may compute reduced norms as follows: let
  $alpha+beta j in bb(H)_d$, where $alpha,beta in K_d$. As matrices over $K_d$,
  we have
  $ alpha -> mat(alpha, 0; 0, overline(alpha)),quad j -> mat(0, -1; 1, 0), $
  #source(187)
  therefore
  $
    "nr"_(bb(H)_d slash E_d) lr((alpha+beta j))
    =mat(delim: "|", alpha, -beta; overline(beta), overline(alpha))
    =alpha overline(alpha)+beta overline(beta).
  $
  The fact that $alpha overline(alpha)+beta overline(beta) > 0$ in the real
  field $E_d$, provided not both $alpha$ and $beta$ are $0$, gives another
  verification that $bb(H)_d$ is a skewfield.
] <exm:quaternion-group-algebra-reduced-norm>

The preceding examples show how to evaluate reduced norms in a number of cases.
The last two examples are quite useful, since they exhibit the Wedderburn
decompositions of the rational group algebra $QQ G$ for the cases where $G$ is a
dihedral or generalized quaternion group.

Returning to the general theory, suppose now that $A$ is a simple $K$-algebra of
dimension $m^2$ over its center. If $char K$ divides $m$, it follows from
@eq:simple-algebra-trace-norm-reduced-power that the ordinary trace function
$T_(A slash K)$ is identically zero. As we shall see in
§@ss:frobenius-symmetric-algebras, it is desirable to have at our disposal a
nondegenerate bilinear form from $A$ to $K$. In the “classical” case where $A$
is a semisimple algebra over a field of characteristic $0$, the ordinary trace
form $T_(A slash K)$ provides such a nondegenerate form. As pointed out, this
need not be the case for modular fields $K$, and this is one of the reasons for
using $"tr"_(A slash K)$ instead of $T_(A slash K)$. We state without proof (see
@bib:Reiner1975[MO (9.26)]):

#proposition[
  Let $A$ be a separable $K$-algebra. Then the reduced trace $"tr"_(A slash K)$
  gives a symmetric bilinear associative nondegenerate trace form from
  $A times A$ to $K$, namely,
  $ (a,b) -> "tr"_(A slash K) a b, quad forall a,b in A. $
] <prop:reduced-trace-nondegenerate>

Suppose now that $A=M_n lr((D))$, where $D$ is a skewfield with center $K$, and
let $K^dot=K-{0}$. Then
$ "nr"_(A slash K):G L_n lr((D)) -> K^dot $
gives a multiplicative homomorphism, which we may regard as a “determinant” map
in some sense. Set
$ D^dot=D-{0}, quad D^hash=D^dot slash [D^dot,D^dot]. $
Then $"nr"_(D slash K):D^dot -> K^dot$ is also a homomorphism, and induces a map
$ "nr"_(D slash K):D^hash -> K^dot. $
On the other hand, there is also a homomorphism
$ det:G L_n lr((D)) -> D^hash, $
#source(188)
given by the Dieudonné determinant (see Artin~@bib:Artin1957). We shall review
its properties, and then show that
$ "nr"_(D slash K) det a="nr"_(A slash K) a "for all" a in G L_n lr((D)). $
<eq:reduced-norm-dieudonne-determinant>
By an _elementary matrix_#idx("elementary matrix") $bold(E) in G L_n lr((D))$ we
mean a matrix $bold(E)$ obtained from the identity matrix by replacing exactly
one off-diagonal zero entry by some element of $D$. For
$bold(X) in G L_n lr((D))$, $bold(E)bold(X)$ is obtained from $bold(X)$ by
increasing some row of $bold(X)$ by a left multiple of another row; likewise,
$bold(X)bold(E)$ is obtained by increasing some column of $bold(X)$ by a right
multiple of another column of $bold(X)$. Given any $bold(X) in G L_n lr((D))$,
we can find products $bold(P)$ and $bold(Q)$ of elementary matrices, such that
$ bold(P)bold(X)bold(Q)="diag"(a_1,dots,a_n),a_i in D. $
Since $"diag"(a,a^(-1))$ is itself a product of elementary matrices (see
@eq:balanced-units-elementary-factorization), we may in fact choose $bold(P)$
and $bold(Q)$ so that
$ bold(P)bold(X)bold(Q)="diag"(1,dots,1,a),a=product_1^n a_i in D^dot. $
<eq:dieudonne-diagonal-reduction>
The image of $a$ in $D^hash$ is called the _Dieudonné determinant_#idx(
  "Dieudonné determinant",
) of $bold(X)$, $det bold(X)$. (If $D$ is a field, then $D^hash=D^dot$, and
$det bold(X)$ is the usual determinant of $bold(X)$. If $D$ is not a field, then
the element $a in D^dot$ above is not uniquely determined by $bold(X)$, but its
image in $D^hash$ is uniquely determined by $bold(X)$.)

In particular, each elementary matrix has determinant $1$. Further,
$
  det mat(bold(X), *; bold(0), bold(Y))=(det bold(X))(det bold(Y))
  "for" bold(X) in G L_n lr((D)),bold(Y) in G L_m lr((D)),
$
and
$
  det(bold(X)bold(Y))=(det bold(X))(det bold(Y))
  "for" bold(X),bold(Y) in G L_n lr((D)).
$
Now apply $"nr"_(A slash K)$ to both sides of @eq:dieudonne-diagonal-reduction,
and use Exercise~@exc:block-matrix-reduced-norm. This gives
$
  "nr"_(A slash K) bold(X)=product_(i=1)^n "nr"_(D slash K) lr((a_i))
  ="nr"_(D slash K) det bold(X),
$
which establishes @eq:reduced-norm-dieudonne-determinant.

In Chapter~10 of Volume~II, it will be necessary to know both the kernel and the
image of the reduced norm map
$ "nr"_(A slash K):A^dot -> K^dot, $
where $A$ is a central simple $K$-algebra, and $A^dot$ is its group of units. We
shall
#source(189)
restrict our attention to the case where $K$ is a global field or its
completion. For each prime $P$ of $K$, the completion $A_P$ is a central simple
$K_P$-algebra. For an infinite prime $P$ of $K$, the field $K_P$ is either the
real field $RR$ or the complex field $CC$.

If $A$ is a central simple $CC$-algebra, then of course
$A tilde.equiv M_n lr((CC))$ for some $n$, and then $"nr" A^dot=CC^dot$. If $A$
is a central simple $RR$-algebra, then we have
$ A tilde.equiv M_n lr((RR)) "or" A tilde.equiv M_n lr((bb(H))), $
where $bb(H)$ is the skewfield of real quaternions; this follows from the fact
that $RR$ and $bb(H)$ are the only f.d. skewfields with center $RR$ (see
@bib:Reiner1975[MO (32.2)]). It is easily seen that $"nr" A^dot=RR^dot$ in the
first case, whereas
$
  "nr" A^dot={alpha in RR:alpha > 0}
  "when" A tilde.equiv M_n lr((bb(H))).
$
<eq:real-quaternion-reduced-norm-image>
On the other hand, the following result is not hard to prove (see
@bib:Reiner1975[MO, Exercise~14.6]):

#theorem[
  Let $A$ be a central simple $K$-algebra, where $K$ is the quotient field of a
  complete d.v.r. $R$ with finite residue class field. Then $"nr" A^dot=K^dot$.
] <th:local-field-reduced-norm-surjective>

In order to describe $"nr" A^dot$ when $K$ is a global field, we need some
notation and definitions. These will play an important role in our later
considerations.

#definition[
  Let $A$ be a central simple $K$-algebra, and let $P$ be any prime of the
  global field $K$. Then
  $ A_P tilde.equiv M_(kappa_P) lr((Omega)),quad (Omega:K_P)=m_P^2, $
  where $Omega$ is a skewfield with center $K_P$. Call $m_P$ the _local
  index_#idx("local index")#idx("index") of $A$ at $P$, and $kappa_P$ the _local
  capacity_#idx("local capacity"). The prime $P$ is _ramified_#idx("ramified")
  in $A$ if $m_P > 1$, and _unramified_#idx("unramified") if $m_P=1$. Define
] <def:local-index-capacity-ramification>
$
  K^+={alpha in K^dot:alpha_P > 0
    "at each real prime" P "of" K "ramified in" A}.
$
<eq:positive-at-ramified-real-primes>
(Thus, $K^+=K^dot$ if $K$ has no real primes, or if each real prime of $K$ is
unramified in $A$. In any case, $K^+$ is a subgroup of $K^dot$ of index a power
of $2$.)

The following deep result is proved in @bib:Reiner1975[MO (33.15)]:

#theorem(name: "Hasse-Schilling-Maass Norm Theorem")[
  Let $A$ be a central simple $K$-algebra, where $K$ is a global field. Then
  $ "nr"_(A slash K) A^dot=K^+, $
  #source(190)
  that is, a nonzero element $alpha in K$ is the reduced norm of an element of
  $A^dot$ if and only if $alpha_P > 0$ at every real prime $P$ of $K$ ramified
  in $A$.
] <th:hasse-schilling-maass-norm>
#idx(
  "Hasse-Schilling-Maass Norm Theorem",
  target: [@th:hasse-schilling-maass-norm],
)
#idx("reduced norm", target: [@th:hasse-schilling-maass-norm])

The fact that $"nr" A^dot subset.eq K^+$ follows readily from
@eq:real-quaternion-reduced-norm-image and the inclusions
$
  {"nr" A^dot}_P subset.eq "nr"{(A^dot)_P}
  subset.eq "nr"{(A_P)^dot}.
$
The converse is a much deeper result.

Turning next to the question of the kernel of the map $"nr":A^dot -> K^dot$, we
observe first that the commutator subgroup $[A^dot,A^dot]$ of $A^dot$ surely
lies in this kernel. For the local case, we quote without proof:

#theorem(title: [Nakayama-Matsushima~@bib:Nakayama1943])[
  Let $A$ be a central simple $K$-algebra, where $K$ is the quotient field of a
  complete d.v.r. with finite residue class field. Then the kernel of the
  surjection
  $ "nr"_(A slash K):A^dot -> K^dot $
  is precisely the commutator subgroup $[A^dot,A^dot]$ of $A^dot$. Thus there is
  an isomorphism
  $ A^dot slash [A^dot,A^dot] tilde.equiv K^dot. $
] <th:nakayama-matsushima>
#idx("Nakayama-Matsushima Theorem", target: [@th:nakayama-matsushima])

As a special case of the above, we have
$ "nr"_(D slash K):D^hash tilde.equiv K^dot, $
<eq:local-division-abelianization-norm>
where $D$ is a skewfield whose center $K$ is a local field as above. We remark
that the analogue of @th:nakayama-matsushima is also correct when $K=RR$ or
$CC$, with $K^dot$ replaced by the reduced norm image $"nr" A^dot$.

The global version of these results is considerably deeper, and we state without
proof:

#theorem(title: [Wang-Platonov])[
  Let $K$ be a global field, and $A$ a central simple $K$-algebra. Then
  $[A^dot,A^dot]$ is the kernel of the reduced norm map
  $"nr"_(A slash K):A^dot -> K^+$, and there is an isomorphism
  $ A^dot slash [A^dot,A^dot] tilde.equiv K^+. $
] <th:wang-platonov>
#idx("Wang-Platonov Theorem", target: [@th:wang-platonov])

The theorem was proved by Wang~@bib:Wang1950 for the case where $K$ is an
algebraic number field. For many years, it was an open question as to whether
the result holds for arbitrary $K$. Platonov~@bib:Platonov1976 recently
established the theorem for the case where $K$ is any global field, not
necessarily an algebraic number field. His work gives another proof of Wang's
original theorem.

Platonov also gave examples in which $ker("nr"_(A slash K))$ properly contains
$[A^dot,A^dot]$; his field $K$ is a field of formal power series in two
variables. Earlier work of Kodama~@bib:Kodama1956, @bib:Kodama1960, attempting
to establish @th:wang-platonov for all fields of characteristic
#source(191)
$0$, contained some errors. Indeed, Platonov's counterexamples include some
cases where $char K=0$.

#exercises-heading

#exercise[
  Let $A$ and $B$ be f.d. separable $K$-algebras, and let $K'$ be an arbitrary
  extension field of $K$. Show
  #enum(
    numbering: "(i)",
    [$K' times.o_K A$ is a separable $K'$-algebra.],
    [$A times.o_K B$ is a separable $K$-algebra.],
  )
  #hint([@exc:separable-field-base-extension])[
    Let $Omega,Omega'$ be algebraic closures of $K$ and $K'$, respectively, with
    $Omega subset.eq Omega'$, and put
    $ A^(K')=K' times.o_K A,A^Omega=Omega times.o_K A. $
    Then
    $ Omega' times.o_(K') A^(K') tilde.equiv Omega' times.o_Omega A^Omega, $
    and
    $ A^Omega times.o_Omega B^Omega tilde.equiv (A times.o_K B)^Omega. $
    Now use @lem:separable-split-extension.
  ]
] <exc:separable-field-base-extension>

#exercise[
  If $A$ is a separable $K$-algebra, show that there exists a finite Galois
  extension $E$ of $K$ which splits $A$ over $K$.
] <exc:separable-galois-splitting-field>

#exercise[
  Let $A=M_n lr((D))$, where $D$ is a skewfield with center $K$. Let $E$ be a
  splitting field for $D$ over $K$, and let
  $ mu:D -> E times.o_K D tilde.equiv M_m lr((E)),m^2=dim_K D. $
  There is an embedding
  $ A -> E times.o_K A tilde.equiv M_(m n) lr((E)), $
  given by
  $
    a=(alpha_(i j)) in M_n lr((D))
    -> (mu(alpha_(i j))) in M_(m n) lr((E)).
  $
  Show that
  $ "nr"_(A slash K) a=det(mu(alpha_(i j))). $
  Deduce from this that if the matrix $a$ is upper triangular, then
  $ "nr"_(A slash K) a=product_(i=1)^n "nr"_(D slash K) alpha_(i i), $
  whence $"nr"_(A slash K) a=1$ for every elementary matrix $a in A$.
] <exc:block-matrix-reduced-norm>

#source(192)
#exercise[
  Keeping the above notation, show that $"nr"_(A slash K) a=0$ if and only if
  $a$ is a nonunit of $A$.
] <exc:reduced-norm-nonunits>

#exercise[
  Keep the above notation. Show that
  $"nr"_(A slash K) lr((A))="nr"_(D slash K) lr((D))$.
] <exc:matrix-algebra-reduced-norm-image>

#exercise[
  Let $A$ be a f.d. $K$-algebra, $T:A times A -> K$ the ordinary trace form
  defined by $T(a,b)=T_(A slash K)(a b)$ for $a,b in A$. Show that if $T$ is
  nondegenerate, then $A$ is a separable $K$-algebra.
  #hint([@exc:separable-trace-form])[
    For any field $E supset.eq K$, $T^E:A^E times A^E -> E$ is nondegenerate.
    Then $A^E$ is semisimple by Exercise~@exc:nondegenerate-trace-semisimple.
  ]
] <exc:separable-trace-form>

#exercise[
  Prove the analogue of @th:nakayama-matsushima when $K=RR$ or $CC$, with
  $K^dot$ replaced by the reduced norm image $"nr" A^dot$.
] <exc:real-complex-norm-commutator-kernel>

#exercise[
  Let $D$ be a f.d. division algebra over its center $K$, and let $[D,D]$ be the
  $K$-space consisting of all finite sums $sum(a_i b_i-b_i a_i)$,
  $a_i,b_i in D$. Show that $[D,D]$ is properly contained in $D$.
  #hint([@exc:division-algebra-additive-commutators])[
    Let $E$ be a maximal subfield of $D$, and put $D^E=E times.o_K D$. It
    suffices to prove that $[D^E,D^E] != D^E$. But this is obvious because
    $D^E tilde.equiv M_n lr((E))$ for some $n$, and every element of $[D^E,D^E]$
    has trace zero.
  ]
] <exc:division-algebra-additive-commutators>

#exercise[
  Let $A$ be a f.d. $K$-algebra, and let $V,W$ be f.g. left $A$-modules. For $E$
  an extension field of $K$, let $A^E=E times.o_K A$, $V^E=E times.o_K V$, and
  so on. Show that the $A^E$-modules $V^E$ and $W^E$ have a common composition
  factor if and only if $V$ and $W$ have a common composition factor as
  $A$-modules.
  #hint([@exc:base-extension-common-composition-factor])[
    Let $"cf"(V)$ be the set of composition factors of $V$. If $"cf"(V)={V_i}$,
    then $"cf"(V^E)=union_i "cf"(V_i^E)$. Hence if $V$ and $W$ have a common
    composition factor, then so do $V^E$ and $W^E$. To prove the converse, we
    need only show that for $V$ and $W$ non-isomorphic simple $A$-modules, $V^E$
    and $W^E$ have no common composition factor. Viewing $V$ and $W$ as simple
    $(A slash (rad A))$-modules, we can find an element $a in A$ whose image
    acts as $1$ on $V$ and as $0$ on $W$. Then $a$ itself acts in this manner on
    $V$ and $W$, so $1 times.o a in A^E$ acts as $1$ on each composition factor
    of $V^E$, and as $0$ on each composition factor of $W^E$.
  ]
] <exc:base-extension-common-composition-factor>

#exercise[
  #enum(
    numbering: "(a)",
    [Let $E_1,E_2$ be arbitrary extension fields of $K$. Prove that there exists
      a _composite field extension_ $E$ of $K$, with $K$-embeddings
      $tau_i:E_i -> E$, $i=1,2$, such that
      $E=tau_1 lr((E_1)) dot tau_2 lr((E_2))$.],
    [Let $E_1,dots,E_n$ be a set of finite separable extensions of the field
      $K$. Show that there exists a finite separable extension field $E$
      containing $K$ for which there exist $K$-isomorphisms $mu_i:E_i -> E$,
      $1 <= i <= n$.],
  )
  #hint([@exc:composite-field-extension])[
    (a) Take a maximal ideal $I$ in the $K$-algebra $E_1 times.o_K E_2$, and let
    $E=(E_1 times.o E_2) slash I$.

    (b) The desired $E$ is just a composite of the ${E_i}$ over $K$, and may be
    constructed as follows: let
    $ B=E_1 times.o_K dots.c times.o_K E_n, $
    a commutative separable $K$-algebra. Then $B$ is expressible as a direct sum
    $product B_j$, with
    #source(193)
    each $B_j$ a finite separable field extension of $K$. For each $i$, the
    desired embedding of $E_i$ in the field $B_1$ is given by composition of
    maps
    $
      E_i -> 1 times.o dots.c times.o E_i times.o dots.c times.o 1
      subset.eq B -> B_1.
    $
  ]
] <exc:composite-field-extension>

#exercise[
  Let $E$ be a finite extension of the field $K$, and let $Omega$ be an
  algebraic closure of $K$. Let ${sigma_1,dots,sigma_n}$ be the distinct
  $K$-embeddings of $E$ into $Omega$. Prove *Artin's Theorem*#idx(
    "Artin's Theorem",
  ):

  _As maps from $E$ to $Omega$, the functions ${sigma_1,dots,sigma_n}$ are
  linearly independent over $Omega$._

  #hint([@exc:artin-embeddings-independent])[
    Suppose the result false, and let
    $ a_1 sigma_1+dots+a_r sigma_r=0,a_i in Omega,a_i != 0, $
    be a relation of shortest length $r$. Clearly $r >= 2$, and there exists an
    $x_0 in E$ for which $sigma_1 lr((x_0)) != sigma_2 lr((x_0))$. Then
    $
      sum_(i=1)^r a_i sigma_i lr((x_0))sigma_i lr((x))=0, quad
      sum_(i=1)^r a_i sigma_1 lr((x_0))sigma_i lr((x))=0
    $
    for all $x in E$. Subtracting one equation from the other, we obtain a
    shorter relation of linear dependence, connecting $sigma_2,dots,sigma_r$.
    (See also @exm:galois-twisted-group-algebra below.)
  ]
  (As Artin pointed out, the same argument shows that any set of distinct
  homomorphisms ${sigma_1,dots,sigma_n}$ of a group $G$ (not necessarily finite)
  into the multiplicative group of a field $Omega$, are linearly independent
  over $Omega$.)
] <exc:artin-embeddings-independent>

#exercise[
  Let $E$ be a finite extension of the field $K$. Show that $E$ is separable
  over $K$ if and only if there exists an element $x_0 in E$ for which
  $T_(E slash K) lr((x_0)) != 0$.
  #hint([@exc:separable-field-nonzero-trace])[
    Use Exercises~@exc:separable-trace-form and
    @exc:artin-embeddings-independent.
  ]
] <exc:separable-field-nonzero-trace>

#exercise[
  Let $A$ be a f.d. separable $K$-algebra, and $V$ any f.g. left $A$-module.
  Prove that $End_A V$ is also a f.d. separable $K$-algebra.
  #hint([@exc:separable-module-endomorphism-algebra])[
    Use Exercise~@exc:semisimple-module-endomorphisms.
  ]
] <exc:separable-module-endomorphism-algebra>
