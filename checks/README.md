# Mathematical checks

`just check-sage` tests the rank-two image that the separated coefficients
in Proposition 3.56(ii) fail to represent. It also reconstructs an arbitrary
4-by-4 matrix over an integer polynomial ring from the sixteen tensor matrix
units. These 21 exact checks concern factors of dimensions 2 and 2; they do
not prove the general Morita or density theorems.

The same Sage target runs 12 exact checks for Example 7.40
(`exm:quaternion-group-algebra-reduced-norm`) at m=3. They verify the
twelve group elements and relations, the six-dimensional minus-central
image, its Gaussian and quaternion projectors, the symbolic quaternion
norm determinant, and the distinct finite ramification of (-3,-1) and
Hamilton’s (-1,-1). These checks cover this rational example; the general
odd-m decomposition and its proof are outside their scope.

The finite-group checks also test the metacyclic presentation at D₈ against
the kernel criterion of Theorem 11.43
(`th:representation-group-characterization`). They verify all products and
associativity of the sixteen-element model, its derived group and kernel,
and the valid D₁₆ cover. For Proposition 12.11
(`prop:symmetric-intertwining-invariant-properties`), exact C₃ character
averages show that two dual linear modules have invariant zero and their
tensor product has invariant one. These are bounded counterexamples;
they do not establish a general cover presentation or indicator theorem.
The cyclic C₁₂ presentation with m=4, r=1, s=3, t=3 separately tests the
necessary constraint ξᵐ=1 in the metacyclic multiplier calculation: only
one of the three roots allowed by the other two constraints is admissible.

`just check-lean` compiles the declarations listed in `lean-proofs.json`
and audits their axioms. Schur's kernel and image argument and the resulting
inverse endomorphism are checked for arbitrary simple left modules. The
tensor adjunction is checked in the commutative specialization `A=B=K`,
including evaluation and both inverse identities. The full noncommutative
bimodule adjunction is outside those declarations.

The manifest binds each declaration to semantic passage labels and states
its scope. Lean, mathlib and the SageMath CI image are pinned. A prebuilt
local mathlib checkout may be selected with `LEAN_MATHLIB`; local checks
do not install or update it. The compiler must report exactly the listed
axiom audits, with no warnings or unfinished proofs. Only `propext`,
`Classical.choice` and `Quot.sound` are allowed.
