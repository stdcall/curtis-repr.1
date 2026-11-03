"""Exact bounded checks for Proposition 3.56(ii).

The printed separated coefficients fail already for A=B=M_2(Q), with the
usual simple modules Q^2. The assertion itself is correct. The reconstruction
below is a polynomial matrix identity for factors of dimensions2 and2 only;
it is not a proof for all sizes, division algebras, or Morita equivalence.
"""
from sage.all import QQ, ZZ, PolynomialRing, matrix, zero_matrix

count = 0

# The image of the first tensor basis vector is e1⊗e1 + e2⊗e2.
f = zero_matrix(QQ,4,4)
f[0,0] = f[3,0] = 1
image_coefficients = matrix(QQ,2,2,[f[i*2+j,0] for i in range(2) for j in range(2)])
assert image_coefficients == matrix.identity(QQ,2)
assert image_coefficients.rank() == 2
assert f.rank() == 1
count += 3

# Every separated printed expression has rank ≤1. This is a polynomial
# determinant identity in all four coefficient parameters, not sampling.
p = PolynomialRing(ZZ,names=('d0','d1','e0','e1'))
d0,d1,e0,e1 = p.gens()
printed_image = matrix(p,2,2,[d0*e0,d0*e1,d1*e0,d1*e1])
assert printed_image.det() == 0
assert image_coefficients.det() == 1
count += 2

# Arbitrary4×4 matrix reconstructed from all16 tensor matrix units.
q = PolynomialRing(ZZ,names=tuple(f'c{i}' for i in range(16)))
arbitrary = matrix(q,4,4,q.gens())
reconstructed = zero_matrix(q,4,4)
for k in range(2):
    for l in range(2):
        for i in range(2):
            for j in range(2):
                a = zero_matrix(q,2,2); a[k,i] = 1
                b = zero_matrix(q,2,2); b[l,j] = 1
                reconstructed += arbitrary[2*k+l,2*i+j] * a.tensor_product(b)
for row in range(4):
    for col in range(4):
        assert reconstructed[row,col] == arbitrary[row,col]
        count += 1

print(f'ok tensor-matrices: {count} exact checks')
