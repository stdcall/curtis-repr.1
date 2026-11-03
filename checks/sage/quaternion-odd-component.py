"""Exact m=3 check for the odd generalized-quaternion component.

This checks one rational component and its local ramification, not the
general decomposition for all odd m or all ground fields.
"""
from sage.all import (QQ, GF, PolynomialRing, QuadraticField,
                      QuaternionAlgebra, matrix)

checked = []


def check(name, condition):
    assert condition, name
    checked.append(name)


component = QuaternionAlgebra(QQ, -3, -1)
u, y, uy = component.gens()
x = (component(1) + u) / 2
check('cyclotomic relation', x*x - x + 1 == 0)
check('central sign', x**3 == -1 and x**6 == 1)
check('second generator square', y*y == -1)
check('conjugation relation', y*x*(y**(-1)) == x**(-1))

elements = [x**k * y**j for j in range(2) for k in range(6)]
coordinates = {tuple(g.coefficient_tuple()) for g in elements}
check('twelve distinct group elements', len(coordinates) == 12)
check('multiplication closes', all(tuple((g*h).coefficient_tuple()) in coordinates
                                    for g in elements for h in elements))

gaussian = QuadraticField(-1, 'ii')
ii = gaussian.gen()
columns = []
for j in range(2):
    for k in range(6):
        value = gaussian((-1)**k) * ii**j
        pair = (value.list() + [QQ(0), QQ(0)])[:2]
        columns.append(pair + list((x**k * y**j).coefficient_tuple()))
check('minus central block has full image dimension six',
      matrix(QQ, columns).rank() == 6)
check('quaternion central projector', (x + x**(-1) + 2)/3 == 1)
check('Gaussian central projector', (gaussian(-1) + gaussian(-1) + 2)/3 == 0)

polynomials = PolynomialRing(QQ, names=('a', 'b', 'c', 'd'))
a, b, c, d = polynomials.gens()
left_multiplication = matrix(polynomials, [
    [a, -3*b, -c, -3*d],
    [b, a, -d, c],
    [c, 3*d, a, -3*b],
    [d, -c, b, a],
])
norm = a*a + 3*b*b + c*c + 3*d*d
check('symbolic regular determinant', left_multiplication.det() == norm**2)
check('modulo three sum of two squares',
      all(s == 0 and t == 0 for s in GF(3) for t in GF(3)
          if s*s + t*t == 0))
check('different finite ramification',
      component.ramified_primes() == [3]
      and QuaternionAlgebra(QQ, -1, -1).ramified_primes() == [2])
print(f'{len(checked)} exact odd-quaternion component checks passed')
