from fractions import Fraction
from math import comb, factorial, isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def moment(r):
    return Fraction(sum((-1)**j * comb(2*r, j) * (r-j)**(2*r-1)
                        for j in range(r)), factorial(2*r-1))

def ratstr(q, typ='ℝ'):
    return f'({q.numerator} : {typ}) / {q.denominator}'

def generate_test():
    lines = ['import LittlewoodInverse.SincFormula', '',
             'open scoped BigOperators', 'namespace LittlewoodInverse.MomentCertificateTest',
             'open SincFormula', 'set_option maxRecDepth 8192',
             'set_option maxHeartbeats 0', '']
    for r in [3, 40, 81]:
        q = moment(r)
        lines += [f'theorem even_rat_{r} : evenMomentRat {r} = {ratstr(q, "ℚ")} := by',
                  '  norm_num [evenMomentRat, Finset.sum_range_succ,',
                  '    Nat.choose_eq_descFactorial_div_factorial]', '']
    lines += ['end LittlewoodInverse.MomentCertificateTest', '']
    (ROOT / 'LittlewoodInverse' / 'MomentCertificateTest.lean').write_text('\n'.join(lines), encoding='utf-8')

def generate_certificate():
    scale = 10**24
    moments = {2*r: moment(r) for r in range(1,82)}
    bounds = {}
    for k in range(5,161):
        if k % 2 == 0:
            q = moments[k]
            numerator = (q.numerator * scale + q.denominator - 1) // q.denominator
        else:
            q = moments[k-1] * moments[k+1]
            numerator = isqrt(q.numerator * scale**2 // q.denominator) + 1
            assert Fraction(numerator, scale)**2 >= q
        bounds[k] = numerator
    a = Fraction(9,10)
    error = Fraction(55,108)*a*a + (Fraction(2,3)*(Fraction(5,6)*a**4-Fraction(2,3)*a**3)
        +2*sum((a**k*Fraction(bounds[k],scale)/k for k in range(5,161)), Fraction(0))
        +2*a**161/(161*(1-a)))/9
    assert error < Fraction(479084457020255861, 10**18)
    def header(dependency):
        return [f'import LittlewoodInverse.{dependency}', '',
                'open scoped BigOperators', 'namespace LittlewoodInverse.MomentCertificate',
                'open SincFormula', 'set_option maxRecDepth 16384',
                'set_option maxHeartbeats 0', '']
    def write_module(name, content):
        (ROOT / 'LittlewoodInverse' / (name+'.lean')).write_text(
            '\n'.join(content + ['end LittlewoodInverse.MomentCertificate', '']), encoding='utf-8')
    lines = header('SincFormula')
    for k in range(4,163,2):
        r, q = k//2, moments[k]
        lines += [f'theorem sincMoment_{k} : sincMoment {k} = {ratstr(q)} := by',
                  f'  change sincMoment (2 * {r} : ℕ) = _',
                  f'  rw [sincMoment_even_eq_rat {r} (by decide)]',
                  '  norm_num [evenMomentRat, Finset.sum_range_succ,',
                  '    Nat.choose_eq_descFactorial_div_factorial]', '']
    write_module('EvenMomentCertificate', lines)
    lines = header('EvenMomentCertificate')
    for k in range(5,161):
        lines += [f'theorem coefficient_le_{k} : momentCoefficient {k} ≤ ({bounds[k]} : ℝ) / {scale} := by']
        if k%2 == 0:
            lines += [f'  rw [momentCoefficient, if_pos (by decide : Even {k})]',
                      '  norm_num only [Nat.cast_ofNat]',
                      f'  norm_num [sincMoment_{k}]', '']
        else:
            lines += [f'  rw [momentCoefficient, if_neg (by decide : ¬Even {k})]',
                      '  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]',
                      f'  rw [sincMoment_{k-1}, sincMoment_{k+1}]',
                      '  apply (Real.sqrt_le_iff).mpr',
                      '  constructor <;> norm_num', '']
    write_module('CoefficientValues', lines)
    lines = header('CoefficientValues')
    lines += ['def coefficientBound : ℕ → ℚ']
    for k in range(5,161):
        lines += [f'  | {k-5} => ({bounds[k]} : ℚ) / {scale}']
    lines += ['  | _ => 0', '',
              'theorem coefficientBound_valid (j : ℕ) (hj : j < 156) :',
              '    momentCoefficient (j + 5) ≤ (coefficientBound j : ℝ) := by',
              '  interval_cases j']
    for k in range(5,161):
        lines += [f'  · convert coefficient_le_{k} using 1', '    norm_num [coefficientBound]']
    write_module('CoefficientBounds', lines)
    lines = header('CoefficientBounds')
    lines += ['theorem finite_error_bound :',
              '    (55 : ℝ) * (9 / 10)^2 / 108 + (1 / 9 : ℝ) *',
              '      ((2 / 3 : ℝ) * (5 * (9 / 10)^4 / 6 - 2 * (9 / 10)^3 / 3) +',
              '       2 * (∑ j ∈ Finset.range 156, (9 / 10 : ℝ)^(j + 5) / ((j : ℝ) + 5) *',
              '         (coefficientBound j : ℝ)) +',
              '       2 * (9 / 10 : ℝ)^161 / (161 * (1 - (9 / 10 : ℝ)))) ≤',
              '      (479084457020255861 : ℝ) / 10^18 := by',
              '  norm_num [Finset.sum_range_succ, coefficientBound]', '']
    write_module('MomentCertificate', lines)

if __name__ == '__main__':
    generate_test()
    generate_certificate()
