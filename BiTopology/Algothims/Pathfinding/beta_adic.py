"""
β-adic operations for Gaussian integers.

This module implements the core β-adic representation using base β = -1 + i.
The operations mirror those proven in PathPlanning.lean.
"""

from typing import Tuple, List
from functools import lru_cache


def digit(z: complex) -> bool:
    """
    Compute the least significant digit of z in base β = -1 + i.
    
    Returns True (digit 1) if β does not divide z, False (digit 0) otherwise.
    β divides z iff z.real % 2 == z.imag % 2.
    """
    return int(z.real) % 2 != int(z.imag) % 2


def beta_quot(z: complex) -> complex:
    """
    Compute the β-quotient: z = digit(z) + β * βQuot(z).
    
    This is the "shift right" operation in base β.
    """
    re, im = int(z.real), int(z.imag)
    
    if digit(z):
        # Subtract 1 to make divisible by β
        re -= 1
    
    # βQuotAux: divide by β = -1 + i
    # β * q = z means q = z / β = z * conj(β) / |β|² = z * (-1 - i) / 2
    # For z = (re, im): q = ((im - re) / 2, -(re + im) / 2)
    new_re = (im - re) // 2
    new_im = -((re + im) // 2)
    
    return complex(new_re, new_im)


def nth_digit(z: complex, n: int) -> bool:
    """
    Get the n-th digit (0-indexed from least significant) of z in base β.
    """
    current = z
    for _ in range(n):
        current = beta_quot(current)
    return digit(current)


def cylinder_pattern(z: complex, k: int) -> Tuple[bool, ...]:
    """
    Get the k-digit cylinder pattern of z (first k digits from LSD).
    
    Two points are in the same k-cylinder iff they have the same k-pattern.
    """
    if k == 0:
        return ()
    
    pattern = []
    current = z
    for _ in range(k):
        pattern.append(digit(current))
        current = beta_quot(current)
    
    return tuple(pattern)


def cylinder_distance(z: complex, w: complex) -> int:
    """
    Compute the cylinder distance: the first index where patterns differ.
    
    Returns 0 if z == w, otherwise the smallest k where nth_digit(z, k-1) != nth_digit(w, k-1).
    """
    if z == w:
        return 0
    
    # Find first differing digit
    cz, cw = z, w
    k = 0
    while True:
        k += 1
        if digit(cz) != digit(cw):
            return k
        cz = beta_quot(cz)
        cw = beta_quot(cw)
        
        # Safety limit (cylinder distance is O(log(norm)))
        if k > 100:
            raise ValueError(f"Cylinder distance computation exceeded limit for {z}, {w}")


def beta_pow(k: int) -> complex:
    """
    Compute β^k where β = -1 + i.
    """
    if k == 0:
        return complex(1, 0)
    
    result = complex(1, 0)
    base = complex(-1, 1)
    
    for _ in range(k):
        result *= base
    
    return result


def iterate_beta_quot(z: complex, k: int) -> complex:
    """
    Apply βQuot k times: equivalent to z // β^k.
    """
    result = z
    for _ in range(k):
        result = beta_quot(result)
    return result


def grid_distance(z: complex, w: complex) -> int:
    """
    Chebyshev distance on the grid: max(|Δre|, |Δim|).
    """
    dre = abs(int(z.real) - int(w.real))
    dim = abs(int(z.imag) - int(w.imag))
    return max(dre, dim)


def grid_neighbors(z: complex) -> List[complex]:
    """
    Return the 8 grid neighbors of z (8-connectivity).
    """
    re, im = int(z.real), int(z.imag)
    return [
        complex(re + 1, im),
        complex(re - 1, im),
        complex(re, im + 1),
        complex(re, im - 1),
        complex(re + 1, im + 1),
        complex(re + 1, im - 1),
        complex(re - 1, im + 1),
        complex(re - 1, im - 1),
    ]


# Optimized version using bit operations for speed
def cylinder_pattern_fast(x: int, y: int, k: int) -> int:
    """
    Fast cylinder pattern computation using bit operations.
    
    Returns an integer encoding the k-bit pattern.
    For efficiency in set operations and hashing.
    """
    if k == 0:
        return 0
    
    pattern = 0
    re, im = x, y
    
    for i in range(k):
        # digit: re % 2 != im % 2
        d = (re & 1) ^ (im & 1)
        pattern |= (d << i)
        
        # beta_quot
        if d:
            re -= 1
        new_re = (im - re) >> 1
        new_im = -((re + im) >> 1)
        re, im = new_re, new_im
    
    return pattern


def cylinder_distance_fast(x1: int, y1: int, x2: int, y2: int) -> int:
    """
    Fast cylinder distance using integer coordinates.
    """
    if x1 == x2 and y1 == y2:
        return 0
    
    re1, im1 = x1, y1
    re2, im2 = x2, y2
    k = 0
    
    while k < 100:
        k += 1
        d1 = (re1 & 1) ^ (im1 & 1)
        d2 = (re2 & 1) ^ (im2 & 1)
        
        if d1 != d2:
            return k
        
        # beta_quot for both
        if d1:
            re1 -= 1
            re2 -= 1
        
        new_re1 = (im1 - re1) >> 1
        new_im1 = -((re1 + im1) >> 1)
        re1, im1 = new_re1, new_im1
        
        new_re2 = (im2 - re2) >> 1
        new_im2 = -((re2 + im2) >> 1)
        re2, im2 = new_re2, new_im2
    
    raise ValueError("Cylinder distance exceeded limit")


if __name__ == "__main__":
    # Test basic operations
    print("Testing β-adic operations...")
    
    # Test digit
    assert digit(complex(0, 0)) == False  # 0 is divisible by β
    assert digit(complex(1, 0)) == True   # 1 is not divisible by β
    assert digit(complex(0, 1)) == True   # i is not divisible by β
    assert digit(complex(1, 1)) == False  # 1+i is divisible by β
    
    # Test beta_quot
    z = complex(2, 0)
    print(f"βQuot({z}) = {beta_quot(z)}")
    
    # Test cylinder pattern
    z = complex(5, 3)
    print(f"Cylinder pattern of {z} (k=4): {cylinder_pattern(z, 4)}")
    
    # Test cylinder distance
    z, w = complex(0, 0), complex(10, 10)
    print(f"Cylinder distance {z} to {w}: {cylinder_distance(z, w)}")
    
    # Test fast versions match
    x, y = 5, 3
    assert cylinder_pattern_fast(x, y, 4) == sum(
        d << i for i, d in enumerate(cylinder_pattern(complex(x, y), 4))
    )
    print("Fast pattern matches standard pattern ✓")
    
    print("All tests passed!")
