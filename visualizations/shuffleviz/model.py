"""Small exact models that drive the presentation graphics.

These computations are a checked visual companion, not the proof authority.
Lean remains the certificate layer.  We deliberately keep the functions small
and transparent so slide numbers are reproducible without NumPy or SciPy.
"""
from __future__ import annotations

from fractions import Fraction
from functools import lru_cache
from math import comb, factorial, log10


def eulerian_row(n: int) -> list[int]:
    """Return ``[A(n,0), ..., A(n,n-1)]`` using the standard recurrence."""
    if n < 1:
        raise ValueError("n must be positive")
    row = [1]
    for m in range(2, n + 1):
        nxt = [0] * m
        for j in range(m):
            left = (m - j) * (row[j - 1] if j > 0 else 0)
            right = (j + 1) * (row[j] if j < len(row) else 0)
            nxt[j] = left + right
        row = nxt
    return row


def gsr_tv(n: int, riffles: int) -> Fraction:
    """Exact total variation after ``riffles`` ideal GSR riffles on ``n`` cards."""
    if riffles < 0:
        raise ValueError("riffles must be nonnegative")
    if riffles == 0:
        return Fraction(factorial(n) - 1, factorial(n))
    a = 2**riffles
    denom_shuffle = a**n
    uniform = Fraction(1, factorial(n))
    total = Fraction(0)
    for descents, count in enumerate(eulerian_row(n)):
        rising = descents + 1
        p = Fraction(comb(a + n - rising, n), denom_shuffle)
        total += count * abs(p - uniform)
    return total / 2


def first_mode_factor(N: int, m: int, k: int) -> Fraction:
    return Fraction(1) - Fraction(N * k, m * (N - m))


def commander_count(state: int) -> int:
    """Decode presentation state ``0..49`` as the physical count ``1..50``."""
    if not 0 <= state < 50:
        raise ValueError(state)
    return state + 1


@lru_cache(maxsize=None)
def commander_transition(k: int, x_state: int, y_state: int) -> Fraction:
    """Exact 99-card, 50/49 Bernoulli--Laplace transition entry.

    Uses the single-sum formula: once ``x``, ``y`` and the number ``a`` of
    original-left cards leaving the left pile are fixed, the number returning
    from the right is forced to be ``b = y - x + a``.
    """
    if not 0 <= k <= 49:
        raise ValueError(k)
    x = commander_count(x_state)
    y = commander_count(y_state)
    denom = comb(50, k) * comb(49, k)
    num = 0
    for a in range(k + 1):
        b = y - x + a
        if not 0 <= b <= k:
            continue
        num += (
            comb(x, a)
            * comb(50 - x, k - a)
            * comb(50 - x, b)
            * comb(x - 1, k - b)
        )
    return Fraction(num, denom)


@lru_cache(maxsize=None)
def commander_matrix(k: int) -> tuple[tuple[Fraction, ...], ...]:
    return tuple(
        tuple(commander_transition(k, x, y) for y in range(50))
        for x in range(50)
    )


def commander_stationary() -> tuple[Fraction, ...]:
    denom = comb(99, 50)
    return tuple(
        Fraction(comb(50, x) * comb(49, 50 - x), denom)
        for x in range(1, 51)
    )


def mat_step(p: tuple[Fraction, ...], matrix: tuple[tuple[Fraction, ...], ...]) -> tuple[Fraction, ...]:
    return tuple(sum((p[x] * matrix[x][y] for x in range(50)), Fraction(0)) for y in range(50))


def commander_distribution(k: int, steps: int) -> tuple[Fraction, ...]:
    p = tuple(Fraction(1 if x == 49 else 0) for x in range(50))
    matrix = commander_matrix(k)
    for _ in range(steps):
        p = mat_step(p, matrix)
    return p


def tv(p: tuple[Fraction, ...], q: tuple[Fraction, ...]) -> Fraction:
    return sum((abs(a - b) for a, b in zip(p, q)), Fraction(0)) / 2


def commander_tv(k: int, steps: int) -> Fraction:
    return tv(commander_distribution(k, steps), commander_stationary())


def commander_tv_series(k: int = 25, max_steps: int = 4) -> list[float]:
    return [float(commander_tv(k, step)) for step in range(max_steps + 1)]


def safe_log10(x: float, floor: float = -8.0) -> float:
    return max(floor, log10(max(x, 10**floor)))


def protocol_cost(local_rounds: tuple[int, ...], exchanges: tuple[int, ...], local_cost: float, exchange_cost: float) -> float:
    if len(local_rounds) != len(exchanges) + 1:
        raise ValueError("local_rounds must have one more entry than exchanges")
    return sum(local_rounds) * local_cost + len(exchanges) * exchange_cost
