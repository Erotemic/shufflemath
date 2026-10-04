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


def rising_sequences(perm: tuple[int, ...] | list[int]) -> int:
    """Number of maximal increasing runs in a permutation written in one-line form."""
    if not perm:
        return 0
    return 1 + sum(a > b for a, b in zip(perm, perm[1:]))


def stable_sort_cards(order: list[int] | tuple[int, ...], labels: list[int] | tuple[int, ...]) -> list[int]:
    """Stable-sort card identities by labels attached to the original cards.

    ``order`` contains 1-based card identities. ``labels[i - 1]`` is the label
    permanently attached to card ``i``. Python's sort is stable, exactly matching
    the inverse-riffle construction used in the presentation.
    """
    if not order:
        return []
    if min(order) < 1 or max(order) > len(labels):
        raise ValueError("order contains a card without a label")
    return sorted(order, key=lambda card_id: labels[card_id - 1])


def gsr_perm_probability(n: int, riffles: int, rising: int) -> Fraction:
    """Probability of one particular permutation with ``rising`` runs.

    Bayer--Diaconis' ``a``-shuffle formula with ``a = 2**riffles``.
    """
    if n < 1:
        raise ValueError("n must be positive")
    if riffles < 0:
        raise ValueError("riffles must be nonnegative")
    if not 1 <= rising <= n:
        return Fraction(0)
    a = 2**riffles
    top = a + n - rising
    if top < n:
        return Fraction(0)
    return Fraction(comb(top, n), a**n)


def uniform_rising_mass(n: int, rising: int) -> Fraction:
    """Uniform probability that a permutation has ``rising`` increasing runs."""
    if not 1 <= rising <= n:
        return Fraction(0)
    return Fraction(eulerian_row(n)[rising - 1], factorial(n))


def gsr_rising_mass(n: int, riffles: int, rising: int) -> Fraction:
    """GSR probability mass of the entire ``rising``-run class."""
    if not 1 <= rising <= n:
        return Fraction(0)
    return eulerian_row(n)[rising - 1] * gsr_perm_probability(n, riffles, rising)


def gsr_likelihood_ratio(n: int, riffles: int, rising: int) -> Fraction:
    """Likelihood ratio Q/U for any permutation with ``rising`` runs."""
    return gsr_perm_probability(n, riffles, rising) * factorial(n)


def gsr_tv_via_rising(n: int, riffles: int) -> Fraction:
    """Exact TV after collapsing permutations by their rising-sequence count."""
    return sum(
        (
            abs(gsr_rising_mass(n, riffles, r) - uniform_rising_mass(n, r))
            for r in range(1, n + 1)
        ),
        Fraction(0),
    ) / 2


def gsr_optimal_rising_event(n: int, riffles: int) -> tuple[int, Fraction, Fraction, Fraction]:
    """The monotone likelihood-ratio TV witness ``R <= threshold``.

    Returns ``(threshold, Q(event), U(event), Q(event)-U(event))``.
    For GSR the likelihood ratio decreases with the number of rising runs, so
    this event realizes total variation.
    """
    favored = [r for r in range(1, n + 1) if gsr_likelihood_ratio(n, riffles, r) >= 1]
    threshold = max(favored, default=0)
    q = sum((gsr_rising_mass(n, riffles, r) for r in range(1, threshold + 1)), Fraction(0))
    u = sum((uniform_rising_mass(n, r) for r in range(1, threshold + 1)), Fraction(0))
    return threshold, q, u, q - u


def uniform_rising_moments(n: int) -> tuple[Fraction, Fraction]:
    """Exact mean and variance of the number of rising sequences under uniformity."""
    if n < 1:
        raise ValueError("n must be positive")
    masses = [uniform_rising_mass(n, r) for r in range(1, n + 1)]
    mean = sum((Fraction(r) * p for r, p in enumerate(masses, start=1)), Fraction(0))
    second = sum((Fraction(r * r) * p for r, p in enumerate(masses, start=1)), Fraction(0))
    return mean, second - mean * mean


def gsr_likelihood_step_ratio(n: int, riffles: int, rising: int) -> Fraction:
    """Exact ratio ``L(r+1)/L(r)`` for the GSR likelihood ratio.

    For ``1 <= rising < min(n, 2**riffles + 1)`` this simplifies to
    ``(a-rising)/(a+n-rising)`` with ``a = 2**riffles``.
    """
    if n < 1:
        raise ValueError("n must be positive")
    if riffles < 0:
        raise ValueError("riffles must be nonnegative")
    if not 1 <= rising < n:
        raise ValueError("rising must satisfy 1 <= rising < n")
    current = gsr_likelihood_ratio(n, riffles, rising)
    following = gsr_likelihood_ratio(n, riffles, rising + 1)
    if current == 0:
        raise ZeroDivisionError("likelihood ratio is already zero")
    return following / current


def hypergeom_pmf(good: int, bad: int, draws: int, got_good: int) -> Fraction:
    """Exact hypergeometric probability.

    There are ``good`` marked objects and ``bad`` unmarked objects. Draw
    ``draws`` uniformly without replacement. Return the probability of seeing
    exactly ``got_good`` marked objects.
    """
    if min(good, bad, draws) < 0 or draws > good + bad:
        raise ValueError("invalid hypergeometric parameters")
    if got_good < 0 or got_good > draws or got_good > good or draws - got_good > bad:
        return Fraction(0)
    return Fraction(comb(good, got_good) * comb(bad, draws - got_good), comb(good + bad, draws))


def bl_support(N: int, m: int, r: int) -> range:
    """Feasible values of X = number of red cards in the left pile."""
    if not (0 <= r <= N and 0 <= m <= N):
        raise ValueError("require 0 <= r,m <= N")
    lo = max(0, m - (N - r))
    hi = min(m, r)
    return range(lo, hi + 1)


def bl_stationary(N: int, m: int, r: int, x: int) -> Fraction:
    """Hypergeometric stationary law for the two-urn membership chain."""
    if x not in bl_support(N, m, r):
        return Fraction(0)
    return Fraction(comb(r, x) * comb(N - r, m - x), comb(N, m))


def bl_transition(N: int, m: int, r: int, k: int, x: int, y: int) -> Fraction:
    """Exact Bernoulli--Laplace transition probability P(X'=y | X=x).

    The left pile has ``m`` cards and the right pile has ``N-m``. There are
    ``r`` red cards total. A step samples ``k`` cards uniformly from each pile
    and swaps the two samples.
    """
    if not (0 <= k <= min(m, N - m)):
        raise ValueError("exchange size exceeds one of the piles")
    if x not in bl_support(N, m, r) or y not in bl_support(N, m, r):
        return Fraction(0)
    total = Fraction(0)
    # A = red cards leaving the left; B = red cards entering from the right.
    for a in range(k + 1):
        b = y - x + a
        p_leave = hypergeom_pmf(x, m - x, k, a)
        p_enter = hypergeom_pmf(r - x, (N - m) - (r - x), k, b)
        total += p_leave * p_enter
    return total


def bl_conditional_mean(N: int, m: int, r: int, k: int, x: int) -> Fraction:
    """Exact E[X' | X=x] from the two hypergeometric sample means."""
    if x not in bl_support(N, m, r):
        raise ValueError("infeasible state")
    if not (0 <= k <= min(m, N - m)):
        raise ValueError("exchange size exceeds one of the piles")
    return Fraction(x) - Fraction(k * x, m) + Fraction(k * (r - x), N - m)


def bl_stationary_mean(N: int, m: int, r: int) -> Fraction:
    """Mean of the hypergeometric stationary count X."""
    return Fraction(m * r, N)


def bl_centered_mean_factor(N: int, m: int, k: int) -> Fraction:
    """First centered-count eigenvalue lambda for Bernoulli--Laplace."""
    return Fraction(1) - Fraction(N * k, m * (N - m))


def bl_centered_drift(N: int, m: int, r: int, k: int, x: int) -> Fraction:
    """Return E[X'-mu | X=x], where mu=m*r/N."""
    return bl_conditional_mean(N, m, r, k, x) - bl_stationary_mean(N, m, r)
