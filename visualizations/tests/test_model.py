from fractions import Fraction

import pytest

from shuffleviz import model


def test_gsr_reference_values():
    assert float(model.gsr_tv(52, 7)) == pytest.approx(0.3340609995, abs=2e-10)
    assert float(model.gsr_tv(99, 9)) == pytest.approx(0.21996960076, abs=2e-10)


def test_first_mode_commander_values():
    assert model.first_mode_factor(99, 50, 24) == Fraction(37, 1225)
    assert model.first_mode_factor(99, 50, 25) == Fraction(-1, 98)
    assert model.first_mode_factor(99, 50, 26) == Fraction(-62, 1225)


def test_commander_rows_normalize():
    matrix = model.commander_matrix(25)
    assert all(sum(row, Fraction(0)) == 1 for row in matrix)


def test_commander_stationary_normalizes():
    assert sum(model.commander_stationary(), Fraction(0)) == 1


def test_commander_exact_tv_values():
    assert float(model.commander_tv(25, 1)) == pytest.approx(0.8416153388386696)
    assert model.commander_tv(25, 2) == Fraction(
        12255318415559330995522631403472464258192877,
        4933350368865509640837610315994582805439728012,
    )
    assert model.commander_tv(25, 3) == Fraction(
        172379525755689183991816396516567920780192827919620440221147749,
        6691837923759692633601708022649918108038775216019298375918637677488,
    )


def test_protocol_cost_shape():
    assert model.protocol_cost((2, 3, 1), (25, 25), 1.0, 4.0) == 14.0
    with pytest.raises(ValueError):
        model.protocol_cost((1, 2), (25, 25), 1.0, 1.0)


def test_rising_sequences_small_examples():
    assert model.rising_sequences([1, 2, 3, 4, 5]) == 1
    assert model.rising_sequences([1, 3, 5, 2, 4]) == 2
    assert model.rising_sequences([3, 1, 4, 2, 5]) == 3


def test_gsr_one_riffle_probability_classes():
    n = 5
    assert model.gsr_perm_probability(n, 1, 1) == Fraction(n + 1, 2**n)
    assert model.gsr_perm_probability(n, 1, 2) == Fraction(1, 2**n)
    assert model.gsr_perm_probability(n, 1, 3) == 0


def test_gsr_tv_collapses_exactly_to_rising_statistic():
    for k in range(4, 10):
        assert model.gsr_tv_via_rising(52, k) == model.gsr_tv(52, k)


def test_seven_shuffle_optimal_rising_event():
    threshold, q, u, gap = model.gsr_optimal_rising_event(52, 7)
    assert threshold == 25
    assert float(q) == pytest.approx(0.64999390497)
    assert float(u) == pytest.approx(0.31593290550)
    assert gap == model.gsr_tv(52, 7)


def test_eulerian_row_counts_all_permutations():
    from math import factorial
    for n in range(1, 10):
        assert sum(model.eulerian_row(n)) == factorial(n)


def test_uniform_rising_moments():
    mean, var = model.uniform_rising_moments(52)
    assert mean == Fraction(53, 2)
    assert var == Fraction(53, 12)


def test_gsr_likelihood_ratio_is_monotone_in_rising_runs():
    n = 52
    k = 7
    a = 2**k
    for r in range(1, n):
        ratio = model.gsr_likelihood_step_ratio(n, k, r)
        assert ratio == Fraction(a - r, a + n - r)
        assert 0 < ratio < 1


def test_inverse_riffle_stable_sort_example():
    order = list(range(1, 9))
    bits = [0, 1, 0, 1, 1, 0, 1, 1]
    assert model.stable_sort_cards(order, bits) == [1, 3, 6, 2, 4, 5, 7, 8]


def test_two_inverse_riffles_equal_one_two_bit_address_sort():
    order = list(range(1, 9))
    first_bits = [1, 0, 1, 1, 0, 0, 1, 0]
    second_bits = [0, 1, 0, 1, 1, 0, 0, 1]
    after_first = model.stable_sort_cards(order, first_bits)
    after_second = model.stable_sort_cards(after_first, second_bits)
    addresses = [2 * second_bits[i] + first_bits[i] for i in range(len(order))]
    direct = model.stable_sort_cards(order, addresses)
    assert after_first == [2, 5, 6, 8, 1, 3, 4, 7]
    assert after_second == [6, 1, 3, 7, 2, 5, 8, 4]
    assert after_second == direct
