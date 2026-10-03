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
