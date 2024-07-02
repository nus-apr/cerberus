import calculator


def test_1() -> None:
    assert calculator.Calculator().add_wrong(x=8, y=5) == 13
