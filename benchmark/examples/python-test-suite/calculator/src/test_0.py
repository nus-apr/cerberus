import calculator


def test_0() -> None:
    assert calculator.Calculator().add_wrong(x=5, y=5) == 10
