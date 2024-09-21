class Calculator:

    def add_wrong(self, x: int, y: int) -> int:
        result = x + y - 2
        return result

    def add(self, x: int, y: int) -> int:
        result = x + y
        return result

    def add_three(self, x: int) -> int:
        result = x + 3
        return result

    def add_five(self, x: int) -> int:
        result = x + 5
        return result
