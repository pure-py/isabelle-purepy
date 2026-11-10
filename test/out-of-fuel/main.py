# Fuel is implementation-specific
def even(n: int) -> bool:
    if n == 0:
        return True
    return odd(n - 1)


def odd(n: int) -> bool:
    if n == 0:
        return False
    return even(n - 1)


print(even(100))
