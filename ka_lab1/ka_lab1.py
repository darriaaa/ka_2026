"""
Лабораторна робота
Тема: Розкладання поліномів на множники методом Кронекера

Приклади:
1) Варіант 12:
   f(x) = -x^5 - x^4 + 12x^3 - 5x^2 - 5x + 60

2) Варіант 27:
   f(x) = 6x^3 + 55x^2 + 129x + 90

- тут покроково реалізовано логіку методу Кронекера;
- усі обчислення виконуються точно, через Fraction, без похибок float.

ІДЕЯ МЕТОДУ КРОНЕКЕРА:
1. Нехай маємо поліном f(x) степеня n.
2. Шукаємо нетривіальний дільник g(x) степеня не вище floor(n / 2).
3. Обираємо точки x = 0, 1, ..., m, де m = floor(n / 2).
4. Обчислюємо f(0), f(1), ..., f(m).
5. Для кожного значення f(i) виписуємо всі його цілі дільники.
6. Перебираємо можливі значення g(0), g(1), ..., g(m),
   причому кожне g(i) повинно бути дільником f(i).
7. За цими значеннями будуємо інтерполяційний поліном g(x).
8. Якщо:
   - степінь g(x) > 0
   - коефіцієнти g(x) цілі
   - f(x) ділиться на g(x) без остачі
   тоді знайдено нетривіальний дільник.
9. Повторюємо процес для знайдених множників, поки не дійдемо до незвідних.

Нижче реалізовано:
- базові операції з поліномами;
- інтерполяція Лагранжа, бо потрібно відновити поліном по точках автоматично;
- перебір дільників;
- перевірка подільності;
- рекурсивний розклад на множники методом Кронекера.
"""

from fractions import Fraction
from itertools import product
from math import gcd
from functools import reduce


# ============================================================
#                   ДОПОМІЖНІ ФУНКЦІЇ
# ============================================================

def trim(poly):
    """
    Видаляє старші нульові коефіцієнти з полінома.

    Поліном зберігаємо як список коефіцієнтів
    від найстаршого степеня до вільного члена.

    Наприклад:
    x^2 + x - 12  -> [1, 1, -12]
    """
    poly = poly[:]
    while len(poly) > 1 and poly[0] == 0:
        poly.pop(0)
    return poly


def degree(poly):
    """
    Повертає степінь полінома.
    """
    poly = trim(poly)
    return len(poly) - 1


def poly_to_fraction(poly):
    "   Перетворює всі коефіцієнти полінома в Fraction, щоб надалі обчислення були точними."
    return [Fraction(c) for c in poly]


def poly_eval(poly, x):
    """
    Обчислює значення полінома в точці x за схемою Горнера.

    poly: список коефіцієнтів від старшого до молодшого
    x: число (int або Fraction)
    """
    result = Fraction(0)
    x = Fraction(x)
    for coef in poly:
        result = result * x + Fraction(coef)
    return result


def poly_add(p, q):
    " Додає два поліноми. "
    p = poly_to_fraction(p)
    q = poly_to_fraction(q)

    # вирівнюємо довжини
    if len(p) < len(q):
        p = [Fraction(0)] * (len(q) - len(p)) + p
    elif len(q) < len(p):
        q = [Fraction(0)] * (len(p) - len(q)) + q

    return trim([a + b for a, b in zip(p, q)])


def poly_sub(p, q):
    """
    Віднімає q від p.
    """
    p = poly_to_fraction(p)
    q = poly_to_fraction(q)

    if len(p) < len(q):
        p = [Fraction(0)] * (len(q) - len(p)) + p
    elif len(q) < len(p):
        q = [Fraction(0)] * (len(p) - len(q)) + q

    return trim([a - b for a, b in zip(p, q)])


def poly_mul(p, q):
    """
    Множить два поліноми.
    """
    p = poly_to_fraction(p)
    q = poly_to_fraction(q)

    res = [Fraction(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            res[i + j] += a * b
    return trim(res)


def poly_scalar_mul(p, k):
    """
    Множення полінома на число.
    """
    k = Fraction(k)
    return trim([Fraction(c) * k for c in poly_to_fraction(p)])


def poly_divmod_exact(dividend, divisor):
    """
    Ділення поліномів "стовпчиком".

    Повертає:(частка, остача)

    Усі коефіцієнти зберігаються як Fraction.
    """
    dividend = trim(poly_to_fraction(dividend))
    divisor = trim(poly_to_fraction(divisor))

    if divisor == [0]:
        raise ZeroDivisionError("Ділення на нульовий поліном неможливе")

    if degree(dividend) < degree(divisor):
        return [Fraction(0)], dividend

    quotient = [Fraction(0)] * (degree(dividend) - degree(divisor) + 1)
    remainder = dividend[:]

    while degree(remainder) >= degree(divisor) and remainder != [0]:
        # старший коефіцієнт частки
        lead_coeff = remainder[0] / divisor[0]
        # різниця степенів
        shift = degree(remainder) - degree(divisor)

        # моном частки: lead_coeff * x^shift
        term = [lead_coeff] + [Fraction(0)] * shift
        quotient[len(quotient) - shift - 1] = lead_coeff

        # ВАЖЛИВО:
        # наш формат від старших до молодших, тому для множення
        # на x^shift додаємо shift нулів справа
        subtract_poly = [c for c in divisor] + [Fraction(0)] * shift

        # домножуємо subtract_poly на lead_coeff
        subtract_poly = poly_scalar_mul(subtract_poly, lead_coeff)

        # Вирівнюємо довжини перед відніманням
        if len(subtract_poly) < len(remainder):
            subtract_poly = [Fraction(0)] * (len(remainder) - len(subtract_poly)) + subtract_poly
        elif len(remainder) < len(subtract_poly):
            remainder = [Fraction(0)] * (len(subtract_poly) - len(remainder)) + remainder

        remainder = trim([a - b for a, b in zip(remainder, subtract_poly)])

    return trim(quotient), trim(remainder)


def divisors_of_integer(n):
    """
    Повертає всі цілі дільники числа n:
    додатні та від'ємні.

    Наприклад:
    divisors_of_integer(6) -> [-6, -3, -2, -1, 1, 2, 3, 6]
    """
    n = abs(int(n))
    if n == 0:
        # Для 0 дільників нескінченно багато, але в нашій задачі
        # окремо оброблятимемо випадок f(i) = 0.
        return [0]

    pos = set()
    for d in range(1, int(n ** 0.5) + 1):
        if n % d == 0:
            pos.add(d)
            pos.add(n // d)

    all_divs = sorted([-d for d in pos] + list(pos))
    return all_divs


def gcd_list(nums):
    """
    НСД для списку чисел
    """
    nums = [abs(int(x)) for x in nums if x != 0]
    if not nums:
        return 0
    return reduce(gcd, nums)


def primitive_part(poly):
    """
    Повертає примітивну частину полінома:
    ділимо всі коефіцієнти на їхній спільний НСД.

    Наприклад:
    [14, -46, -82, 138, 120] -> [7, -23, -41, 69, 60]
    """
    poly = trim(poly)
    g = gcd_list(poly)
    if g in (0, 1):
        return poly[:]
    return [int(c // g) for c in poly]


def all_integer_coeffs(poly):
    """
    Перевіряє, чи всі коефіцієнти полінома є цілими числами.
    """
    for c in poly:
        if Fraction(c).denominator != 1:
            return False
    return True


def fractions_to_ints(poly):
    """
    Якщо всі коефіцієнти цілі, перетворює Fraction -> int.
    """
    if not all_integer_coeffs(poly):
        raise ValueError("Не всі коефіцієнти є цілими")
    return [int(Fraction(c)) for c in poly]


def poly_str(poly):
    """
    Красивий рядок для полінома.
    Степені записуються через ^, як ти й просила.

    Наприклад:
    [1, 1, -12] -> x^2 + x - 12
    """
    poly = trim(poly)
    n = degree(poly)

    if poly == [0]:
        return "0"

    terms = []
    for i, coef in enumerate(poly):
        power = n - i
        if coef == 0:
            continue

        sign = "-" if coef < 0 else "+"
        abs_coef = abs(coef)

        if power == 0:
            body = f"{abs_coef}"
        elif power == 1:
            if abs_coef == 1:
                body = "x"
            else:
                body = f"{abs_coef}x"
        else:
            if abs_coef == 1:
                body = f"x^{power}"
            else:
                body = f"{abs_coef}x^{power}"

        terms.append((sign, body))

    first_sign, first_body = terms[0]
    result = first_body if first_sign == "+" else f"-{first_body}"

    for sign, body in terms[1:]:
        result += f" {sign} {body}"

    return result


# ============================================================
#            ІНТЕРПОЛЯЦІЯ ЛАГРАНЖА ДЛЯ ПОБУДОВИ g(x)
# ============================================================

def lagrange_interpolation(points):
    """
    Будує інтерполяційний поліном за точками методом Лагранжа.

    points: список пар (x_i, y_i)

    Повертає поліном у вигляді списку Fraction-коефіцієнтів.

    Формула:
    g(x) = Σ y_i * L_i(x)

    де
    L_i(x) = Π (x - x_j)/(x_i - x_j), j != i
    """
    result = [Fraction(0)]

    for i, (xi, yi) in enumerate(points):
        # Починаємо з 1
        Li = [Fraction(1)]
        denom = Fraction(1)

        for j, (xj, yj) in enumerate(points):
            if i == j:
                continue

            # Множимо на (x - xj)
            Li = poly_mul(Li, [Fraction(1), Fraction(-xj)])
            denom *= Fraction(xi - xj)

        Li = poly_scalar_mul(Li, Fraction(yi, 1) / denom)
        result = poly_add(result, Li)

    return trim(result)


# ============================================================
#         ПОШУК НЕТРИВІАЛЬНОГО ДІЛЬНИКА ЗА КРОНЕКЕРОМ
# ============================================================

def try_find_factor_kronecker(poly, verbose=True):
    """
    Пробує знайти НЕТРИВІАЛЬНИЙ дільник полінома методом Кронекера.

    Якщо дільник знайдено:
        повертає (factor, quotient)

    Якщо не знайдено:
        повертає (None, None)

    verbose=True -> друкує детальний хід розв'язання.
    """
    poly = trim(poly)
    n = degree(poly)

    # Поліноми степеня 0 або 1 далі вже не розкладаємо цим методом
    if n <= 1:
        return None, None

    # Беремо примітивну частину
    ppoly = primitive_part(poly)

    # Максимальний степінь шуканого нетривіального дільника
    m = n // 2

    if verbose:
        print("=" * 80)
        print(f"Розглядаємо поліном: f(x) = {poly_str(ppoly)}")
        print(f"Степінь n = {n}")
        print(f"Максимальний степінь нетривіального дільника m = floor(n / 2) = {m}")
        print()

    # Точки x = 0, 1, ..., m
    xs = list(range(m + 1))
    values = [poly_eval(ppoly, x) for x in xs]

    if verbose:
        print("1) Обчислюємо значення полінома в точках x = 0..m:")
        for x, val in zip(xs, values):
            print(f"   f({x}) = {val}")
        print()

    # Якщо в якійсь точці значення 0, то маємо лінійний множник x - a
    # Це теж законний крок у межах логіки методу Кронекера.
    for x, val in zip(xs, values):
        if val == 0:
            factor = [1, -x]   # x - a
            q, r = poly_divmod_exact(ppoly, factor)
            if r == [0]:
                factor = fractions_to_ints(factor)
                q = fractions_to_ints(q)
                if verbose:
                    print(f"2) Знайдено корінь x = {x}, отже лінійний дільник: {poly_str(factor)}")
                    print(f"   Частка: {poly_str(q)}")
                return factor, q

    # Для кожного f(i) виписуємо множину дільників
    divisor_sets = []
    if verbose:
        print("2) Будуємо множини дільників U_i:")
    for x, val in zip(xs, values):
        # тут val має бути цілим
        if val.denominator != 1:
            raise ValueError("Очікувалося ціле значення полінома в цілій точці")
        Ui = divisors_of_integer(int(val))
        divisor_sets.append(Ui)
        if verbose:
            print(f"   U_{x} (дільники f({x}) = {int(val)}): {Ui}")
    if verbose:
        print()

    # Перебираємо всі комбінації g(0), g(1), ..., g(m)
    if verbose:
        counts = [len(Ui) for Ui in divisor_sets]
        total = 1
        for c in counts:
            total *= c
        print(f"3) Починаємо перебір декартового добутку U_0 x U_1 x ... x U_{m}")
        print(f"   Загальна кількість комбінацій: {total}")
        print()

    step = 0
    for combo in product(*divisor_sets):
        step += 1

        # Будуємо інтерполяційний поліном g(x),
        # який проходить через точки (0, combo[0]), (1, combo[1]), ..., (m, combo[m])
        points = list(zip(xs, combo))
        g_poly = lagrange_interpolation(points)

        # Нас цікавлять тільки поліноми з цілими коефіцієнтами
        if not all_integer_coeffs(g_poly):
            continue

        g_poly_int = fractions_to_ints(g_poly)
        g_poly_int = trim(g_poly_int)

        # Відкидаємо константи та "асоційовані" дільники ±1
        if degree(g_poly_int) <= 0:
            continue

        # Перевіряємо подільність
        quotient, remainder = poly_divmod_exact(ppoly, g_poly_int)

        if remainder == [0] and all_integer_coeffs(quotient):
            quotient_int = fractions_to_ints(quotient)

            if verbose:
                print(f"4) На кроці {step} знайдено дільник:")
                print(f"   Обрані значення g(i): {combo}")
                print(f"   g(x) = {poly_str(g_poly_int)}")
                print(f"   Частка q(x) = {poly_str(quotient_int)}")
                print()

            return g_poly_int, quotient_int

    if verbose:
        print("4) Нетривіальний дільник не знайдено. Поліном вважаємо незвідним над Z[x].")
        print()

    return None, None


# ============================================================
#          РЕКУРСИВНИЙ РОЗКЛАД ПОЛІНОМА НА МНОЖНИКИ
# ============================================================

def factor_kronecker(poly, verbose=True, level=0):
    """
    Рекурсивно розкладає поліном на множники методом Кронекера.

    Повертає список множників.
    """
    poly = trim(poly)

    indent = "    " * level

    if verbose:
        print(indent + "-" * 80)
        print(indent + f"Поточний поліном: {poly_str(poly)}")

    # Константа або лінійний поліном — далі не розкладаємо
    if degree(poly) <= 1:
        if verbose:
            print(indent + "Поліном степеня <= 1, вважаємо його незвідним на цьому етапі.")
            print()
        return [poly]

    factor, quotient = try_find_factor_kronecker(poly, verbose=verbose)

    if factor is None:
        # Поліном не розклався далі
        return [poly]

    # Рекурсивно розкладаємо factor та quotient
    left = factor_kronecker(factor, verbose=verbose, level=level + 1)
    right = factor_kronecker(quotient, verbose=verbose, level=level + 1)
    return left + right


def multiply_factors(factors):
    """
    Перемножує список множників назад,
    щоб перевірити правильність розкладу.
    """
    result = [1]
    for f in factors:
        result = fractions_to_ints(poly_mul(result, f))
    return trim(result)


# ============================================================
#       ДОДАТКОВА ФУНКЦІЯ ДЛЯ КРАСИВОГО ВИВЕДЕННЯ ВІДПОВІДІ
# ============================================================

def format_factorization(poly, factors):
    """
    Формує красивий запис розкладу:
    f(x) = ( ... )( ... )( ... )
    """
    left = poly_str(poly)
    right = " * ".join(f"({poly_str(f)})" for f in factors)
    return f"{left} = {right}"


# ============================================================
#                     ЗАДАЧА 1: ВАРІАНТ 12
# ============================================================

variant_12 = [-1, -1, 12, -5, -5, 60]
# Це означає:
# -x^5 - x^4 + 12x^3 - 5x^2 - 5x + 60

print("\n" + "#" * 100)
print("ВАРІАНТ 12")
print("#" * 100)
print(f"Початковий поліном: {poly_str(variant_12)}")
print()

factors_12 = factor_kronecker(variant_12, verbose=True)

print("ПІДСУМКОВІ МНОЖНИКИ ДЛЯ ВАРІАНТА 12:")
for i, f in enumerate(factors_12, start=1):
    print(f"  Множник {i}: {poly_str(f)}")

print()
print("Перевірка перемноження множників:")
restored_12 = multiply_factors(factors_12)
print(f"  Отримали: {poly_str(restored_12)}")

print()
print("Фінальний запис:")
print(" ", format_factorization(variant_12, factors_12))


# ============================================================
#                     ЗАДАЧА 2: ВАРІАНТ 27
# ============================================================

variant_27 = [6, 55, 129, 90]
# Це означає:
# 6x^3 + 55x^2 + 129x + 90

print("\n" + "#" * 100)
print("ВАРІАНТ 27")
print("#" * 100)
print(f"Початковий поліном: {poly_str(variant_27)}")
print()

factors_27 = factor_kronecker(variant_27, verbose=True)

print("ПІДСУМКОВІ МНОЖНИКИ ДЛЯ ВАРІАНТА 27:")
for i, f in enumerate(factors_27, start=1):
    print(f"  Множник {i}: {poly_str(f)}")

print()
print("Перевірка перемноження множників:")
restored_27 = multiply_factors(factors_27)
print(f"  Отримали: {poly_str(restored_27)}")

print()
print("Фінальний запис:")
print(" ", format_factorization(variant_27, factors_27))


# ============================================================
#               ОЧІКУВАНІ РЕЗУЛЬТАТИ ДЛЯ ТВОЇХ ВАРІАНТІВ
# ============================================================

"""
Для варіанта 12 очікуваний правильний розклад:
-x^5 - x^4 + 12x^3 - 5x^2 - 5x + 60 = -(x + 4)(x - 3)(x^3 + 5)

У коді це може вийти, наприклад, у вигляді:
(-x^3 - 5), (x^2 + x - 12)
або ще далі:
(-1), (x + 4), (x - 3), (x^3 + 5)
або з іншим порядком множників.
Це нормально, бо порядок множників не впливає на відповідь.

Для варіанта 27 очікуваний правильний розклад:
6x^3 + 55x^2 + 129x + 90 = (x + 6)(3x + 5)(2x + 3)

Знову ж таки, порядок множників може бути іншим.
"""
