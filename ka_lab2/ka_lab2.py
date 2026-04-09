# ============================================================
# ЛАБОРАТОРНА РОБОТА №2
# ТЕМА: Базис Гребнера
# ВАРІАНТ 2
#
# Система поліномів:
#   f1 = x^2 + y^2 + z^2
#   f2 = x + y - z
#   f3 = y + z^2
#
# У ЦЬОМУ КОДІ РЕАЛІЗОВАНО:
# 1) ручний алгоритм Бухбергера;
# 2) побудову базису Гребнера;
# 3) побудову мінімального базису Гребнера;
# 4) побудову редукованого базису Гребнера.
#
# ВАЖЛИВО:
# - тут НЕ використовується sympy.groebner() для основного розв'язку;
# - основний алгоритм написаний вручну;
# - sympy тут використовується лише як інструмент для роботи з поліномами:
#   Poly, розкриття дужок, впорядкування мономів тощо.
#
# ПОРЯДОК МОНОМІВ:
#   lex
# ПОРЯДОК ЗМІННИХ:
#   x > y > z
# ============================================================

from itertools import combinations
from sympy import symbols, Poly, expand, simplify


# ------------------------------------------------------------
# 1. ОГОЛОШУЄМО ЗМІННІ
# ------------------------------------------------------------
x, y, z = symbols("x y z")


# ------------------------------------------------------------
# 2. ЗАДАЄМО ПОЛІНОМИ ВАРІАНТА 2
# ------------------------------------------------------------
f1 = x**2 + y**2 + z**2
f2 = x + y - z
f3 = y + z**2

# Початкова множина поліномів
F = [f1, f2, f3]


# ------------------------------------------------------------
# 3. ДОПОМІЖНІ ФУНКЦІЇ ДЛЯ РОБОТИ З ПОЛІНОМАМИ
# ------------------------------------------------------------
def to_poly(expr):
    """
    Перетворює вираз SymPy у Poly.

    Це потрібно для того, щоб мати доступ до:
    - провідного монома
    - провідного коефіцієнта
    - списку мономів
    - степенів змінних

    domain='QQ' означає, що працюємо над полем раціональних чисел.
    """
    return Poly(expand(expr), x, y, z, domain="QQ")


def normalize(expr):
    """
    Нормалізує поліном:
    - розкриває дужки;
    - скорочує подібні доданки;
    - ділить на провідний коефіцієнт, щоб старший коефіцієнт став 1.

    Це зручно:
    - при додаванні нового полінома в базис;
    - при побудові мінімального/редукованого базису.
    """
    p = to_poly(expr)

    # Якщо поліном нульовий, просто повертаємо 0
    if p.is_zero:
        return 0

    lc = p.LC(order="lex")
    return expand(p.as_expr() / lc)


def poly_str(expr):
    """
    Просто красивий вивід полінома.
    """
    return str(expand(expr))


def lm(poly_expr):
    """
    Повертає провідний моном полінома у вигляді кортежу степенів.
    Наприклад:
        x^2*y*z^3 -> (2, 1, 3)
    """
    p = to_poly(poly_expr)
    return p.LM(order="lex").exponents


def lc(poly_expr):
    """
    Повертає провідний коефіцієнт полінома.
    """
    p = to_poly(poly_expr)
    return p.LC(order="lex")


def lt_expr(poly_expr):
    """
    Повертає провідний член полінома у вигляді виразу.
    Наприклад:
        для 3*x^2*y + ...
        поверне 3*x^2*y
    """
    p = to_poly(poly_expr)

    if p.is_zero:
        return 0

    coeff = p.LC(order="lex")
    exps = p.LM(order="lex").exponents

    return coeff * x**exps[0] * y**exps[1] * z**exps[2]


def monomial_expr(exps):
    """
    Перетворює кортеж степенів у моном.
    Наприклад:
        (2, 1, 0) -> x^2*y
    """
    return x**exps[0] * y**exps[1] * z**exps[2]


def monomial_divides(a, b):
    """
    Перевіряє, чи моном a ділить моном b.

    Наприклад:
        a = x*y   -> (1,1,0)
        b = x^2*y*z -> (2,1,1)

        a | b  -> True

    У термінах степенів:
        a ділить b, якщо кожна степінь у a <= відповідної степені у b
    """
    return all(ai <= bi for ai, bi in zip(a, b))


def monomial_quotient(a, b):
    """
    Обчислює частку b / a для двох мономів у вигляді кортежів степенів,
    якщо a ділить b.

    Наприклад:
        a = (1,1,0)   # x*y
        b = (2,1,1)   # x^2*y*z
        b/a = (1,0,1) # x*z
    """
    return tuple(bi - ai for ai, bi in zip(a, b))


def monomial_lcm(a, b):
    """
    НСК двох мономів у вигляді кортежу степенів.

    Наприклад:
        x^2*y   -> (2,1,0)
        x*z^3   -> (1,0,3)

        LCM = x^2*y*z^3 -> (2,1,3)
    """
    return tuple(max(ai, bi) for ai, bi in zip(a, b))


# ------------------------------------------------------------
# 4. ОБЧИСЛЕННЯ S-ПОЛІНОМА
# ------------------------------------------------------------
def s_polynomial(f, g):
    """
    Обчислює S-поліном для двох поліномів f і g.

    Формула:
        S(f, g) = (LCM(LM(f), LM(g)) / LT(f)) * f
                - (LCM(LM(f), LM(g)) / LT(g)) * g

    Де:
    - LM = leading monomial (провідний моном)
    - LT = leading term (провідний член, включає коефіцієнт)

    Ми будуємо множники вручну:
    1. знаходимо НСК провідних мономів;
    2. ділимо його на провідний моном кожного полінома;
    3. коригуємо на провідні коефіцієнти.
    """
    f = normalize(f)
    g = normalize(g)

    lm_f = lm(f)
    lm_g = lm(g)
    lc_f = lc(f)
    lc_g = lc(g)

    lcm_m = monomial_lcm(lm_f, lm_g)

    # Мономи-множники
    qf = monomial_expr(monomial_quotient(lm_f, lcm_m))
    qg = monomial_expr(monomial_quotient(lm_g, lcm_m))

    # Через те, що LT містить ще й коефіцієнт,
    # треба ділити також на старший коефіцієнт
    S = expand((qf / lc_f) * f - (qg / lc_g) * g)

    return expand(S)


# ------------------------------------------------------------
# 5. РУЧНЕ ДІЛЕННЯ ПОЛІНОМА НА МНОЖИНУ ПОЛІНОМІВ
# ------------------------------------------------------------
def multivariate_division(f, divisors, verbose=False):
    """
    Ручне багаточленне ділення полінома f на множину divisors.

    Це саме той алгоритм, який використовується в теорії базисів Гребнера:
    на кожному кроці:
    - беремо провідний член поточного полінома p;
    - шукаємо перший дільник g_i, чий LM(g_i) ділить LM(p);
    - якщо такий є, віднімаємо відповідний множник * g_i;
    - якщо такого немає, провідний член переносимо в остачу.

    Повертає:
    - список часток q_i;
    - остачу r.
    """
    p = expand(f)             # поточний поліном, який ще треба ділити
    r = 0                     # остача
    qs = [0] * len(divisors)  # список часток для кожного дільника

    if verbose:
        print("    Починаємо ділення полінома:")
        print(f"    p = {expand(p)}")
        print()

    while p != 0:
        p = expand(p)
        p_poly = to_poly(p)

        # Провідний моном і провідний коефіцієнт поточного p
        lm_p = p_poly.LM(order="lex").exponents
        lc_p = p_poly.LC(order="lex")

        divided = False

        # Поступово пробуємо ділити провідний член p
        # на провідний моном кожного дільника
        for i, g in enumerate(divisors):
            g = expand(g)
            g_poly = to_poly(g)

            if g_poly.is_zero:
                continue

            lm_g = g_poly.LM(order="lex").exponents
            lc_g = g_poly.LC(order="lex")

            # Якщо LM(g) ділить LM(p), можна виконати редукцію
            if monomial_divides(lm_g, lm_p):
                # Обчислюємо моном частки
                q_exp = monomial_quotient(lm_g, lm_p)
                q_mon = monomial_expr(q_exp)

                # Коефіцієнт частки
                q_coeff = lc_p / lc_g

                # Отримуємо терм, на який треба домножити g
                t = expand(q_coeff * q_mon)

                # Додаємо t у відповідну частку
                qs[i] = expand(qs[i] + t)

                # Віднімаємо t*g від p
                old_p = p
                p = expand(p - t * g)

                if verbose:
                    print(f"    Провідний член p ділиться на LT(g{i+1})")
                    print(f"    Беремо множник t = {t}")
                    print(f"    Віднімаємо t * g{i+1} = {expand(t*g)}")
                    print(f"    Було p = {expand(old_p)}")
                    print(f"    Стало p = {expand(p)}")
                    print()

                divided = True
                break

        # Якщо жоден провідний моном дільників не поділив LM(p),
        # то провідний член p переходить в остачу
        if not divided:
            lt_p = lt_expr(p)
            old_p = p
            r = expand(r + lt_p)
            p = expand(p - lt_p)

            if verbose:
                print("    Жоден провідний моном дільників не поділив LT(p)")
                print(f"    Переносимо в остачу LT(p) = {lt_p}")
                print(f"    Було p = {expand(old_p)}")
                print(f"    Стало p = {expand(p)}")
                print(f"    Поточна остача r = {expand(r)}")
                print()

    return qs, expand(r)


# ------------------------------------------------------------
# 6. РУЧНИЙ АЛГОРИТМ БУХБЕРГЕРА
# ------------------------------------------------------------
def buchberger_manual(initial_basis, verbose=True):
    """
    Ручна реалізація алгоритму Бухбергера.

    Алгоритм:
    1. Беремо початкову множину G = F
    2. Формуємо всі пари поліномів
    3. Для кожної пари:
       - обчислюємо S-поліном;
       - ділимо його на поточний базис G;
       - якщо остача != 0, додаємо її в G;
       - після цього створюємо нові пари з новим поліномом.
    4. Коли всі пари оброблені — отримали базис Гребнера.
    """
    # Нормалізуємо початкові поліноми
    G = [normalize(f) for f in initial_basis]

    # Початковий список пар індексів
    pairs = list(combinations(range(len(G)), 2))

    step = 1

    if verbose:
        print("=" * 80)
        print("ПОЧАТОК АЛГОРИТМУ БУХБЕРГЕРА")
        print("=" * 80)
        print("Початкова множина G:")
        for i, g in enumerate(G, start=1):
            print(f"g{i} = {poly_str(g)}")
        print()

    while pairs:
        i, j = pairs.pop(0)

        f = G[i]
        g = G[j]

        if verbose:
            print(f"Крок {step}. Беремо пару (g{i+1}, g{j+1})")
            print(f"f = {poly_str(f)}")
            print(f"g = {poly_str(g)}")
            print()

        # 1) будуємо S-поліном
        S = s_polynomial(f, g)

        if verbose:
            print("  S-поліном:")
            print(f"  S(f, g) = {poly_str(S)}")
            print()

        # 2) ділимо S на поточний базис G
        if verbose:
            print("  Ділимо S-поліном на поточну множину G:")
        qs, remainder = multivariate_division(S, G, verbose=verbose)

        remainder = normalize(remainder)

        if verbose:
            print(f"  Остача h = {poly_str(remainder)}")
            print()

        # 3) якщо остача не нульова — додаємо новий поліном
        if remainder != 0:
            # Перевіряємо, чи такого полінома ще немає
            exists = any(expand(remainder - old) == 0 for old in G)

            if not exists:
                G.append(remainder)
                new_index = len(G) - 1

                # Додаємо всі нові пари з цим поліномом
                for k in range(new_index):
                    pairs.append((k, new_index))

                if verbose:
                    print("  Оскільки h ≠ 0, додаємо його до базису.")
                    print(f"  Новий поліном: g{new_index+1} = {poly_str(remainder)}")
                    print()
            else:
                if verbose:
                    print("  Остача ненульова, але такий поліном уже є в G.")
                    print()

        else:
            if verbose:
                print("  Оскільки h = 0, множина G не змінюється.")
                print()

        if verbose:
            print("  Поточна система поліномів G:")
            for idx, poly in enumerate(G, start=1):
                print(f"  g{idx} = {poly_str(poly)}")
            print("-" * 80)
            print()

        step += 1

    if verbose:
        print("=" * 80)
        print("АЛГОРИТМ БУХБЕРГЕРА ЗАВЕРШЕНО")
        print("=" * 80)
        print("Отриманий базис Гребнера:")
        for i, g in enumerate(G, start=1):
            print(f"g{i} = {poly_str(g)}")
        print()

    return G


# ------------------------------------------------------------
# 7. МІНІМАЛЬНИЙ БАЗИС ГРЕБНЕРА
# ------------------------------------------------------------
def minimal_groebner_basis(G, verbose=True):
    """
    Будує мінімальний базис Гребнера.

    Ідея:
    - спочатку нормалізуємо всі поліноми;
    - прибираємо дублікати;
    - прибираємо ті поліноми, чий провідний моном
      ділиться на провідний моном іншого полінома.
    """
    basis = [normalize(g) for g in G]

    # Прибираємо точні дублікати
    unique_basis = []
    for g in basis:
        if not any(expand(g - h) == 0 for h in unique_basis):
            unique_basis.append(g)

    result = []

    if verbose:
        print("=" * 80)
        print("ПОБУДОВА МІНІМАЛЬНОГО БАЗИСУ ГРЕБНЕРА")
        print("=" * 80)

    for i, g in enumerate(unique_basis):
        lm_g = lm(g)
        removable = False

        for j, h in enumerate(unique_basis):
            if i == j:
                continue

            lm_h = lm(h)

            # Якщо LM(h) ділить LM(g), то g можна викинути,
            # якщо мономи не однакові
            if monomial_divides(lm_h, lm_g) and lm_h != lm_g:
                removable = True

                if verbose:
                    print(f"Поліном {poly_str(g)} можна виключити,")
                    print(f"бо його LM = {lm_g} ділиться на LM іншого полінома = {lm_h}")
                    print()

                break

        if not removable:
            result.append(g)

            if verbose:
                print(f"Поліном {poly_str(g)} залишаємо.")
                print()

    if verbose:
        print("Мінімальний базис:")
        for i, g in enumerate(result, start=1):
            print(f"m{i} = {poly_str(g)}")
        print()

    return result


# ------------------------------------------------------------
# 8. РЕДУКОВАНИЙ БАЗИС ГРЕБНЕРА
# ------------------------------------------------------------
def reduced_groebner_basis(G_min, verbose=True):
    """
    Будує редукований базис Гребнера.

    Для кожного полінома g_i:
    - ділимо g_i на множину G_min \\ {g_i}
    - беремо остачу
    - нормалізуємо остачу

    Отримана множина і буде редукованим базисом.
    """
    reduced = []

    if verbose:
        print("=" * 80)
        print("ПОБУДОВА РЕДУКОВАНОГО БАЗИСУ ГРЕБНЕРА")
        print("=" * 80)

    for i, g in enumerate(G_min):
        others = [G_min[j] for j in range(len(G_min)) if j != i]

        if verbose:
            print(f"Беремо поліном g{i+1} = {poly_str(g)}")
            print("Ділимо його на всі інші поліноми мінімального базису:")
            for j, h in enumerate(others, start=1):
                print(f"  h{j} = {poly_str(h)}")
            print()

        _, rem = multivariate_division(g, others, verbose=verbose)
        rem = normalize(rem)

        reduced.append(rem)

        if verbose:
            print(f"Залишок: {poly_str(rem)}")
            print("-" * 80)
            print()

    # прибираємо дублікати, якщо вони виникли
    unique_reduced = []
    for g in reduced:
        if not any(expand(g - h) == 0 for h in unique_reduced):
            unique_reduced.append(g)

    if verbose:
        print("Редукований базис:")
        for i, g in enumerate(unique_reduced, start=1):
            print(f"r{i} = {poly_str(g)}")
        print()

    return unique_reduced


# ------------------------------------------------------------
# 9. ОСНОВНА ЧАСТИНА ПРОГРАМИ
# ------------------------------------------------------------
if __name__ == "__main__":
    print("ВИХІДНА СИСТЕМА ПОЛІНОМІВ:")
    print(f"f1 = {poly_str(f1)}")
    print(f"f2 = {poly_str(f2)}")
    print(f"f3 = {poly_str(f3)}")
    print()

    # 1. Базис Гребнера за ручним алгоритмом Бухбергера
    G = buchberger_manual(F, verbose=True)

    # 2. Мінімальний базис Гребнера
    G_min = minimal_groebner_basis(G, verbose=True)

    # 3. Редукований базис Гребнера
    G_red = reduced_groebner_basis(G_min, verbose=True)

    print("=" * 80)
    print("ФІНАЛЬНА ВІДПОВІДЬ")
    print("=" * 80)

    print("Базис Гребнера:")
    for g in G:
        print(" ", poly_str(g))

    print("\nМінімальний базис Гребнера:")
    for g in G_min:
        print(" ", poly_str(g))

    print("\nРедукований базис Гребнера:")
    for g in G_red:
        print(" ", poly_str(g))