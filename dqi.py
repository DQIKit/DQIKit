import random
import math
import cmath
from typing import Callable

import numpy as np
from sage.all import Matrix, GF, codes, vector, codes
from sage import coding
from sage.rings.finite_rings.element_base import FiniteRingElement

from decoders import BenchmarkResult, AbstractDecoder


class Dqi:
    def __init__(self, instance, decoder_constructor=None):
        self.instance = instance.to_max_linsat()
        if decoder_constructor is None:
            self.decoder_constructor = self.instance.default_decoder_constructor
        else:
            self.decoder_constructor = decoder_constructor
        self.decoder = None
        self.g = None
        self.g_tilde = None

    def get_decoder(self) -> AbstractDecoder:
        if self.decoder is None:
            self.decoder = self.decoder_constructor(self.instance)
        return self.decoder

    def estimate_solution_quality(
        self,
        l: int | None = None,
        rhs_approximation=True,
        n_decoding_samples=500,
        n_interference_samples=10000,
        w: np.ndarray | None = None,
    ):
        decoder = self.get_decoder()
        radius = decoder.decoding_radius()
        if l is None:
            l = radius

        if l is None:
            raise ValueError(
                "l parameter needs to specified manually since decoder has no explicit decoding radius"
            )

        is_binary = self.instance.field.order() == 2

        if (
            radius is not None
            and l <= radius
            and self._check_semicircle_law_requirements()
        ):
            return self.semicircle_law_solution_quality()
        elif is_binary:
            if rhs_approximation:
                return self._dqi_lower_bound_average_v(
                    l, w=w, n_tries=n_decoding_samples
                )
            else:
                return self._dqi_estimate_performance_binary(
                    l,
                    w=w,
                    n_benchmark_tries=n_decoding_samples,
                    n_error_combination_tries=n_interference_samples,
                )
        else:
            return self._dqi_compute_exact_performance_non_binary(l, w=w)

    def _check_semicircle_law_requirements(self):
        B = self.instance.get_B()
        n = B.ncols()
        m = B.nrows()
        d = self.instance.get_minimum_distance()

        if m <= n:
            return False

        if d <= 3:
            return False

        return True

    def semicircle_law_solution_quality(self):
        B = self.instance.get_B()
        n = B.ncols()
        m = B.nrows()

        if m <= n:
            raise ValueError("Requirement m > n for semicircle law not met")

        r = self.instance.get_r()
        d = self.instance.get_minimum_distance()
        p = self.instance.field.order()

        if d <= 3:
            raise ValueError(
                "Requirement minimum distance >= 4 for semicircle law not met"
            )
        if d % 2 == 0:
            l = d / 2 - 1
        else:
            l = (d - 1) / 2

        return _predict_dqi_performance_perfect_optimal_w(p, r, m, l)

    def _dqi_lower_bound_average_v(
        self, l: int, w: np.ndarray | None = None, n_tries=500
    ):
        assert self.instance.field == GF(2) and self.instance.get_r() == 1

        decoder = self.get_decoder()
        # decoding with zero errors always succeeds
        # Starting a large errors is avanteagous for some decoders
        epsilon = [0.0] + [
            decoder.get_benchmarks(l, k, n_tries).epsilon
            for k in reversed(range(1, l + 1))
        ]

        B = self.instance.get_B()
        m = B.nrows()

        return _upper_bound_dqi_performance_imperfect_average_v(m, l, epsilon, w)

    def _dqi_estimate_performance_binary(
        self,
        l: int,
        w: np.ndarray | None = None,
        n_benchmark_tries: int | None = 500,
        n_error_combination_tries: int = 10000,
    ):
        assert self.instance.field == GF(2) and self.instance.get_r() == 1

        minimum_distance = self.instance.get_minimum_distance()
        decoder = self.get_decoder()

        B = self.instance.get_B()
        m = B.nrows()

        v = self.instance.get_v()

        benchmarks = {0: BenchmarkResult([vector(GF(2), [0] * B.nrows())], [], 0)}
        epsilons = [0] * (l + 1)
        # Starting a large errors is avanteagous for some decoders
        for k in ggreversed(range(1, l + 1)):
            benchmarks[k] = decoder.get_benchmarks(l, k, n_tries=n_benchmark_tries)

        for k, b in benchmarks.items():
            epsilons[k] = b.epsilon

        A_bar = approximate_A_bar(
            B, v, l, benchmarks, minimum_distance, n_error_combination_tries
        )
        return _predict_dqi_performance_imperfect_binary(A_bar, m, l, w, epsilons)

    def _dqi_compute_exact_performance_non_binary(
        self,
        l: int,
        w: np.ndarray | None = None,
    ):
        if not self.instance.field.is_prime_field():
            raise ValueError("This function only supports prime fields")

        decoder = self.get_decoder()

        B = self.instance.get_B()
        B_T = B.T
        F = self.instance.get_F()
        m = self.instance.get_m()
        r = self.instance.get_r()
        field = self.instance.field
        p = field.order()

        g_tilde = self._get_g_tilde()

        def total_g_tilde(y):
            product = 1
            for i, y_i in enumerate(y):
                if y_i != 0:
                    product *= g_tilde[i](int(y_i))
            return product

        benchmarks = {
            0: BenchmarkResult([vector(self.instance.field, [0] * B.nrows())], [], 0)
        }
        epsilons = [0] * (l + 1)
        # Starting a large errors is avanteagous for some decoders
        for k in reversed(range(1, l + 1)):
            benchmarks[k] = decoder.get_benchmarks(l, k, n_tries=None)

        A = make_A(p, r, m, l)
        if w is None:
            _, w = get_eigenvector(A, -1)
            w = w / np.linalg.norm(w)

        # compute norm
        norm = 0
        for k in range(l):
            term = 0
            for y in benchmarks[k].correct:
                product = 1
                for i, y_i in enumerate(y):
                    if y_i != 0:
                        product *= abs(g_tilde[i](int(y_i)))
                term += product
            norm += w[k] ** 2 / math.comb(m, k) * term

        e = [vector(field, [0] * m) for _ in range(m)]
        for i in range(m):
            e[i][i] = 1

        omega_p = cmath.exp(2j * math.pi / p)

        expectation = 0
        for k1 in range(l):
            for k2 in range(l):
                factor = w[k1] * w[k2] / math.sqrt(math.comb(m, k1) * math.comb(m, k2))
                term = 0
                for y1 in benchmarks[k1].correct:
                    for y2 in benchmarks[k2].correct:
                        subfactor = total_g_tilde(y1).conjugate() * total_g_tilde(y2)
                        subterm = 0
                        for i in range(m):
                            for a in field:
                                if B_T * y1 != B_T * (y2 - a * e[i]):
                                    continue
                                for v in F[i]:
                                    subterm += omega_p ** (-int(a) * int(v))
                        term += subfactor * subterm
                expectation += factor * term

        result = expectation / p / norm
        return float(result.real)

    def _compute_g_g_tilde(self):
        if not self.instance.field.is_prime_field():
            raise ValueError("This function only supports prime fields")
        p = self.instance.field.order()
        r = self.instance.get_r()
        f_dash = 2 * r / p - 1
        phi = math.sqrt(4 * r * (1 - r / p))

        yes_value = (+1 - f_dash) / phi
        no_value = (-1 - f_dash) / phi

        self.g = [
            lambda y: yes_value if y in F_i else no_value
            for F_i in self.instance.get_F()
        ]

        omega_p = cmath.exp(2j * math.pi / p)

        self.g_tilde = [
            (
                lambda y: 1
                / math.sqrt(p)
                * sum((omega_p ** (y * x)) * g_i(x) for x in range(p))
            )
            for g_i in self.g
        ]

    def _get_g_tilde(self) -> list[Callable[[FiniteRingElement], complex]]:
        if self.g is None:
            self._compute_g_g_tilde()
        return list(self.g_tilde)


def get_eigenvector(mat: np.ndarray, index: int) -> np.ndarray:
    values, vectors = np.linalg.eigh(mat)
    value = values[index]
    vector = vectors[:, index]
    return value, vector


def make_A(p: int, r: int, m: int, l: int) -> np.array:
    diag = (p - 2 * r) / p * np.diag(np.arange(0, l + 1))

    k = np.arange(0, l + 1)
    a_k = np.sqrt(k * (m - k + 1))

    off_diag = np.diag(a_k)
    return diag + np.roll(off_diag, -1, 0) + np.roll(off_diag, -1, 1)


def _predict_dqi_performance_perfect(p: int, r: int, m: int, l: int, w: int) -> float:
    A = make_A(p, r, m, l)

    assert len(w) == l + 1
    norm = np.linalg.norm(w)

    polynomial_effect = (
        w.reshape((1, l + 1)) @ A @ w.reshape((l + 1, 1)) / (norm * norm)
    )

    return ((m * r) / p + np.sqrt(r * (p - r)) / p * polynomial_effect).item()


def _predict_dqi_performance_perfect_optimal_w(p: int, r: int, m: int, l: int) -> float:
    A = make_A(p, r, m, l)

    lambda_1 = np.linalg.eigh(A)[0][-1]
    return (m * r) / p + np.sqrt(r * (p - r)) / p * lambda_1


def _upper_bound_dqi_performance_imperfect_average_v(
    m: int, l: int, epsilon: float, w: np.ndarray = None
) -> float:
    if isinstance(epsilon, float) or isinstance(epsilon, int):
        epsilon = [float(epsilon)] * (l + 1)

    assert len(epsilon) == l + 1
    assert min(epsilon) >= 0
    assert w is None or len(w) == l + 1

    A = make_A(2, 1, m, l)

    if w is None:
        lambda_1, w = get_eigenvector(A, -1)
        matrix_product = lambda_1
    else:
        w = np.array(w)
        matrix_product = w.reshape((1, l + 1)) @ A @ w.reshape((l + 1, 1))

    largest_epsilon = max(epsilon)
    epsilon = np.array(epsilon)

    norm = np.sum(w * w * (1 - epsilon))

    observable = (matrix_product - np.sum(w * w) * 2 * largest_epsilon * (m + 1)) / norm

    return (max(0.0, observable.item()) + m) / 2


def _predict_dqi_performance_imperfect_binary(
    A_bar: np.ndarray, m: int, l: int, w: int, epsilon: float
) -> float:
    if isinstance(epsilon, float) or isinstance(epsilon, int):
        epsilon = [float(epsilon)] * (l + 1)

    assert len(epsilon) == l + 1
    assert min(epsilon) >= 0
    assert w is None or len(w) == l + 1

    epsilon = np.array(epsilon)
    if w is None:
        A = make_A(2, 1, m, l)
        _, w = get_eigenvector(A, -1)
    else:
        w = np.array(w)

    norm = np.sum(w * w * (1 - epsilon))
    matrix_product = w.reshape((1, l + 1)) @ A_bar @ w.reshape((l + 1, 1))
    observable = matrix_product / norm

    return (max(0.0, observable.item()) + m) / 2


def approximate_A_bar(
    B: Matrix,
    v: vector,
    l: int,
    benchmarks: dict[int, BenchmarkResult],
    minimum_distance: int,
    n_tries=1000,
) -> np.ndarray:
    m = B.nrows()
    n = B.ncols()
    B_T = B.T

    A = make_A(2, 1, m, l)

    A_bar = np.zeros((l + 1, l + 1))

    zero = vector(GF(2), [0] * n)

    for k in range(0, l + 1):
        for k2 in range(k, l + 1):
            # For perfect decoding, A_bar[k, k2] = A[k, k2]
            if (
                k + k2 + 1 < minimum_distance
                and benchmarks[k].epsilon == 0
                and benchmarks[k2].epsilon == 0
            ):
                A_bar[k, k2] = A[k, k2]
                continue

            # In this regime, A_bar is guaranteed to be zero, since neither case matches
            if k + k2 + 1 < minimum_distance and k2 != k + 1:
                continue

            for i in range(m):
                e_i = vector(GF(2), [0] * m)
                e_i[i] = 1

                total_size = (
                    math.comb(m, k)
                    * (1 - benchmarks[k].epsilon)
                    * math.comb(m, k2)
                    * (1 - benchmarks[k2].epsilon)
                )

                n_matches = 0.0
                n_in_set = 0
                n_positive = 0
                # for y2 in benchmarks[k2].correct:

                # Case 1: y + y2 + e_i = 0

                for y2 in benchmarks[k2].correct:
                    y = y2 + e_i
                    if y.hamming_weight() != k:
                        continue
                    if y in benchmarks[k].correct:
                        n_matches += 1

                A_bar[k, k2] += (
                    total_size
                    * n_matches
                    / (len(benchmarks[k2].correct) * len(benchmarks[k].correct))
                )

                # Case 2: y + y2 + e_i != 0 but B_T * (y + y2 + e_i) = 0
                for _ in range(n_tries):
                    y = random.choice(benchmarks[k].correct)
                    y2 = random.choice(benchmarks[k2].correct)
                    if y + y2 + e_i == 0:
                        continue
                    if B_T * (y + y2 + e_i) == 0:
                        n_in_set += 1
                        if v.dot_product(y + y2) == v[i]:
                            n_positive += 1
                estimated_set_size = total_size * n_in_set / n_tries
                if estimated_set_size == 0:
                    continue
                ratio_positive = n_positive / n_in_set
                A_bar[
                    k, k2
                ] += estimated_set_size * ratio_positive - estimated_set_size * (
                    1 - ratio_positive
                )
            correction = math.sqrt(math.comb(m, k) * math.comb(m, k2))
            A_bar[k, k2] /= correction

    A_bar = A_bar + (A_bar.T - np.diag(np.diag(A_bar)))

    return A_bar
