from __future__ import annotations
import math
import itertools
import random
from typing import Iterator, Callable

import scipy as sp
import numpy as np
from ldpc import BpDecoder, BpOsdDecoder
from sage.all import Matrix, GF, codes, vector, codes
from sage.coding.linear_code import (
    LinearCodeNearestNeighborDecoder,
    LinearCodeSyndromeDecoder,
)
from sage.coding.information_set_decoder import LinearCodeInformationSetDecoder
from sage.coding.grs_code import GRSBerlekampWelchDecoder
from sage.coding.guruswami_sudan.gs_decoder import GRSGuruswamiSudanDecoder


class BenchmarkResult:
    def __init__(self, correct: list, incorrect: list, epsilon: float):
        self.correct = correct
        self.incorrect = incorrect
        self.epsilon = epsilon
        for e in correct:
            e.set_immutable()
        for e in incorrect:
            e.set_immutable()
        self.correct_set = set(correct)
        self.incorrect_set = set(incorrect)

    def __str__(self) -> str:
        return f"BenchmarkResult(#correct = {len(self.correct)}, #incorrect = {len(self.incorrect)}, epsilon = {self.epsilon})"


def generate_all_errors(field: GF, n: int, k: int) -> Iterator[vector]:
    els = [e for e in field if e != 0]

    for error_indices in (
        np.array(comb) for comb in itertools.combinations(range(n), k)
    ):
        for error_digits in itertools.product(els, repeat=k):
            e = vector(field, [0] * n)
            for i, idx in enumerate(error_indices):
                e[idx] += error_digits[i]
            yield e


def generate_errors(field: GF, n: int, k: int, n_tries: int | None) -> Iterator[vector]:
    els = [e for e in field if e != 0]

    n_possible_errors = math.comb(n, k) * len(els) ** k
    if n_tries is None or n_possible_errors <= n_tries:
        for e in generate_all_errors(field, n, k):
            yield e

    elif 2 * n_tries >= n_possible_errors:
        all_errors = [e for e in generate_all_errors(field, n, k)]
        random.shuffle(all_errors)
        for i in range(n_tries):
            yield all_errors[i]
    else:
        seen = set()
        n_produced = 0
        while n_produced < n_tries:
            e = vector(field, [0] * n)
            error_indices = np.random.choice(n, k, replace=False)
            for i in error_indices:
                e[i] += random.choice(els)
            e.set_immutable()
            if e in seen:
                continue
            seen.add(e)
            n_produced += 1
            yield e


class AbstractDecoder:
    def __init__(self, instance: "MaxLinSat"):
        self.instance = instance
        self.benchmarks = {}

    def decoding_radius(self) -> int | None:
        raise NotImplementedError()

    def decode(self, message: vector, l: int) -> vector:
        raise NotImplementedError()

    def compute_benchmarks(self, l: int, n_errors: int, n_tries: int | None):
        correct = list()
        incorrect = list()

        els = [e for e in self.instance.field if e != 0]
        c = vector(self.instance.field, [0] * self.instance.get_m())
        # c = vector(self.field, [0] * len(c))

        for e in generate_errors(self.instance.field, len(c), n_errors, n_tries):
            c_tilde = e
            c_out = self.decode(c_tilde, l)

            if c_out == c:
                correct.append(e)
            else:
                incorrect.append(e)

        epsilon = len(incorrect) / (len(correct) + len(incorrect))

        self.benchmarks[(n_errors, n_tries)] = BenchmarkResult(
            correct, incorrect, epsilon
        )

    def get_benchmarks(
        self, l: int, n_errors: int, n_tries: int | None = 100
    ) -> BenchmarkResult:
        key = (n_errors, n_tries)
        if key not in self.benchmarks:
            self.compute_benchmarks(l, n_errors, n_tries)
        return self.benchmarks[key]


class NearestNeighborDecoder(AbstractDecoder):
    @staticmethod
    def constructor() -> Callable[["MaxLinSat"], AbstractDecoder]:
        return NearestNeighborDecoder

    def __init__(self, instance: "MaxLinSat"):
        super().__init__(instance)
        self.decoder = LinearCodeNearestNeighborDecoder(instance.get_code())

    def decoding_radius(self) -> int:
        return None

    def decode(self, message: vector, l: int) -> vector:
        return self.decoder.decode_to_code(message)


class SyndromeDecoder(AbstractDecoder):
    @staticmethod
    def constructor(**decoder_parameters) -> Callable[["MaxLinSat"], AbstractDecoder]:
        return lambda instance: SyndromeDecoder(instance, **decoder_parameters)

    def __init__(self, instance: "MaxLinSat"):
        self.decoders = {}

    def get_decoder(self, l: int) -> LinearCodeSyndromeDecoder:
        valid_ls = [k for k in self.decoders if k >= l]

        if len(valid_ls) > 0:
            return self.decoders[min(valid_ls)]

        decoder = LinearCodeSyndromeDecoder(self.instance.get_code(), l)
        self.decoders[l] = decoder
        return decoder

    def decoding_radius(self):
        return None

    def decode(self, message: vector, l: int):
        decoder = self.get_decoder(l)
        return decoder.decode_to_code(message)


class InformationSetDecoder(AbstractDecoder):
    @staticmethod
    def constructor(**decoder_parameters) -> Callable[["MaxLinSat"], AbstractDecoder]:
        return lambda instance: InformationSetDecoder(instance, **decoder_parameters)

    def __init__(self, instance: "MaxLinSat", **decoder_parameters):
        super().__init__(instance)
        self.decoder_parameters = decoder_parameters
        self.decoders = {}

    def get_decoder(self, l: int) -> LinearCodeInformationSetDecoder:
        if l not in self.decoders:
            self.decoders[l] = LinearCodeInformationSetDecoder(
                self.instance.get_code(), l, **self.decoder_parameters
            )
        return self.decoders[l]

    def decoding_radius(self):
        return None

    def decode(self, message: vector, l: int):
        decoder = self.get_decoder(l)
        return decoder.decode_to_code(message)


class BeliefPropagationDecoder(AbstractDecoder):
    @staticmethod
    def constructor(**decoder_parameters) -> Callable[["MaxLinSat"], AbstractDecoder]:
        return lambda instance: BeliefPropagationDecoder(instance, **decoder_parameters)

    def __init__(self, instance: "MaxLinSat", **decoder_parameters):
        super().__init__(instance)
        self.H = sp.sparse.csc_matrix(
            np.array(self.instance.get_code().parity_check_matrix()).astype(np.int8)
        )
        self.decoder_parameters = decoder_parameters
        self.decoders = {}

    def decoding_radius(self) -> None:
        return None

    def get_decoder(self, l: int) -> BpDecoder:
        if l not in self.decoders:
            error_rate = l / self.instance.get_m()
            self.decoders[l] = BpDecoder(
                self.H, error_rate=error_rate, **self.decoder_parameters
            )
        return self.decoders[l]

    def decode(self, message: vector, l: int) -> vector:
        message_np = np.array(message)
        decoder = self.get_decoder(l)
        result_np = decoder.decode(message_np)
        return vector(self.instance.field, result_np)


class BeliefPropagationOsdDecoder(AbstractDecoder):
    @staticmethod
    def constructor(**decoder_parameters) -> Callable[["MaxLinSat"], AbstractDecoder]:
        return lambda instance: BeliefPropagationOsdDecoder(
            instance, **decoder_parameters
        )

    def decoding_radius(self) -> None:
        return None

    def __init__(self, instance: "MaxLinSat", **decoder_parameters):
        super().__init__(instance)
        self.H = sp.sparse.csc_matrix(
            np.array(self.instance.get_code().parity_check_matrix()).astype(np.int8)
        )
        self.decoder_parameters = decoder_parameters
        self.decoders = {}

    def get_decoder(self, l: int) -> BpOsdDecoder:
        if l not in self.decoders:
            error_rate = l / self.instance.get_m()
            self.decoders[l] = BpOsdDecoder(
                self.H, error_rate=error_rate, **self.decoder_parameters
            )
        return self.decoders[l]

    def decode(self, message, l):
        message_np = np.array(message, dtype=np.int8)
        syndrome = self.H @ message_np % 2
        decoder = self.get_decoder(l)
        result_np = decoder.decode(syndrome)
        decoded = message_np + result_np
        return vector(self.instance.field, decoded)


class GeneralizedReedSolomonDecoder(AbstractDecoder):
    @staticmethod
    def constructor() -> Callable[["MaxLinSat"], AbstractDecoder]:
        return GeneralizedReedSolomonDecoder

    def __init__(self, instance: "MaxLinSat"):
        super().__init__(instance)
        self.decoder = GRSBerlekampWelchDecoder(self.instance.code)
        self.list_decoders = {}

    def get_decoder_by_l(
        self, l: int
    ) -> GRSBerlekampWelchDecoder | GRSGuruswamiSudanDecoder:
        if l <= self.decoding_radius():
            return self.decoder
        if l in self.list_decoders:
            return self.list_decoders[l]
        decoder = GRSGuruswamiSudanDecoder(self.instance.code, l)
        self.list_decoders[l] = decoder
        return decoder

    def decoding_radius(self) -> int:
        return (self.instance.get_minimum_distance() - 1) // 2

    def decode(self, message: vector, l: int) -> vector:
        result = self.get_decoder_by_l(l).decode_to_code(message)
        if isinstance(result, list):
            return result[0]
        return result


def DEFAULT_DECODER_CONSTRUCTOR(instance):
    if instance.field.order() == 2:
        return BeliefPropagationDecoder(instance)
    return InformationSetDecoder(instance)
