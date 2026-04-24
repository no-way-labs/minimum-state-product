#!/usr/bin/env python3
"""Direct word-family generators for the EC BAF branch."""

from __future__ import annotations

from typing import Iterable

from ec_distance_class_values import canonical_turnaround_word, representative_word


def reflect_word(word: tuple[int, ...], n: int) -> tuple[int, ...]:
    return tuple((2 - x) % n for x in word)


def normalize_rotation(word: tuple[int, ...]) -> tuple[int, ...]:
    return min(word[i:] + word[:i] for i in range(len(word)))


def distance_class_words(n: int, d: int) -> list[tuple[int, ...]]:
    """Return the direct two-turnaround words in distance class d."""
    rep = representative_word(n, d)
    words = {rep}
    refl = normalize_rotation(reflect_word(rep, n))
    words.add(refl)
    return sorted(words)


def all_distance_words(n: int) -> list[tuple[int, ...]]:
    words = set()
    for d in range(n // 2 + 1):
        words.update(distance_class_words(n, d))
    return sorted(words)
