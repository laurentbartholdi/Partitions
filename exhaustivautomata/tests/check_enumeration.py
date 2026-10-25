#!/usr/bin/env python3
"""Independent exhaustive oracle for reachable binary DFAs with 1--3 states.

Run after `make dfa`: python3 tests/check_enumeration.py
The reference enumerates labelled tables and tests right-language equality by
pair distinguishability after completing with an implicit rejecting sink.
"""
import itertools
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
BINARY = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else ROOT / "dfa"


def canonical(transitions, final):
    """Canonical breadth-first numbering starting at state zero."""
    order = [0]
    renamed = {0: 0, -1: -1}
    for state in order:
        for target in transitions[2 * state:2 * state + 2]:
            if target not in renamed:
                renamed[target] = len(order)
                order.append(target)
    if len(order) != len(final):
        return None
    return (tuple(renamed[transitions[2 * q + a]] for q in order for a in range(2)),
            tuple(final[q] for q in order))


def minimal(transitions, final, partial):
    n = len(final)
    sink = n
    completed = tuple(sink if q == -1 else q for q in transitions) + (sink, sink)
    finals = final + (0,)
    distinct = {(p, q) for p in range(n + 1) for q in range(p + 1, n + 1)
                if finals[p] != finals[q]}
    while True:
        more = distinct | {(p, q) for p in range(n + 1) for q in range(p + 1, n + 1)
                           if any(tuple(sorted((completed[2*p+a], completed[2*q+a]))) in distinct
                                  for a in range(2))}
        if more == distinct:
            break
        distinct = more
    if any((p, q) not in distinct for p in range(n) for q in range(p + 1, n)):
        return False
    if partial and any((p, sink) not in distinct for p in range(n)):
        return n == 1 and not final[0] and transitions == (-1, -1)
    return True


def expected(n, partial, filter_minimal=True):
    result = set()
    for transitions in itertools.product(range(-1 if partial else 0, n), repeat=2*n):
        if canonical(transitions, (0,) * n) is None:
            continue
        for final in itertools.product(range(2), repeat=n):
            if not filter_minimal or minimal(transitions, final, partial):
                result.add(canonical(transitions, final))
    return result


def automaton_lines(text):
    lines = text.splitlines()
    assert lines, "no output"
    if lines[-1].strip().isdigit():
        total = int(lines.pop())
        assert total == len(lines), "incorrect counter"
    return lines


def state_count(line):
    """Infer size from the output: every reachable state is named somewhere."""
    tokens = line.split()
    declared = int(tokens.pop(0)) if tokens and tokens[0].isdigit() else None
    states = []
    for token in tokens:
        marker = re.fullmatch(r'[if](\d+)', token)
        edge = re.fullmatch(r'(\d+)[ab](\d+)', token)
        assert marker or edge, token
        states.extend(map(int, marker.groups() if marker else edge.groups()))
    assert states, 'no states'
    size = max(states) + 1
    assert declared is None or declared == size, 'incorrect state count'
    return size


def read_output(text, n, partial, maximum=False):
    lines = automaton_lines(text)
    actual = []
    sizes = []
    languages = set()
    for line in lines:
        size = state_count(line)
        assert 1 <= size <= n if maximum else size == n
        sizes.append(size)
        transitions = [-1] * (2*size)
        final = [0] * size
        initial = []
        seen = set()
        tokens = line.split()
        if tokens and tokens[0].isdigit():
            assert int(tokens.pop(0)) == size, 'incorrect state count'
        for token in tokens:
            if token.startswith('i'):
                initial.append(int(token[1:]))
            elif token.startswith('f'):
                state = int(token[1:])
                assert 0 <= state < size
                final[state] = 1
            else:
                match = re.fullmatch(r'(\d+)([ab])(\d+)', token)
                assert match, token
                source, letter, target = match.groups()
                source, target = int(source), int(target)
                assert 0 <= source < size and 0 <= target < size
                edge = 2*source + (letter == 'b')
                assert edge not in seen, "duplicate transition"
                seen.add(edge)
                transitions[edge] = target
        assert initial == [0], initial
        assert partial or -1 not in transitions
        key = canonical(tuple(transitions), tuple(final))
        assert key is not None, "unreachable state"
        actual.append(key)
        if maximum:
            from check_multi_initial import language_key
            language = language_key(transitions, final, initial)
            assert language not in languages, 'duplicate language across sizes'
            languages.add(language)
    if maximum:
        assert sizes == sorted(sizes), 'sizes must be enumerated in increasing order'
    assert len(set(actual)) == len(actual), "duplicate up to renaming"
    return set(actual)


def check(binary, raw=False):
    cumulative = {False: set(), True: set()}
    previous = {False: [], True: []}
    for n in range(1, 4):
        for partial in (False, True):
            args = [str(binary), str(n)] + (['--partial'] if partial else [])
            run = subprocess.run(args, check=True, text=True, capture_output=True, timeout=30)
            assert not run.stderr, run.stderr
            actual = read_output(run.stdout, n, partial, maximum=not raw)
            wanted = expected(n, partial, filter_minimal=not raw)
            if not raw:
                cumulative[partial].update(wanted)
                wanted = cumulative[partial]
                lines = automaton_lines(run.stdout)
                assert lines[:len(previous[partial])] == previous[partial], 'output prefix changed'
                previous[partial] = lines
            assert actual == wanted, (n, partial, len(wanted-actual), len(actual-wanted))
            print(f'{"raw" if raw else "maximum"} {n} states, '
                  f'{"partial" if partial else "complete"}: {len(actual)} OK')


if __name__ == '__main__':
    from check_multi_initial import check as check_multi
    check(BINARY)
    check_multi(BINARY)
    for args in ([], ['0'], ['-1'], ['nonsense'], ['2x'], ['999999999999999999999'],
                 ['2', '--unknown'], ['2', '--partial', 'extra'],
                 ['2', '--partial', '--partial'], ['2', '--multi-initial', '--multi-initial']):
        run = subprocess.run([str(BINARY)] + args, text=True, capture_output=True, timeout=5)
        assert run.returncode != 0 and run.stderr and not run.stdout, args
    print('Invalid arguments: OK')
    if len(sys.argv) > 2:
        check(Path(sys.argv[2]).resolve(), raw=True)
        check_multi(Path(sys.argv[2]).resolve(), raw=True)
    else:
        with tempfile.TemporaryDirectory(prefix='dfa-tests-') as directory:
            probe = Path(directory) / 'generator-probe'
            subprocess.run(shlex.split(os.environ.get('CXX', 'c++')) + [
                '-std=c++98', '-O2',
                '-I', str(ROOT / 'include'), str(ROOT / 'tests/generator_probe.cpp'),
                str(ROOT / 'include/CatalanSuit.cpp'), str(ROOT / 'include/CompletionSuit.cpp'),
                '-o', str(probe)], check=True)
            check(probe, raw=True)
            check_multi(probe, raw=True)
