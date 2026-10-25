"""Independent labelled-table oracle for multiple initial states (1--3 states).

Structural isomorphism uses all state permutations. Language equivalence uses
subset construction followed by pair distinguishability, independently of the
C++ filter's signature refinement. No single initial state need reach all states.
"""
import itertools
from pathlib import Path
import re
import subprocess

from check_enumeration import automaton_lines, minimal, state_count


def reachable(table, initial):
    reached = set(initial)
    while True:
        more = reached | {table[2*q+a] for q in reached for a in range(2)}
        more.discard(-1)
        if more == reached:
            return len(reached) == len(table)//2
        reached = more


def structural_key(table, final, initial):
    n = len(final)
    images = []
    for order in itertools.permutations(range(n)):
        renamed = {old: new for new, old in enumerate(order)}
        renamed[-1] = -1
        images.append((tuple(int(q in initial) for q in order),
                       tuple(final[q] for q in order),
                       tuple(renamed[table[2*q+a]] for q in order for a in range(2))))
    return min(images)


def language_key(table, final, initial):
    start = frozenset(initial)
    subsets = [start]
    index = {start: 0}
    transitions, finals = [], []
    for subset in subsets:
        finals.append(int(any(final[q] for q in subset)))
        row = []
        for a in range(2):
            target = frozenset(table[2*q+a] for q in subset if table[2*q+a] != -1)
            if target not in index:
                index[target] = len(subsets)
                subsets.append(target)
            row.append(index[target])
        transitions.append(row)
    count = len(subsets)
    distinct = {(p, q) for p in range(count) for q in range(p+1, count)
                if finals[p] != finals[q]}
    while True:
        more = distinct | {(p, q) for p in range(count) for q in range(p+1, count)
                           if any(tuple(sorted((transitions[p][a], transitions[q][a]))) in distinct
                                  for a in range(2))}
        if more == distinct:
            break
        distinct = more
    representative = [next(q for q in range(p+1) if q == p or (q, p) not in distinct)
                      for p in range(count)]
    order = [representative[0]]
    renamed = {order[0]: 0}
    result = [2]
    for state in order:
        result.append(finals[state])
        for target in transitions[state]:
            image = representative[target]
            if image not in renamed:
                renamed[image] = len(order)
                order.append(image)
            result.append(renamed[image])
    return tuple(result)


def expected(n, partial, raw):
    result = set()
    initial_sets = [tuple(q for q in range(n) if bits[q])
                    for bits in itertools.product(range(2), repeat=n) if any(bits)]
    for table in itertools.product(range(-1 if partial else 0, n), repeat=2*n):
        for final in itertools.product(range(2), repeat=n):
            if not raw and not minimal(table, final, partial):
                continue
            for initial in initial_sets:
                if reachable(table, initial):
                    key = structural_key if raw else language_key
                    result.add(key(table, final, initial))
    return result


def parse(text, n, partial, raw, minimum_sizes=None):
    lines = automaton_lines(text)
    result = set()
    sizes = []
    for line in lines:
        size = state_count(line)
        assert size == n if raw else 1 <= size <= n
        sizes.append(size)
        table, final, initial, seen = [-1]*(2*size), [0]*size, [], set()
        tokens = line.split()
        if tokens and tokens[0].isdigit():
            assert int(tokens.pop(0)) == size, 'incorrect state count'
        for token in tokens:
            if token.startswith('i') or token.startswith('f'):
                q = int(token[1:])
                assert 0 <= q < size
                if token[0] == 'i':
                    initial.append(q)
                else:
                    final[q] = 1
            else:
                match = re.fullmatch(r'(\d+)([ab])(\d+)', token)
                assert match, token
                p, a, q = match.groups()
                p, q = int(p), int(q)
                assert 0 <= p < size and 0 <= q < size
                edge = 2*p + (a == 'b')
                assert edge not in seen
                seen.add(edge)
                table[edge] = q
        assert initial and len(set(initial)) == len(initial)
        assert partial or -1 not in table
        assert reachable(table, initial)
        assert raw or minimal(tuple(table), tuple(final), partial)
        key = (structural_key if raw else language_key)(table, final, initial)
        assert key not in result, ('duplicate structure' if raw else 'duplicate language', line)
        if minimum_sizes is not None:
            assert size == minimum_sizes[key], ('larger representative emitted first', line)
        result.add(key)
    if not raw:
        assert sizes == sorted(sizes), 'sizes must be enumerated in increasing order'
    return result


def check(binary, raw=False):
    cumulative = {False: set(), True: set()}
    minimum_sizes = {False: {}, True: {}}
    previous = {False: [], True: []}
    for n in range(1, 4):
        for partial in (False, True):
            args = [str(binary), str(n), '--multi-initial'] + (['--partial'] if partial else [])
            run = subprocess.run(args, check=True, capture_output=True, text=True, timeout=30)
            assert not run.stderr, run.stderr
            wanted = expected(n, partial, raw)
            if not raw:
                for key in wanted:
                    minimum_sizes[partial].setdefault(key, n)
                cumulative[partial].update(wanted)
                wanted = cumulative[partial]
                lines = automaton_lines(run.stdout)
                assert lines[:len(previous[partial])] == previous[partial], 'output prefix changed'
                previous[partial] = lines
            actual = parse(run.stdout, n, partial, raw,
                           minimum_sizes=None if raw else minimum_sizes[partial])
            assert actual == wanted, (n, partial, raw, len(wanted-actual), len(actual-wanted))
            print(f'multi-initial {"exactly" if raw else "maximum"} {n} states, '
                  f'{"partial" if partial else "complete"}: '
                  f'{len(actual)} {"structures" if raw else "distinct languages"} OK')


if __name__ == '__main__':
    import sys
    check(Path(sys.argv[1] if len(sys.argv) > 1 else './dfa').resolve())
    if len(sys.argv) > 2:
        check(Path(sys.argv[2]).resolve(), raw=True)
