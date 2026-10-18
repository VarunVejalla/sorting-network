"""Exact obstruction to any singleton-routing correction of the witness charge."""
from collections import Counter, deque
from fractions import Fraction
from pathlib import Path
import json
from kahale_image_difficulty import gate_image, graph


def main():
    root = Path(__file__).resolve().parents[3]
    terms = json.loads((root/'docs/kahale-witness-charge-results.json').read_text())['quadratic_cases'][0]['simplified_certificate']['active_weights']
    def potential(domain):
        def witness(t):
            k,a,b = t
            return any(x.bit_count()==k and x&a==a and not x&b for x in domain)
        return sum(Fraction(t['weight'])*witness(t['first'])*witness(t['second']) for t in terms)
    images,layers,edges,*_ = graph(5)
    values = [potential({x>>1 for x in domain if not x&1}) for domain in images]
    start = (0,(1,1,1,1,1))
    parents = {start:None}
    todo = deque([start])
    worst = Fraction(0)
    checks = 0
    while todo:
        source,m = state = todo.popleft()
        for j,layer in enumerate(layers):
            next_m = list(m)
            for a,b in layer:
                next_m[b] += next_m[a]
                next_m[a] = 0
            target = (edges[source][j],tuple(next_m))
            if target not in parents:
                parents[target] = state,layer
                todo.append(target)
            if m[1:]==tuple(next_m[1:]):
                checks += 1
                worst = max(worst,values[source]-values[target[0]])
    assert len(parents)==1019 and worst==Fraction(5,3)
    prefix = (((0,1),(2,3)),((0,2),))
    layer = ((2,4),)
    def run(x):
        for step in prefix:
            x = gate_image(x,step)
        return x
    before = [run(x) for x in range(32)]
    after = [gate_image(y,layer) for y in before]
    assert all(before[1<<i]==after[1<<i] for i in range(5))
    fiber = {y>>1 for y in before if not y&1}
    next_fiber = {y>>1 for y in after if not y&1}
    assert potential(fiber)==3 and potential(next_fiber)==Fraction(4,3)
    masses = {}
    for k in (1,2,3):
        masses[k] = dict(before=dict(sorted(Counter(y>>1 for x,y in enumerate(before)
                                if x.bit_count()==k and not y&1).items())),
                        after=dict(sorted(Counter(y>>1 for x,y in enumerate(after)
                                if x.bit_count()==k and not y&1).items())))
    result = dict(reachable_image_multiplicity_states=len(parents),
                  total_layer_checks=len(parents)*len(layers),
                  unchanged_singleton_multiplicity_checks=checks,worst_unchanged_drop=str(worst),
                  prefix=prefix,next_layer=layer,fiber=sorted(fiber),after_fiber=sorted(next_fiber),
                  potential_before='3',potential_after='4/3',
                  singleton_outputs=[before[1<<i] for i in range(5)],
                  rank_preimage_masses=masses,
                  status='Exact finite obstruction: no additive function of singleton routes can repair this unit-drop inequality')
    (root/'docs/kahale-singleton-correction-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('reachable_image_multiplicity_states','total_layer_checks',
                   'unchanged_singleton_multiplicity_checks','worst_unchanged_drop','potential_before','potential_after')},indent=2))


if __name__=='__main__':
    main()
