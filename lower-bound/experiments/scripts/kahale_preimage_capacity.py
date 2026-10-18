"""Exhaustive four-wire screen of singleton Hall capacities; exact arithmetic."""
from itertools import product
from fractions import Fraction
import json
from pathlib import Path
from math import comb
from kahale_image_difficulty import gate_image, graph
from kahale_layer_occupation import matchings


def pair_union_capacity(m, edges):
    """Number of input pairs permitted by at least one output edge.

    Source pairs in different routing groups belong to one edge; source pairs
    within a group belong to every incident edge, and must be counted once.
    """
    touched = {i for edge in edges for i in edge}
    return sum(m[i]*m[j] for i,j in edges)+sum(comb(m[i],2) for i in touched)


def check_pair_capacity_formula():
    edges = [(i,j) for i in range(4) for j in range(i+1,4)]
    checks = 0
    for m in product(range(5),repeat=4):
        if sum(m)!=4:
            continue
        q = tuple(i for i in range(4) for _ in range(m[i]))
        for mask in range(64):
            selected = [edge for j,edge in enumerate(edges) if mask >> j & 1]
            brute = sum(any(q[a] in edge and q[b] in edge for edge in selected)
                        for a in range(4) for b in range(a+1,4))
            assert pair_union_capacity(m,selected)==brute
            checks += 1
    return checks


def routing(domain, ordered=False, mode='full'):
    """Independent rank assignments: total on inputs, onto each output slice.

    This is necessary, not sufficient, for one monotone conserving map.
    Return a singleton routing witnessing every rank's Hall conditions.
    """
    singles = [i for i in range(4) if 1 << i in domain]
    for q in product(singles, repeat=4):
        if set(q) != set(singles) or (ordered and any(q[i] < i for i in range(4))):
            continue
        valid = True
        for k in ((2,) if mode=='rank2' else (2,3)):
            inputs = [s for s in range(16) if s.bit_count()==k]
            outputs = [y for y in domain if y.bit_count()==k]
            routes = {s:sum(1 << j for j in set(q[i] for i in range(4) if s >> i & 1)) for s in inputs}
            allowed = {y:[s for s in inputs if routes[s] & ~y == 0] for y in outputs}
            if any(not any(s in choices for choices in allowed.values()) for s in inputs):
                valid = False
                break
            if any(not choices for choices in allowed.values()):
                valid = False
                break
            if mode=='individual' or (mode=='rank2_hall_rank3_individual' and k==3):
                continue
            assigned = {}
            def augment(y, seen):
                for s in allowed[y]:
                    if s in seen:
                        continue
                    seen.add(s)
                    if s not in assigned or augment(assigned[s], seen):
                        assigned[s] = y
                        return True
                return False
            if not all(augment(y,set()) for y in outputs):
                valid = False
                break
        if valid:
            return q
    return None


def main():
    root = Path(__file__).resolve().parents[3]
    data = json.loads((root/'docs/kahale-witness-charge-results.json').read_text())
    terms = data['quadratic_cases'][0]['simplified_certificate']['active_weights']
    def potential(domain):
        def witness(p):
            k,a,b = p
            return any(x.bit_count()==k and x&a==a and not x&b for x in domain)
        return sum(Fraction(t['weight'])*witness(t['first'])*witness(t['second']) for t in terms)
    sorted_points = {0,8,12,14,15}
    optional = sorted(set(range(16))-sorted_points)
    layers = [tuple(layer) for layer in matchings(tuple(range(4))) if layer]
    actual_images,*_ = graph(4)
    assert all(routing(domain) is not None for domain in actual_images)
    counts = dict(domains=0,bottom_capacity=0,bottom_top_capacity=0,ordered_bottom_top_capacity=0)
    relaxations = {mode:dict(domains=0,worst_drop='0') for mode in
                   ('individual','rank2','rank2_hall_rank3_individual')}
    worst = {}
    for mask in range(1 << len(optional)):
        domain = frozenset(sorted_points | {x for i,x in enumerate(optional) if mask >> i & 1})
        counts['domains'] += 1
        value = potential(domain)
        drops = [(value-potential(frozenset(gate_image(x,layer) for x in domain)),layer) for layer in layers]
        drop,layer = max(drops)
        for mode,report in relaxations.items():
            rq = routing(domain,mode=mode)
            if rq is None:
                continue
            report['domains'] += 1
            if drop>Fraction(report['worst_drop']):
                report.update(worst_drop=str(drop),image=sorted(domain),layer=layer,singleton_routing=rq)
        q = routing(domain)
        if q is None:
            continue
        categories = ['bottom_capacity']
        dual = frozenset(15^x for x in domain)
        if routing(dual) is not None:
            categories.append('bottom_top_capacity')
            # Complement plus wire reversal converts the top routing to ascending order.
            reversed_dual = frozenset(int(f'{x:04b}'[::-1],2) for x in dual)
            if routing(domain,True) is not None and routing(reversed_dual,True) is not None:
                categories.append('ordered_bottom_top_capacity')
        for category in categories:
            counts[category] += 1
        for layer in layers:
            after = frozenset(gate_image(x,layer) for x in domain)
            drop = potential(domain)-potential(after)
            for category in categories:
                if category not in worst or drop > Fraction(worst[category]['drop']):
                    worst[category] = dict(drop=str(drop),image=sorted(domain),layer=layer,singleton_routing=q)
    assert counts['domains']==2048 and all(Fraction(v['drop'])<=1 for v in worst.values())
    result = dict(counts=counts,pair_capacity_formula_checks=check_pair_capacity_formula(),actual_images_checked=len(actual_images),
                  bottom_capacity_layer_checks=counts['bottom_capacity']*len(layers),worst=worst,relaxations=relaxations,
                  status='Necessary independent-rank capacity screen, not a monotone-map or network certificate')
    (root/'docs/kahale-preimage-capacity-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
