"""Sound finite quotient screens retaining joint comparator polarity.

Quotient edges come from actual image transitions; hidden images may switch
inside a profile class. Thus quotient distances are lower bounds, not exact
closure laws or universal asymptotic estimates.
"""
import argparse
from collections import deque
from itertools import combinations
import json

from kahale_image_difficulty import graph


def probe(n):
    states,layers,edges,actual,prefix,suffix = graph(n)
    pairs = list(combinations(range(n),2))
    transport_checks = 0
    layer_transport_checks = 0
    four_coordinate_patterns = 0
    for image in states:
        witness_cache = {}
        def witness(ones,zeros):
            key = ones,zeros
            if key not in witness_cache:
                witness_cache[key] = sum(1 << k for k in range(n+1)
                    if any(x.bit_count()==k and x & ones == ones and not x & zeros for x in image))
            return witness_cache[key]
        for a,b in pairs:
            actual_image = frozenset(gate(x,a,b) for x in image)
            for p,q in pairs:
                if p==a and q==b:
                    predicted = 0
                elif p==a:
                    predicted = witness((1 << a)|(1 << b),1 << q)
                elif p==b:
                    predicted = witness(1 << a,1 << q)|witness(1 << b,1 << q)
                elif q==a:
                    predicted = witness(1 << p,1 << a)|witness(1 << p,1 << b)
                elif q==b:
                    predicted = witness(1 << p,(1 << a)|(1 << b))
                else:
                    predicted = witness(1 << p,1 << q)
                observed = sum(1 << k for k in range(n+1) if any(
                    x.bit_count()==k and (x >> p)&1 and not (x >> q)&1 for x in actual_image))
                assert predicted == observed
                transport_checks += 1
        for layer in layers:
            positive = [(1 << i,) for i in range(n)]
            negative = [(1 << i,) for i in range(n)]
            for a,b in layer:
                ab = (1 << a)|(1 << b)
                positive[a],negative[a] = (ab,),(1 << a,1 << b)
                positive[b],negative[b] = (1 << a,1 << b),(ab,)
            actual_image = frozenset(apply_layer(x,layer) for x in image)
            for p,q in pairs:
                predicted = 0
                for ones in positive[p]:
                    for zeros in negative[q]:
                        if ones & zeros:
                            continue
                        predicted |= witness(ones,zeros)
                        four_coordinate_patterns += (ones | zeros).bit_count()==4
                observed = sum(1 << k for k in range(n+1) if any(
                    x.bit_count()==k and (x >> p)&1 and not (x >> q)&1 for x in actual_image))
                assert predicted == observed
                layer_transport_checks += 1

    def profile(image,rankwise):
        bins = [0]*(n+1 if rankwise else 1)
        for x in image:
            k = x.bit_count() if rankwise else 0
            for pi,(a,b) in enumerate(pairs):
                if (x >> a)&1 and not (x >> b)&1:
                    bins[k] |= 1 << pi
        return tuple(bins)

    results = []
    for rankwise in (False,True):
        signatures = [profile(s,rankwise) for s in states]
        classes,index,members = [],{},[]
        ids = []
        for source,p in enumerate(signatures):
            if p not in index:
                index[p] = len(classes)
                classes.append(p)
                members.append([])
            ci = index[p]
            members[ci].append(source)
            ids.append(ci)
        reverse = [set() for _ in classes]
        successors = [set() for _ in classes]
        for source,row in enumerate(edges):
            for target in row:
                successors[ids[source]].add(ids[target])
                reverse[ids[target]].add(ids[source])
        target = index[(0,)*(n+1 if rankwise else 1)]
        distance = [None]*len(classes)
        distance[target] = 0
        queue = deque([target])
        while queue:
            t = queue.popleft()
            for s in reverse[t]:
                if distance[s] is None:
                    distance[s] = distance[t]+1
                    queue.append(s)
        assert all(x is not None for x in distance)
        assert all(distance[ids[i]] <= actual[i] for i in range(len(states)))
        failure = None
        for group in members:
            if len(group)<2:
                continue
            for li,layer in enumerate(layers):
                a = group[0]
                b = next((b for b in group if ids[edges[a][li]] != ids[edges[b][li]]),None)
                if b is not None:
                    failure = dict(prefix_a=prefix(a),prefix_b=prefix(b),
                                   image_a=sorted(states[a]),image_b=sorted(states[b]),
                                   common_profile=signatures[a],layer=layer,
                                   successor_a=signatures[edges[a][li]],
                                   successor_b=signatures[edges[b][li]])
                    if len(layer)==1:
                        ga,gb = layer[0]
                        for c in range(n):
                            if c in (ga,gb):
                                continue
                            for ones,zeros in (((1 << ga)|(1 << gb),1 << c),
                                               (1 << c,(1 << ga)|(1 << gb))):
                                for k in range(n+1):
                                    wa = any(x.bit_count()==k and x & ones == ones and not x & zeros for x in states[a])
                                    wb = any(x.bit_count()==k and x & ones == ones and not x & zeros for x in states[b])
                                    if wa!=wb:
                                        failure["hidden_mixed_witness"] = dict(weight=k,ones_mask=ones,zeros_mask=zeros,
                                            exists_a=wa,exists_b=wb)
                                        break
                                if "hidden_mixed_witness" in failure:
                                    break
                            if "hidden_mixed_witness" in failure:
                                break
                    break
            if failure:
                break
        ambiguity = []
        for ci,group in enumerate(members):
            lo,hi = min(group,key=lambda i:actual[i]),max(group,key=lambda i:actual[i])
            if actual[lo] != actual[hi]:
                ambiguity.append(dict(profile=classes[ci],minimum_actual=actual[lo],maximum_actual=actual[hi],
                                      prefix_a=prefix(lo),prefix_b=prefix(hi)))
        worst = max(range(len(states)),key=lambda i:actual[i]-distance[ids[i]])
        results.append(dict(rankwise=rankwise,classes=len(classes),
                            exact_distance_images=sum(distance[ids[i]]==actual[i] for i in range(len(states))),
                            maximum_gap=actual[worst]-distance[ids[worst]],
                            initial_lower_bound=distance[ids[0]],
                            deterministic_closure_counterexample=failure,
                            ambiguous_depth_classes=ambiguity,
                            worst_gap_witness=dict(prefix=prefix(worst),image=sorted(states[worst]),
                                                   quotient_depth=distance[ids[worst]],actual_depth=actual[worst]),
                            image_lower_bounds=[distance[ids[i]] for i in range(len(states))]))
    return dict(wires=n,images=len(states),actual_initial_depth=actual[0],
                exact_mixed_witness_transport_checks=transport_checks,
                exact_parallel_polarity_transport_checks=layer_transport_checks,
                four_coordinate_pattern_queries=four_coordinate_patterns,screens=results)


def gate(x,a,b):
    if (x >> a)&1 and not (x >> b)&1:
        x ^= (1 << a)|(1 << b)
    return x


def apply_layer(x,layer):
    for a,b in layer:
        x = gate(x,a,b)
    return x


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",required=True)
    args = parser.parse_args()
    result = dict(cases=[probe(n) for n in (2,3,4,5)],
                  status="Exact finite quotient lower bounds; no general profile closure or improved coefficient")
    with open(args.output,"w",encoding="utf-8") as handle:
        json.dump(result,handle,indent=2)
        handle.write("\n")
    print(json.dumps([dict(wires=c["wires"],screens=[{k:s[k] for k in
                         ("rankwise","classes","exact_distance_images","maximum_gap","initial_lower_bound")}
                         for s in c["screens"]]) for c in result["cases"]],indent=2))
