"""Exact small Boolean-image completion distances and residual witnesses.

All nonempty ascending parallel matchings are included. No symmetry quotient,
SMT solver, or floating-point optimization is used.
"""
import argparse
from collections import deque
from itertools import combinations
import json

from kahale_layer_occupation import matchings


def gate_image(x, layer):
    for a,b in layer:
        if (x >> a)&1 and not (x >> b)&1:
            x ^= (1 << a) | (1 << b)
    return x


def image_metrics(image,n):
    full = (1 << n)-1
    cube = (0,0,0)
    for free in range(1 << n):
        dimension = free.bit_count()
        if dimension <= cube[0]:
            continue
        fixed = full ^ free
        groups = {}
        for x in image:
            key = x & fixed
            groups[key] = groups.get(key,0)+1
        for fixed_ones,count in groups.items():
            if count == 1 << dimension:
                cube = dimension,free,fixed_ones
                break
    supports,essential,essential_masks,allowed_sets,monotone_sets,monotone_supports = [],[],[],[],[],[]
    for k in range(n):
        coords = 0
        for x in image:
            if x.bit_count() != k:
                continue
            for i in range(n):
                if not (x >> i)&1 and (x | (1 << i)) in image:
                    coords |= 1 << i
        essential.append(coords.bit_count())
        essential_masks.append(coords)
        # A coordinate set determines the target output iff no projection
        # class contains inputs on both sides of the weight threshold.
        minimum = n
        allowed = 0
        for subset in range(1 << n):
            size = subset.bit_count()
            if coords & ~subset:
                continue
            labels = {}
            consistent = True
            for x in image:
                key = x & subset
                label = int(x.bit_count()>k)
                if key in labels and labels[key] != label:
                    consistent = False
                    break
                labels[key] = label
            if consistent:
                minimum = min(minimum,size)
                allowed |= 1 << subset
        assert minimum >= essential[-1]
        supports.append(minimum)
        allowed_sets.append(allowed)
        cuts = {x & ~y for x in image if x.bit_count()>k
                for y in image if y.bit_count()<=k}
        assert 0 not in cuts
        monotone = 0
        mono_minimum = n
        for subset in range(1 << n):
            if all(subset & cut for cut in cuts):
                monotone |= 1 << subset
                mono_minimum = min(mono_minimum,subset.bit_count())
        assert not monotone & ~allowed
        monotone_sets.append(monotone)
        monotone_supports.append(mono_minimum)
    fanout = [sum((mask >> i)&1 for mask in essential_masks) for i in range(n)]
    return dict(largest_cube_dimension=cube[0],cube_free_mask=cube[1],
                cube_fixed_ones=cube[2],rank_minimum_determining_coordinates=supports,
                rank_essential_coordinate_counts=essential,
                rank_essential_coordinate_masks=essential_masks,
                essential_rank_fanout=fanout,
                fanout_depth_bound=(max(fanout)-1).bit_length(),
                rank_determining_set_masks=allowed_sets,
                rank_monotone_determining_set_masks=monotone_sets,
                rank_minimum_monotone_coordinates=monotone_supports,
                support_depth_bound=(max(supports)-1).bit_length())


def cone_catalogue(n,layers):
    initial = tuple(1 << i for i in range(n))
    states,index,parents,depths = [initial],{initial:0},[None],[0]
    for source,cones in enumerate(states):
        for li,layer in enumerate(layers):
            out = list(cones)
            for a,b in layer:
                out[a] = out[b] = cones[a] | cones[b]
            out = tuple(out)
            if out not in index:
                index[out] = len(states)
                states.append(out)
                parents.append((source,li))
                depths.append(depths[source]+1)
    def witness(source):
        out = []
        while parents[source] is not None:
            source,li = parents[source]
            out.append(layers[li])
        return out[::-1]
    return states,depths,witness


def graph(n):
    layers = [l for l in matchings(list(range(n))) if l]
    maps = [tuple(gate_image(x,l) for x in range(1 << n)) for l in layers]
    initial = frozenset(range(1 << n))
    states,index,parents = [initial],{initial:0},[None]
    edges,reverse = [],[[]]
    for source,image in enumerate(states):
        successors = []
        for li,row in enumerate(maps):
            target_image = frozenset(row[x] for x in image)
            if target_image not in index:
                index[target_image] = len(states)
                states.append(target_image)
                parents.append((source,li))
                reverse.append([])
            target = index[target_image]
            successors.append(target)
            reverse[target].append((source,li))
        edges.append(successors)
    target_image = frozenset(((1 << k)-1) << (n-k) for k in range(n+1))
    terminal = index[target_image]
    distance = [None]*len(states)
    policy = [None]*len(states)
    distance[terminal] = 0
    queue = deque([terminal])
    while queue:
        target = queue.popleft()
        for source,li in reverse[target]:
            if distance[source] is None:
                distance[source] = distance[target]+1
                policy[source] = li
                queue.append(source)
    assert all(d is not None for d in distance)

    def prefix(source):
        out = []
        while parents[source] is not None:
            source,li = parents[source]
            out.append(layers[li])
        return out[::-1]

    def suffix(source):
        out = []
        while distance[source]:
            li = policy[source]
            out.append(layers[li])
            source = edges[source][li]
        return out

    return states,layers,edges,distance,prefix,suffix


def probe(n,sorting_depths):
    states,layers,edges,distance,prefix,suffix = graph(n)
    sorting_depths[n] = distance[0]
    metrics = [image_metrics(image,n) for image in states]
    cone_states,cone_depths,cone_witness = cone_catalogue(n,layers)
    records = []
    cells = {}
    for i,(image,m) in enumerate(zip(states,metrics)):
        cube_bound = sorting_depths[m["largest_cube_dimension"]]
        cone_index = next(ci for ci,cones in enumerate(cone_states)
                          if all((m["rank_determining_set_masks"][n-j-1] >> cones[j])&1
                                 for j in range(n)))
        dependency_bound = cone_depths[cone_index]
        incidence_index = next(ci for ci,cones in enumerate(cone_states)
                               if all(not m["rank_essential_coordinate_masks"][n-j-1] & ~cones[j]
                                      for j in range(n)))
        incidence_bound = cone_depths[incidence_index]
        assert incidence_bound <= dependency_bound
        mono_index = next(ci for ci,cones in enumerate(cone_states)
                         if all((m["rank_monotone_determining_set_masks"][n-j-1] >> cones[j])&1
                                for j in range(n)))
        monotone_dependency_bound = cone_depths[mono_index]
        assert monotone_dependency_bound >= dependency_bound
        assert dependency_bound >= m["support_depth_bound"]
        assert dependency_bound >= m["fanout_depth_bound"]
        bound = max(cube_bound,monotone_dependency_bound)
        assert bound <= distance[i]
        key = (m["largest_cube_dimension"],max(m["rank_minimum_determining_coordinates"]))
        cells.setdefault(key,[]).append(i)
        records.append(dict(image=sorted(image),shortest_prefix=prefix(i),
                            shortest_suffix=suffix(i),prefix_depth=len(prefix(i)),
                            exact_suffix_depth=distance[i],cube_depth_bound=cube_bound,
                            individual_combined_depth_bound=max(cube_bound,m["support_depth_bound"]),
                            two_direction_combined_depth_bound=max(cube_bound,m["support_depth_bound"],m["fanout_depth_bound"]),
                            joint_dependency_depth_bound=dependency_bound,
                            joint_essential_incidence_depth_bound=incidence_bound,
                            joint_monotone_dependency_depth_bound=monotone_dependency_bound,
                            dependency_witness=cone_witness(cone_index),
                            combined_depth_bound=bound,gap=distance[i]-bound,**m))
        # Verify each saved optimal suffix directly on every image element.
        for x in image:
            out = x
            for layer in records[-1]["shortest_suffix"]:
                out = gate_image(out,layer)
            assert out == ((1 << x.bit_count())-1) << (n-x.bit_count())
    stronger = max(range(len(states)),key=lambda i:metrics[i]["support_depth_bound"]-sorting_depths[metrics[i]["largest_cube_dimension"]])
    gap = max(range(len(states)),key=lambda i:records[i]["gap"])
    ambiguous = []
    for key,ids in cells.items():
        lo,hi = min(ids,key=lambda i:distance[i]),max(ids,key=lambda i:distance[i])
        if distance[lo] != distance[hi]:
            ambiguous.append(dict(cube_dimension=key[0],maximum_determining_coordinates=key[1],
                                  minimum_depth=distance[lo],maximum_depth=distance[hi],
                                  easier_image_index=lo,harder_image_index=hi))
    frontier = []
    for t in range(distance[0]+1):
        ids = [i for i,r in enumerate(records) if r["prefix_depth"] <= t]
        frontier.append(dict(prefix_budget=t,minimum_remaining_depth=min(distance[i] for i in ids),
                             minimum_cube_dimension=min(metrics[i]["largest_cube_dimension"] for i in ids),
                             minimum_combined_bound=min(records[i]["combined_depth_bound"] for i in ids)))
    drop = max((records[source]["combined_depth_bound"]-records[target]["combined_depth_bound"],source,li,target)
               for source,successors in enumerate(edges) for li,target in enumerate(successors))
    for source,successors in enumerate(edges):
        for target in successors:
            assert records[source]["joint_essential_incidence_depth_bound"] <= 1+records[target]["joint_essential_incidence_depth_bound"]
    additive_failures = []
    for i,r in enumerate(records):
        w = r["largest_cube_dimension"]
        s = max(r["rank_minimum_determining_coordinates"])
        extra = 0
        while w*(1 << extra)<s:
            extra += 1
        candidate = r["cube_depth_bound"]+extra
        if candidate>r["exact_suffix_depth"]:
            additive_failures.append(dict(image_index=i,candidate_depth=candidate,
                                          exact_suffix_depth=r["exact_suffix_depth"]))
    return dict(wires=n,complete=True,reachable_images=len(states),layers=len(layers),
                exact_full_sorting_depth=distance[0],frontier=frontier,
                dependency_cone_states=len(cone_states),
                incidence_one_layer_drop_checks=len(states)*len(layers),
                images_improved_by_joint_dependency=sum(r["combined_depth_bound"]>r["individual_combined_depth_bound"] for r in records),
                images_improved_by_monotone_cuts=sum(r["joint_monotone_dependency_depth_bound"]>r["joint_dependency_depth_bound"] for r in records),
                images_improved_beyond_fanin_and_fanout=sum(r["combined_depth_bound"]>r["two_direction_combined_depth_bound"] for r in records),
                maximum_combined_bound_layer_drop=drop[0],
                layer_drop_witness=dict(source_image_index=drop[1],layer=layers[drop[2]],target_image_index=drop[3]),
                additive_candidate_counterexamples=additive_failures,
                strongest_support_over_cube_image_index=stronger,largest_gap_image_index=gap,
                maximum_gap=records[gap]["gap"],ambiguous_metric_cells=ambiguous,
                records=records)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",required=True)
    args = parser.parse_args()
    depths = {0:0,1:0}
    result = dict(cases=[probe(n,depths) for n in (2,3,4,5)],
                  status="Exact finite image graph and completion distances; derived residual bounds, not Lean checked; no improved universal coefficient")
    with open(args.output,"w",encoding="utf-8") as handle:
        json.dump(result,handle,indent=2)
        handle.write("\n")
    print(json.dumps([dict(wires=c["wires"],images=c["reachable_images"],
                           full_depth=c["exact_full_sorting_depth"],maximum_gap=c["maximum_gap"],
                           frontier=c["frontier"]) for c in result["cases"]],indent=2))
