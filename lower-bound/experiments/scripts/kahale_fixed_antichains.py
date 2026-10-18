"""Small exact search of fixed-input antichains in equal-height prefixes."""
import argparse
import json

from kahale_layer_occupation import matchings


def width(reach,n):
    return max(s.bit_count() for s in range(1 << n)
               if all(not (s & reach[i]) for i in range(n) if (s >> i)&1))


def probe(n,depth,cap):
    # Only height and accumulated comparator order are needed for this screen.
    # All reachable states are actual prefixes; this is not a sorting test.
    states = {((0,)*n,(0,)*n): []}
    layers = list(matchings(list(range(n))))
    rows = []
    for stage in range(1,depth+1):
        out = {}
        complete = True
        for (heights,reach),path in states.items():
            for layer in layers:
                if any(heights[a] != heights[b] for a,b in layer):
                    continue
                h,r = list(heights),list(reach)
                for a,b in layer:
                    h[b] += 1
                    r[a] |= 1 << b
                for middle in range(n-1,-1,-1):
                    for i in range(middle):
                        if (r[i] >> middle)&1:
                            r[i] |= r[middle]
                key = tuple(h),tuple(r)
                if key not in out:
                    if len(out) >= cap:
                        complete = False
                        break
                    out[key] = path+[layer]
            if not complete:
                break
        best = min(out,key=lambda key:width(key[1],n))
        rows.append(dict(depth=stage,states=len(out),complete=complete,
                         minimum_poset_width=width(best[1],n),witness=out[best]))
        if not complete:
            break
        states = out
    return dict(wires=n,stages=rows,status="Exact finite height/poset search; not a sorting or universal depth theorem")


def image_probe(n,depth,cap,perfect=False):
    initial = tuple(sum(((x >> i)&1) << x for x in range(1 << n)) for i in range(n))
    states = {((0,)*n,initial): []}
    layers = [layer for layer in matchings(list(range(n))) if not perfect or len(layer)*2 == n]
    cache = {}

    def largest_cube(state):
        image = frozenset(sum(((f >> x)&1) << i for i,f in enumerate(state))
                          for x in range(1 << n))
        if image not in cache:
            best = (0,0,0)
            for free in range(1 << n):
                size = free.bit_count()
                if size <= best[0]:
                    continue
                fixed = ((1 << n)-1)^free
                counts = {}
                for x in image:
                    key = x & fixed
                    counts[key] = counts.get(key,0)+1
                for assignment,count in counts.items():
                    if count == 1 << size:
                        best = size,free,assignment
                        break
            cache[image] = best
        return cache[image]

    rows = []
    for stage in range(1,depth+1):
        out = {}
        complete = True
        for (heights,state),path in states.items():
            for layer in layers:
                if any(heights[a] != heights[b] for a,b in layer):
                    continue
                h,f = list(heights),list(state)
                for a,b in layer:
                    h[b] += 1
                    f[a],f[b] = state[a]&state[b],state[a]|state[b]
                key = tuple(h),tuple(f)
                if key not in out:
                    if len(out) >= cap:
                        complete = False
                        break
                    out[key] = path+[layer]
            if not complete:
                break
        best = min(out,key=lambda key:largest_cube(key[1])[0])
        dimension,free,fixed = largest_cube(best[1])
        rows.append(dict(depth=stage,states=len(out),complete=complete,
                         minimum_largest_image_cube_dimension=dimension,
                         witness=out[best],witness_free_mask=free,witness_fixed_ones=fixed))
        if not complete:
            break
        states = out
    return dict(wires=n,perfect_layers_only=perfect,stages=rows,
                status="Exact Boolean image-cube enumeration; incomplete searches cannot establish a minimum")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",required=True)
    parser.add_argument("--cap",type=int,default=200000)
    args = parser.parse_args()
    result = dict(fixed_poset_antichains=[probe(n,3,args.cap) for n in (4,5,6)],
                  output_image_cubes=[image_probe(n,3,args.cap) for n in (4,5,6)]
                                    +[image_probe(8,3,args.cap,perfect=True)])
    with open(args.output,"w",encoding="utf-8") as handle:
        json.dump(result,handle,indent=2)
        handle.write("\n")
    print(json.dumps(result,indent=2))
