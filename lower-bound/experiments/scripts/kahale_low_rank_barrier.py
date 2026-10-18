"""Exact low-rank selector checks and a standalone-potential ceiling."""
from math import ceil, log2
from pathlib import Path
import json
from kahale_image_difficulty import gate_image, graph


def maximum_tournament(wires):
    """Disjoint adjacent groups; each representative is its largest index."""
    representatives=list(wires)
    layers=[]
    while len(representatives)>1:
        layer=tuple((representatives[i],representatives[i+1])
                    for i in range(0,len(representatives)-1,2))
        representatives=[representatives[i+1] for i in range(0,len(representatives)-1,2)]+(
            representatives[-1:] if len(representatives)%2 else [])
        layers.append(layer)
    return layers


def select_largest(n,r):
    return [layer for j in range(min(n,r)) for layer in maximum_tournament(range(n-j))]


def run(x,layers):
    for layer in layers:
        x=gate_image(x,layer)
    return x


def main():
    checks=[]
    for n in range(2,13):
        for r in range(1,min(n,3)+1):
            layers=select_largest(n,r)
            assert len(layers)<=r*ceil(log2(n))
            for layer in layers:
                wires=[i for pair in layer for i in pair]
                assert len(wires)==len(set(wires)) and all(a<b for a,b in layer)
            checked=0
            for x in range(1<<n):
                if x.bit_count()>r:
                    continue
                assert run(x,layers)==((1<<x.bit_count())-1)<<(n-x.bit_count())
                checked+=1
            checks.append(dict(wires=n,selected=r,depth=len(layers),input_checks=checked))
    examples=[]
    hidden_cubes=[]
    for n in range(4,11):
        star=[((i,n-1),) for i in range(n-1)]+[((i,n-2),) for i in range(n-2)]
        image={run(x,star) for x in range(1<<n)}
        top_two=3<<(n-2)
        expected={0,1<<(n-1)}|{top_two|u for u in range(1<<(n-2))}
        assert image==expected
        assert all(run(x,star)==((1<<x.bit_count())-1)<<(n-x.bit_count())
                   for x in range(1<<n) if x.bit_count()<=2)
        hidden_cubes.append(dict(wires=n,prefix_depth=len(star),hidden_cube_dimension=n-2))
    for n in (4,5):
        images,_,_,actual,prefix,suffix=graph(n)
        terminal={1<<(n-1),3<<(n-2)}
        candidates=[i for i,R in enumerate(images) if {x for x in R if x.bit_count() in (1,2)}==terminal]
        i=max(candidates,key=lambda i:actual[i])
        examples.append(dict(wires=n,pair_terminal_images=len(candidates),
            maximum_remaining_depth=actual[i],image=sorted(images[i]),prefix=prefix(i),suffix=suffix(i)))
    result=dict(selector_checks=checks,pair_terminal_examples=examples,star_hidden_cube_checks=hidden_cubes,
        status='Exact finite checks of a derived general selector argument; no Lean or improved coefficient')
    root=Path(__file__).resolve().parents[3]
    (root/'docs/kahale-low-rank-barrier-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(selector_cases=len(checks),total_input_checks=sum(c['input_checks'] for c in checks),
                         pair_terminal_examples=examples),indent=2))


if __name__=='__main__':
    main()
