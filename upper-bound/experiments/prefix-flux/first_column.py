#!/usr/bin/env python3
"""Exact first column sort on an RLE word, without allocating its wires.

Layout: L full rows, with r extra cells in columns [0,r) after row L//2.
One means a zero key, as in oracle.py. This is a deterministic reachable-state
restriction of the proposed centered-ragged core, not a sorting proof.
"""
from oracle import normalize_word,dominates


def minimum_rectangular_prefix_zeros(total,zeros,cut,rows=4096):
    """Minimum zeros in a row-major prefix after sorting each column.

    The minimum ranges over every input placement with the given total. The
    exact rectangular layout is required; later ascending comparators can
    only increase this prefix count.
    """
    assert total%rows==0 and 0<=zeros<=total
    columns=total//rows; cut=max(0,min(total,cut))
    full,partial=divmod(cut,columns)
    if full==rows: return zeros
    if partial==0:
        # With a whole-row prefix, a column of height h contributes
        # min(h,full) zeros to that prefix. To store `zeros` total zeros with
        # minimum prefix mass, fill floor(zeros/rows) columns completely,
        # then put the remainder in one column. The general inverse-envelope
        # search below is unnecessary in this common case.
        whole,remainder=divmod(zeros,rows)
        return whole*full+min(remainder,full)
    low_columns=columns-partial

    def max_zeros_with_prefix_budget(budget):
        """Maximum total zeros with at most `budget` prefix zeros.

        A column of prefix height h either stays unsaturated, storing x<=h
        zeros at prefix cost x, or is saturated, storing all `rows` zeros at
        cost h. Saturation has the best gain/cost for smaller h, so use the
        full-height columns (height `full`) before the `partial` columns
        (height `full+1`); spend leftover budget in unsaturated columns.
        """
        mass=0
        if full==0:
            # Columns beyond the cut can be filled at zero prefix cost.
            mass=rows*low_columns
            low_saturated=low_columns
            used=0
        else:
            low_saturated=min(low_columns,budget//full)
            mass=rows*low_saturated
            used=full*low_saturated
        remaining=budget-used
        high_saturated=min(partial,remaining//(full+1))
        mass+=rows*high_saturated
        remaining-=(full+1)*high_saturated
        capacity=(low_columns-low_saturated)*full+(partial-high_saturated)*(full+1)
        return mass+min(remaining,capacity)

    # Invert the monotone maximum-mass envelope. This is logarithmic in the
    # prefix size instead of scanning every column, which matters at depth d
    # where the root rectangle has k**d columns.
    lo,hi=0,cut
    while lo<hi:
        mid=(lo+hi)//2
        if max_zeros_with_prefix_budget(mid)>=zeros:
            hi=mid
        else:
            lo=mid+1
    return lo


def first_column(word,q=12):
    a=sum(length for length,_ in word)
    assert a>0
    n=(a+(1<<q)-1)//(1<<q)
    L,r=divmod(a,n); b=L//2; middle=b*n
    events={0:0,n:0,r:0}

    def add(lo,hi,value):
        if lo<hi:
            events[lo]=events.get(lo,0)+value
            events[hi]=events.get(hi,0)-value

    def rectangular(lo,hi):
        length=hi-lo
        if length<=0: return
        count,tail=divmod(length,n); start=lo%n
        add(0,n,count)
        add(start,min(n,start+tail),1)
        add(0,max(0,start+tail-n),1)

    pos=0
    for length,marked in word:
        end=pos+length
        if marked:
            rectangular(pos,min(end,middle))
            add(max(pos,middle)-middle,min(end,middle+r)-middle,1)
            rectangular(max(pos,middle+r)-r,end-r)
        pos=end
    cuts=sorted(events); heights=[]; value=0
    for lo,hi in zip(cuts,cuts[1:]):
        value+=events[lo]
        if lo<hi:
            assert 0<=value<=L+(lo<r)
            if heights and heights[-1][2]==value and lo!=r:
                heights[-1]=(heights[-1][0],hi,value)
            else: heights.append((lo,hi,value))
    output=[]

    def emit(length,bit):
        if not length: return
        if output and output[-1][1]==bit:
            output[-1]=(output[-1][0]+length,bit)
        else: output.append((length,bit))

    for row in range(L):
        if row==b and r:
            for lo,hi,height in heights:
                if lo<r: emit(min(hi,r)-lo,int(b<height))
        for lo,hi,height in heights:
            rank=row+int(row>=b and lo<r)
            emit(hi-lo,int(rank<height))
    assert sum(k for k,_ in output)==a
    assert sum(k*v for k,v in output)==sum(k*v for k,v in word)
    assert dominates(output,word)
    return output


def self_check():
    """Independent literal-column comparison, exhaustive small/random larger."""
    import itertools,random
    rng=random.Random(0); count=0
    cases=((list(bits),2) for a in range(1,13)
           for bits in itertools.product((0,1),repeat=a))
    random_cases=(( [rng.randrange(2) for _ in range(rng.randrange(20,2000))],
                   rng.randrange(2,10)) for _ in range(300))
    for bits,q in itertools.chain(cases,random_cases):
        a=len(bits); n=(a+(1<<q)-1)//(1<<q); L,r=divmod(a,n); b=L//2
        columns=[[] for _ in range(n)]; indices=[]
        for row in range(L):
            if row==b: indices.extend(range(r))
            indices.extend(range(n))
        for bit,j in zip(bits,indices): columns[j].append(bit)
        columns=[sorted(c,reverse=True) for c in columns]; used=[0]*n; expected=[]
        for j in indices:
            expected.append(columns[j][used[j]]); used[j]+=1
        actual=first_column(normalize_word([(1,v) for v in bits]),q)
        assert actual==normalize_word([(1,v) for v in expected])
        count+=1
    print(f'{count} literal-column comparisons passed')


def minimum_bound_self_check():
    """Compare the formula with all column-count vectors on tiny rectangles."""
    from itertools import product
    checks=0
    for rows in range(1,5):
        for columns in range(1,5):
            total=rows*columns
            vectors=list(product(range(rows+1),repeat=columns))
            for zeros in range(total+1):
                feasible=[v for v in vectors if sum(v)==zeros]
                for cut in range(total+1):
                    k,s=divmod(cut,columns)
                    brute=min(sum(min(v[j],k+int(j<s))
                                  for j in range(columns)) for v in feasible)
                    assert minimum_rectangular_prefix_zeros(
                        total,zeros,cut,rows
                    )==brute,(rows,columns,zeros,cut,brute)
                    checks+=1
    print(f'{checks} exact column-count lower bounds passed')


if __name__=='__main__':
    self_check()
    minimum_bound_self_check()
