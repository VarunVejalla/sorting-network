#!/usr/bin/env python3
"""Shared-state local-context certificate screen for D2 receiver fan-in.

For each reachable parent-state type and stage, examine its 8 child receiver
contexts.  The source pieces are the parent's down port, the receiver's
retained bag when inactive, and active grandchildren's up ports.  Static
addresses are joined to the next receiver bag and grouped by its local
4096x64 tile.  Translation invariance makes one parent occurrence sufficient
when native sizes are multiples of 4096.  Diagnostic only: it does not prove
the all-depth state/phase bound or any key-error recurrence.
"""
from collections import defaultdict
import argparse

from flow_dag import FlowDAG
from oracle import Par

CELL = 4096
TILE_CELLS = 64
TILE = CELL * TILE_CELLS


def port_cells(flow, node, idx, lo, hi, label):
    """Aligned global-cell runs tagged by source sender-local physical tile."""
    out=[]
    rank=0
    for a,b in flow.bag_intervals(node,idx):
        left,right=max(lo,rank),min(hi,rank+b-a)
        if left<right:
            ga,gb=a+left-rank,a+right-rank
            assert ga%CELL==gb%CELL==left%CELL==right%CELL==0, (node,idx,lo,hi,a,b,rank)
            c,stop=ga//CELL,gb//CELL
            local=left//CELL
            while c<stop:
                tile=local//TILE_CELLS
                take=min(stop-c,TILE_CELLS-local%TILE_CELLS)
                out.append((c,c+take,(label,node,tile)))
                c+=take; local+=take
        rank+=b-a
    assert hi<=rank
    return out


def whole_target_tiles(flow,node,idx):
    out=[]
    rank=0
    for a,b in flow.bag_intervals(node,idx):
        assert a%CELL==b%CELL==0
        c,stop=a//CELL,b//CELL
        local=rank//CELL
        while c<stop:
            tile=local//TILE_CELLS
            take=min(stop-c,TILE_CELLS-local%TILE_CELLS)
            out.append((c,c+take,tile))
            c+=take; local+=take
        rank+=b-a
    return out


def receiver_sources(flow,t,parent,j):
    """Return this receiver's source-cell runs and target tile runs."""
    p=flow.p
    plevel,_,_,_,children=flow.nodes[parent]
    receiver=children[j]
    sources=[]

    # Parent sender's down port into child j.
    prow=flow.rows[t].get(parent)
    if prow is not None:
        a,pi,blocks=prow
        if pi<a:
            start=pi//2+sum(blocks[:j])
            stop=start+blocks[j]
            sources += port_cells(flow,parent,0,start,stop,'parent')

    # An inactive receiver keeps its own sender bag.
    if receiver not in flow.rows[t]:
        a=flow.allocation(receiver)
        sources += port_cells(flow,receiver,j,0,a,'self')

    # Each active child sends its two up ports to this receiver.
    grandchildren=flow.nodes[receiver][4]
    for k,child in enumerate(grandchildren):
        row=flow.rows[t].get(child)
        if row is None:
            continue
        a,pi,_=row
        if pi==a:
            sources += port_cells(flow,child,j*p.k+k,0,a,('child',k))
        else:
            half=pi//2
            sources += port_cells(flow,child,j*p.k+k,0,half,('child',k))
            sources += port_cells(flow,child,j*p.k+k,a-half,a,('child',k))

    # Parent cuts can overwrite the receiver root after its own recursive
    # update, so read the receiver from the updated parent, not its local
    # transition entry.
    updated=flow.nodes[flow.transitions[t][parent]][4][j]
    target=whole_target_tiles(flow,updated,j)
    sources.sort()
    target.sort()
    return sources,target


def root_sources(flow,t):
    """Root receiver has no parent contribution."""
    receiver=flow.roots[t]
    sources=[]
    if receiver not in flow.rows[t]:
        sources += port_cells(flow,receiver,0,0,flow.allocation(receiver),'self')
    for k,child in enumerate(flow.nodes[receiver][4]):
        row=flow.rows[t].get(child)
        if row is None: continue
        a,pi,_=row
        if pi==a:
            sources += port_cells(flow,child,k,0,a,('child',k))
        else:
            half=pi//2
            sources += port_cells(flow,child,k,0,half,('child',k))
            sources += port_cells(flow,child,k,a-half,a,('child',k))
    target=whole_target_tiles(flow,flow.roots[t+1],0)
    sources.sort(); target.sort()
    return sources,target


def routing_summary(sources,target):
    """Return max fan-in witness and both tile-incidence degrees."""
    incoming=defaultdict(set)
    outgoing=defaultdict(set)
    i=j=0
    while i<len(sources) and j<len(target):
        slo,shi,source=sources[i]
        tlo,thi,dest=target[j]
        lo,hi=max(slo,tlo),min(shi,thi)
        if lo<hi:
            incoming[dest].add(source)
            outgoing[source].add(dest)
        end=min(shi,thi)
        if end==shi: i+=1
        if end==thi: j+=1
    assert i==len(sources) and j==len(target),(i,j,len(sources),len(target))
    if not incoming:
        return 0, None, (), 0, 0
    dest,sources=max(incoming.items(),key=lambda item: len(item[1]))
    return (len(sources),dest,tuple(sorted(sources,key=repr)),
            max(map(len,outgoing.values()),default=0),
            max(map(len,incoming.values()),default=0))


def check(depth,scale,params):
    flow=FlowDAG(depth,scale=scale,p=Par(*params)).build()
    stage_rows=[]
    for t in range(len(flow.rows)):
        reachable=flow.reachable(t)
        best=(0,None)
        max_out=max_in=0
        root_value=routing_summary(*root_sources(flow,t))
        best=(root_value[0],('root',flow.roots[t],root_value[1],root_value[2]))
        max_out=max(max_out,root_value[3]); max_in=max(max_in,root_value[4])
        for parent in reachable:
            lev=flow.nodes[parent][0]
            if lev>=depth: continue
            for j in range(flow.p.k):
                sources,target=receiver_sources(flow,t,parent,j)
                try:
                    value=routing_summary(sources,target)
                except AssertionError as error:
                    raise AssertionError((t, parent, lev, j, sources[:3], target[:3], error))
                max_out=max(max_out,value[3]); max_in=max(max_in,value[4])
                if value[0]>best[0]:
                    best=(value[0],(lev,parent,j,len(sources),len(target),value[1],value[2]))
        stage_rows.append((t,best,max_out,max_in))
    return len(flow.rows),len(flow.nodes),stage_rows


if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--depths',nargs='+',type=int,default=[5,6,7])
    ap.add_argument('--scale',type=int,default=8192)
    ap.add_argument('--params',nargs=3,type=int,default=(3,3,2))
    args=ap.parse_args()
    for d in args.depths:
        stages,states,rows=check(d,args.scale,args.params)
        print(f'd={d} scale={args.scale}: stages={stages}, DAG nodes={states}',flush=True)
        print('stage, max incoming sources, witness, max source fanout:',
              [(t,v[0],v[1],max_out) for t,v,max_out,_ in rows],flush=True)
        print('max source/target incidence degree by stage:',
              [(t,max_out,max_in) for t,_,max_out,max_in in rows],flush=True)
