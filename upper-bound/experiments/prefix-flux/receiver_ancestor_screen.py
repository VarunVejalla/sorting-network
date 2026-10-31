#!/usr/bin/env python3
"""Finite backward-cone screen for the D2 source-tile routing graph.

This asks the key terminal question after the one-step fan-in screen: how many
earlier physical tiles can contribute to a fixed terminal tile after several
schedule transitions?  A small cone would turn bounded local profile error
into a logarithmic terminal error; an expanding cone rejects that shortcut.
The screen is exact for the enumerated FlowDAG, not an all-depth theorem.
"""
from collections import defaultdict
import argparse

from flow_dag import FlowDAG
from oracle import Par
from receiver_fiber_screen import owner_runs


def source_map(source,target):
    incoming=defaultdict(set)
    i=j=0
    while i<len(source) and j<len(target):
        slo,shi,skey=source[i]
        tlo,thi,tkey=target[j]
        if max(slo,tlo)<min(shi,thi): incoming[tkey].add(skey)
        end=min(shi,thi)
        if end==shi: i+=1
        if end==thi: j+=1
    assert i==len(source) and j==len(target)
    return incoming


def screen(depth,scale,params):
    flow=FlowDAG(depth,scale=scale,p=Par(*params)).build()
    maps=[]
    ids=None
    for t in range(len(flow.rows)):
        src=owner_runs(flow,t); dst=owner_runs(flow,t+1)
        if ids is None: ids=set(x[2] for x in src)
        maps.append(source_map(src,dst))
    final=set(x[2] for x in owner_runs(flow,len(flow.rows)))
    # For every final tile, maintain its exact set of ancestors at the current
    # reverse time. Record cone sizes after each transition.
    cones={x:{x} for x in final}
    profile=[(0,max(map(len,cones.values()),default=0))]
    for t in range(len(maps)-1,-1,-1):
        prev={}
        for terminal,current in cones.items():
            anc=set()
            for dest in current:
                anc.update(maps[t].get(dest,()))
            prev[terminal]=anc
        cones=prev
        profile.append((len(maps)-t,max(map(len,cones.values()),default=0)))
    return len(flow.rows),len(flow.nodes),len(final),profile


if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--depths',nargs='+',type=int,default=[5,6,7])
    ap.add_argument('--scale',type=int,default=8192)
    ap.add_argument('--params',nargs=3,type=int,default=(3,3,2))
    args=ap.parse_args()
    for d in args.depths:
        stages,nodes,tiles,profile=screen(d,args.scale,args.params)
        print(f'd={d}: stages={stages}, DAG nodes={nodes}, terminal tiles={tiles}',flush=True)
        print('max ancestor tiles by backward transitions:',profile,flush=True)
