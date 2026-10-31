#!/usr/bin/env python3
"""Exact D2 flow with identical subtrees shared, without enumerating k**d bags.

Nodes store (level, deficit, low deficit, high deficit, child IDs). Updates
use the same integer interval cuts as slackfree/explicit.py. This is research
instrumentation, not a uniform proof of any shape or sorting property.
"""
from functools import lru_cache
from oracle import Par


class FlowDAG:
    def __init__(self,d,scale=1,p=None,sparse_bottom=False):
        self.d=d; self.scale=scale; self.p=p or Par(2,3,2)
        self.sparse_bottom=sparse_bottom
        self.nodes=[]; self.intern={}; self.roots=[]; self.rows=[]; self.transitions=[]
        @lru_cache(None)
        def initial(lev):
            children=(initial(lev+1),)*self.p.k if lev<d else ()
            return self.make(lev,0 if lev==0 else self.native(lev),0,0,children)
        self.roots.append(initial(0))

    def native(self,lev):
        return self.scale*self.p.k**(self.d-lev)

    def make(self,lev,G,low,high,children):
        key=(lev,G,low,high,tuple(children))
        if key not in self.intern:
            self.intern[key]=len(self.nodes); self.nodes.append(key)
        return self.intern[key]

    def allocation(self,node):
        lev,G,_,_,children=self.nodes[node]
        return (sum(self.nodes[c][1] for c in children) if children else
                self.native(lev))-G

    def step(self):
        t=len(self.rows); rows={}; transitions={}; p=self.p
        @lru_cache(None)
        def update(node):
            lev,G,low,high,children=self.nodes[node]
            newchildren=[update(c) for c in children]
            if not ((lev==0) if t==0 else p.active(self.d,lev,t)):
                out=self.make(lev,G,low,high,newchildren)
                transitions[node]=out
                return out
            a=self.allocation(node)
            assert a>=0 and low+high==G,(t,lev,a,G,low,high)
            role='topDesc' if t==0 else p.role(self.d,lev,t)
            if role=='botRise':
                pi=a; blocks=[0]*len(children)
            else:
                raw=0 if t==0 else self.scale*p.up(self.d,lev,t)
                assert int(raw)==raw
                pi=int(raw)
                # In a sparse-bottom D2 node, the formula's upward quota can
                # exceed its current allocation. Send the whole bag upward;
                # the two cut fronts then meet and fully clear its child ranges.
                if self.sparse_bottom and pi >= a:
                    pi=a
                U=[self.nodes[c][1] for c in children]
                if role=='topDesc':
                    cuts=[(0,0)]*len(children)
                else:
                    assert pi%2==0
                    left=low+pi//2; right=sum(U)-high-pi//2; pos=0; cuts=[]
                    assert left<=right, (t, lev, a, pi, left, right,
                                         low, high, sum(U), role)
                    for u in U:
                        end=pos+u
                        cuts.append((max(0,min(end,left)-pos),
                                     max(0,end-max(pos,right))))
                        pos=end
                blocks=[]
                for j,(cl,ch) in enumerate(cuts):
                    blocks.append(U[j]-cl-ch)
                    clev,_,_,_,grandchildren=self.nodes[newchildren[j]]
                    newchildren[j]=self.make(clev,cl+ch,cl,ch,grandchildren)
            assert all(b>=0 for b in blocks) and sum(blocks)+pi==a
            rows[node]=(a,pi,blocks)
            out=self.make(lev,G+pi,low+pi//2,high+pi-pi//2,newchildren)
            transitions[node]=out
            return out
        self.roots.append(update(self.roots[-1])); self.rows.append(rows)
        self.transitions.append(transitions)

    def build(self,horizon=None):
        stop=self.p.tf(self.d) if horizon is None else min(horizon,self.p.tf(self.d))
        while len(self.rows)<stop:
            self.step()
        return self

    def lookup(self,t,lev,idx):
        node=self.roots[t]
        for power in range(lev-1,-1,-1):
            node=self.nodes[node][4][idx//self.p.k**power%self.p.k]
        return node

    def row(self,t,lev,idx):
        return self.rows[t][self.lookup(t,lev,idx)]

    def subtree_interval(self,node,idx):
        lev,G,low,high,_=self.nodes[node]; R=self.native(lev)
        if G==R:
            return None
        assert 0<=G<R and low+high==G
        return idx*R+low,(idx+1)*R-high

    def bag_intervals(self,node,idx):
        whole=self.subtree_interval(node,idx)
        if whole is None:
            assert self.allocation(node)==0
            return []
        pos,end=whole; out=[]
        for j,child in enumerate(self.nodes[node][4]):
            occupied=self.subtree_interval(child,idx*self.p.k+j)
            if occupied is None:
                continue
            lo,hi=occupied
            assert pos<=lo<=hi<=end
            if pos<lo:
                out.append((pos,lo))
            pos=hi
        if pos<end:
            out.append((pos,end))
        assert sum(hi-lo for lo,hi in out)==self.allocation(node)
        return out

    def reachable(self,t):
        todo=[self.roots[t]]; seen=set()
        while todo:
            node=todo.pop()
            if node not in seen:
                seen.add(node); todo.extend(self.nodes[node][4])
        return seen


if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser(); ap.add_argument('--depth',type=int,default=40)
    ap.add_argument('--compare-explicit',type=int,metavar='MAX_DEPTH',
                    help='compare every active row against the independent explicit table')
    args=ap.parse_args(); flow=FlowDAG(args.depth).build()
    if args.compare_explicit is not None:
        from explicit import build_table
        count=0
        for d in range(3,args.compare_explicit+1):
            candidate=FlowDAG(d).build()
            table,_,_=build_table(candidate.p,d,'D2')
            for t,step in enumerate(table):
                for lev,rows in step.items():
                    for idx,row in enumerate(rows):
                        assert candidate.row(t,lev,idx)==row,(d,t,lev,idx)
                        count+=1
        print(f'{count} exact active rows matched the explicit table')
    for node in flow.reachable(len(flow.rows)):
        a=flow.allocation(node)
        if a:
            R=flow.native(flow.nodes[node][0])
            assert flow.bag_intervals(node,0)==[(0,R)]
    print(f'd={args.depth}: {len(flow.rows)} stages, {len(flow.nodes)} shared states; '
          'terminal native intervals checked for every reachable state type')
