"""Produce/replay an integer separation witness for a saved cut-loop extremizer.

Replay verifies outside-convex-hull status independently of optimization status:
all reachable middles satisfy w.y<=H(w), and the target violates this inequality.
A failed separation search does not certify convex-hull membership.
"""
import argparse
import json
from pathlib import Path
import numpy as np
from d2_joint_reachable_gate import support_dp,advance_many


def verify(doc):
    perm=np.array(doc['round1'],dtype=np.int64)
    m,n=perm.shape
    assert all(sorted(row.tolist())==list(range(n)) for row in perm)
    y=np.array(doc['target'],dtype=np.int64)
    w=np.array(doc['weights'],dtype=np.int64)
    M=int(doc['mass'])
    assert len(y)==len(w)==n and y.sum()==M and (y>=0).all() and (y<=m).all()
    cap=support_dp(perm,w,M)
    assert cap==doc['cap']
    gap=int(w@y-cap)
    assert gap==doc['gap'] and gap>0
    print(json.dumps(dict(status='exact_integer_separation_verified',cap=cap,
                          target_value=int(w@y),gap=gap)))


def generate(a):
    from d2_bulk_attack import Stage
    from d2_joint_cut_loop import master,separate
    r=json.loads(Path(a.source).read_text())[a.index]
    st=Stage(r['columns'],r['rows'],r['seed'])
    cuts=[(np.array(c['weights'],dtype=np.int64),c['cap']) for c in r['cuts']]
    y,info=master(st,r['mass'],cuts,a.seconds)
    cut,sep=separate(st.s1,y,r['mass'],strong=a.strong)
    if cut is None:
        raise RuntimeError('No cut found; this is not a convex-hull membership certificate: '+str(sep))
    w,cap=cut
    doc=dict(round1=st.s1.tolist(),round2=st.s2.tolist(),mass=r['mass'],
             target=y.tolist(),weights=w.tolist(),cap=cap,gap=int(w@y-cap),
             numerical_master=info,numerical_separation=sep,
             note='exact outside-hull witness for this target; no claim about all maximizers')
    Path(a.output).write_text(json.dumps(doc,indent=2)+'\n')
    verify(doc)


def main():
    p=argparse.ArgumentParser(description=__doc__); sub=p.add_subparsers(dest='cmd',required=True)
    g=sub.add_parser('generate');g.add_argument('source');g.add_argument('--index',type=int,default=0)
    g.add_argument('--seconds',type=float,default=10);g.add_argument('--strong',action='store_true')
    g.add_argument('--output',required=True)
    v=sub.add_parser('verify');v.add_argument('certificate')
    a=p.parse_args()
    if a.cmd=='generate':generate(a)
    else:verify(json.loads(Path(a.certificate).read_text()))

if __name__=='__main__':main()
