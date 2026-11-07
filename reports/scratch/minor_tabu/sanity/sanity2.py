#!/usr/bin/env python3
"""The walk itself: certified graphs at 50-80 vertices, where the whole graph cannot be refuted in 3,000 nodes
but a minor of the full width can.  Seeded from a random bad minor (contractions to 0.6 n; its exact pathwidth is
the floor).  B: 20 s walk, -b 3000 (climb) -nb 3000 (neighbour test).  C: the same with 0 s (no steps).
Reports how often the floor reaches the width, by what certificate, and how far short otherwise."""
import gzip, json, random, subprocess, sys, csv, collections, tempfile
from concurrent.futures import ThreadPoolExecutor
import networkx as nx
CLI='pathwidth_solver/cli/minor_tabu'; PW='pathwidth_solver/cli/pathwidth'
rnd=random.Random(2); rows=[]
for line in gzip.open('paper1/data/dataset/pathwidth_dataset.jsonl.gz','rt'):
    d=json.loads(line)
    if 50<=d['n']<=80 and d['width']>=4 and d['provenance'].startswith('certified') and any('rome' in str(m.get('source','')) for m in d['members']):
        rows.append(d)
rnd.shuffle(rows); rows=rows[:int(sys.argv[1]) if len(sys.argv)>1 else 100]
def tabu(G, w, L, pairs, t, extra):
    g6=nx.to_graph6_bytes(G,header=False)
    sf=tempfile.NamedTemporaryFile('w',suffix='.seed',delete=False); sf.write(''.join(f'{a} {b}\n' for a,b in pairs)); sf.close()
    cmd=['nice','-n','19',CLI,'-t',str(t),'-w',str(w),'-L',str(L),'-c','7','-s','1','-seed',sf.name]+extra
    p=subprocess.run(cmd,input=g6,capture_output=True,timeout=t*3+60); out=p.stdout.decode().strip().splitlines()
    return json.loads(out[-1]) if out else {}
def exact_pw(H):
    g6=nx.to_graph6_bytes(nx.convert_node_labels_to_integers(H),header=False)
    o=subprocess.run(['nice','-n','19',PW,'-t','120'],input=g6,capture_output=True).stdout.decode().split()
    return int(o[1]) if len(o)>=3 and o[2] in ('refutation','bound','minor') else None
def one(d):
    G=nx.Graph(); G.add_nodes_from(range(d['n'])); G.add_edges_from(map(tuple,d['edges'])); w=d['width']; n=d['n']
    H=G.copy(); pairs=[]; r=random.Random(d['id'])
    while H.number_of_nodes()>int(0.6*n):
        a,b=r.choice(list(H.edges())); pairs.append((a,b)); H=nx.contracted_nodes(H,b,a,self_loops=False)
    L=exact_pw(H)
    if L is None: return None
    ex=['-b','3000','-nb','3000','-nt','0.5','-lo','0.2','-hi','0.95','-m','1000']
    B=tabu(G,w,L,pairs,20,ex); C=tabu(G,w,L,pairs,0,ex)
    return dict(id=d['id'],n=n,width=w,seed_minor=H.number_of_nodes(),seed_pw=L,C_floor=C.get('floor'),B_floor=B.get('floor'),B_kind=B.get('kind'),B_minor=B.get('minor_vertices'),B_steps=B.get('steps'),B_calls=B.get('exact_calls'))
with ThreadPoolExecutor(8) as ex: res=[x for x in ex.map(one,rows) if x]
with open('reports/scratch/minor_tabu/sanity/sanity2.csv','w',newline='') as f:
    wr=csv.DictWriter(f,fieldnames=list(res[0].keys())); wr.writeheader(); wr.writerows(res)
N=len(res); print(f'{N} Rome graphs, n {min(x["n"] for x in res)}-{max(x["n"] for x in res)}, width {min(x["width"] for x in res)}-{max(x["width"] for x in res)}')
print('SOUNDNESS: floor above certified width:', sum(x['B_floor']>x['width'] for x in res))
print(f'seed floor == width on {sum(x["seed_pw"]==x["width"] for x in res)}; control (no steps) reaches width on {sum(x["C_floor"]==x["width"] for x in res)}; the walk reaches width on {sum(x["B_floor"]==x["width"] for x in res)}')
up=[x for x in res if x['B_floor']>x['C_floor']]
print(f'walk raised the floor above the control on {len(up)}: certificate a proper minor on {sum(x["B_minor"]<x["n"] for x in up)}, minor size / n median {sorted(x["B_minor"]/x["n"] for x in up)[len(up)//2] if up else None}, steps median {sorted(x["B_steps"] for x in up)[len(up)//2] if up else None}')
print('width - floor after the walk:', dict(sorted(collections.Counter(x['width']-x['B_floor'] for x in res).items())))
print('kinds', dict(collections.Counter(x['B_kind'] for x in res)))
