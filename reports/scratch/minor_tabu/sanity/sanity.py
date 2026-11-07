#!/usr/bin/env python3
"""Does the tabu walk itself find certificates?  Small graphs of certified pathwidth from the dataset.

A. unseeded, default budgets, 10 s: output floor == certified width?  (soundness: never above it)
B. the walk must do the work: seeded from a deliberately bad minor (random contractions to 0.6 n, whose
   exact pathwidth is the floor), the whole-graph climb crippled (-b 50 nodes), 10 s: does the floor
   reach the width?  Control: the same with budget 0 s (no steps), i.e. the seed's floor alone.
"""
import gzip, json, random, subprocess, sys, csv, collections
from concurrent.futures import ThreadPoolExecutor
import networkx as nx
CLI='pathwidth_solver/cli/minor_tabu'; PW='pathwidth_solver/cli/pathwidth'
rnd=random.Random(1); rows=[]
for line in gzip.open('paper1/data/dataset/pathwidth_dataset.jsonl.gz','rt'):
    d=json.loads(line)
    if 14<=d['n']<=36 and d['width']>=3 and d['provenance'].startswith('certified') and d['m']<d['n']*(d['n']-1)//2:
        rows.append(d)
rnd.shuffle(rows); rows=rows[:int(sys.argv[1]) if len(sys.argv)>1 else 120]
def graph_of(d):
    G=nx.Graph(); G.add_nodes_from(range(d['n']))
    e=d['edges']; 
    if isinstance(e,str): e=[tuple(map(int,p.split('-'))) if '-' in p else tuple(map(int,p.split(','))) for p in e.replace(';',' ').split()]
    G.add_edges_from(e); return G
def tabu(G, w, L, seed_pairs, t, extra):
    g6=nx.to_graph6_bytes(G,header=False)
    cmd=[CLI,'-t',str(t),'-w',str(w),'-L',str(L),'-c','7','-s','1']+extra
    sf=None
    if seed_pairs is not None:
        import tempfile; sf=tempfile.NamedTemporaryFile('w',suffix='.seed',delete=False); sf.write(''.join(f'{a} {b}\n' for a,b in seed_pairs)); sf.close(); cmd+=['-seed',sf.name]
    p=subprocess.run(['nice','-n','19']+cmd,input=g6,capture_output=True,timeout=t*3+30)
    out=p.stdout.decode().strip().splitlines(); return json.loads(out[-1]) if out else {}
def exact_pw(H):
    g6=nx.to_graph6_bytes(nx.convert_node_labels_to_integers(H),header=False)
    o=subprocess.run([PW,'-t','60'],input=g6,capture_output=True).stdout.decode().split()
    return int(o[1]) if len(o)>=3 and o[2] in ('refutation','bound','minor') else None
def one(d):
    G=graph_of(d); w=d['width']; n=d['n']
    A=tabu(G,w,0,None,10,[])
    # a bad seed: random contractions to 0.6 n
    H=G.copy(); pairs=[]; r=random.Random(d['id'])
    while H.number_of_nodes()>max(3,int(0.6*n)):
        a,b=r.choice(list(H.edges())); pairs.append((a,b)); H=nx.contracted_nodes(H,b,a,self_loops=False)
    seed_pw=exact_pw(H)
    if seed_pw is None: return None
    B=tabu(G,w,seed_pw,pairs,10,['-b','50','-nb','5000','-nt','0.5','-lo','0.2','-hi','0.95','-m','1000'])
    C=tabu(G,w,seed_pw,pairs,0,['-b','50','-nb','5000','-nt','0.5','-lo','0.2','-hi','0.95','-m','1000'])
    return dict(id=d['id'],n=n,m=d['m'],width=w,A_floor=A.get('floor'),A_kind=A.get('kind'),A_minor=A.get('minor_vertices'),
                seed_minor=H.number_of_nodes(),seed_pw=seed_pw,C_floor=C.get('floor'),B_floor=B.get('floor'),B_kind=B.get('kind'),B_minor=B.get('minor_vertices'),B_steps=B.get('steps'))
with ThreadPoolExecutor(8) as ex: res=[x for x in ex.map(one,rows) if x]
with open('reports/scratch/minor_tabu/sanity/sanity.csv','w',newline='') as f:
    wr=csv.DictWriter(f,fieldnames=list(res[0].keys())); wr.writeheader(); wr.writerows(res)
N=len(res); print(f'{N} graphs, n {min(x["n"] for x in res)}-{max(x["n"] for x in res)}, width {min(x["width"] for x in res)}-{max(x["width"] for x in res)}')
print('SOUNDNESS: floor above certified width:', sum(x['A_floor']>x['width'] for x in res), '(A)', sum(x['B_floor']>x['width'] for x in res), '(B)')
print(f'A unseeded 10 s: floor == width on {sum(x["A_floor"]==x["width"] for x in res)}; kinds', dict(collections.Counter(x['A_kind'] for x in res)), '; minor < n on', sum((x['A_minor'] or 0)<x['n'] for x in res))
print(f'B bad seed, whole-graph climb crippled: seed floor == width on {sum(x["seed_pw"]==x["width"] for x in res)}; control (no steps) reaches width on {sum(x["C_floor"]==x["width"] for x in res)}; the walk reaches width on {sum(x["B_floor"]==x["width"] for x in res)}; walk raised the floor above the control on {sum(x["B_floor"]>x["C_floor"] for x in res)}')
gap=collections.Counter(x['width']-x['B_floor'] for x in res); print('B: width - floor distribution', dict(sorted(gap.items())))
print('B kinds', dict(collections.Counter(x['B_kind'] for x in res)))
