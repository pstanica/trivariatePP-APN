"""Independent exact sparse-polynomial checks in characteristic two.
Run with Python 3. No external dependencies are required.
The five exponents use ten bits each, exceeding all degrees in these checks.
"""
import re,time,json
from pathlib import Path
class Poly:
 def __init__(self,terms): self.t=set(terms)
 def __len__(self): return len(self.t)
 def __add__(self,o):
  if isinstance(o,int): o=Poly([0] if o%2 else [])
  return Poly(self.t^o.t)
 __radd__=__add__
 def __mul__(self,o):
  if isinstance(o,int): return self if o%2 else Poly([])
  out=set()
  for a in self.t:
   for b in o.t:
    c=a+b
    if c in out:out.remove(c)
    else:out.add(c)
  return Poly(out)
 __rmul__=__mul__
 def __pow__(self,n):
  out=Poly([0]);a=self
  while n:
   if n&1:out=out*a
   n>>=1
   if n:a=Poly([2*x for x in a.t])
  return out
 def __eq__(self,o):return self.t==o.t
 def div(self,o):
  import heapq
  terms=set(self.t); q=set();r=set();lead=max(o.t)
  heap=[-x for x in terms];heapq.heapify(heap)
  tail=o.t-{lead}
  while terms:
   m=-heapq.heappop(heap)
   if m not in terms:continue
   terms.remove(m)
   if all(((m>>(10*j))&1023)>=((lead>>(10*j))&1023) for j in range(5)):
    d=m-lead;q.add(d)
    for x in tail:
     v=x+d
     if v in terms:terms.remove(v)
     else:terms.add(v);heapq.heappush(heap,-v)
   else:r.add(m)
  return Poly(q),Poly(r)

s=Path(__file__).with_name('SecondRevision.tex').read_text(); code=s.split('\\begin{filecontents*}[overwrite]{verify_factorization_H.m}\n')[1].split('\\end{filecontents*}')[0]
# Parse the embedded MAGMA source without executing MAGMA.
X,b,Y,Z,u=[Poly([1<<(10*j)]) for j in [4,3,2,1,0]]; env=dict(X=X,b=b,Y=Y,Z=Z,u=u)
for name,expr in re.findall(r'(\w+)\s*:=\s*(.*?);',code,re.S):
 if name in ['F2','Q2','Rfac']: continue
 env[name]=eval(''.join(expr.split()).replace('^','**'),{},env)
 if isinstance(env[name],int):env[name]=Poly([])
print('built',[(k,len(env[k])) for k in ['P','E2','H']],flush=True)
for k in ['E2','H']:
 t=time.time(); quo,rem=env[k].div(env['P']); print(k,'remainder',len(rem),'quotient',len(quo),'seconds',time.time()-t,flush=True); assert len(rem)==0
print('bound at 2^23',2**23-506*(2**23)**.5-5*24**(13/3)-288,flush=True)

app=s.split('\\section{Polynomial definitions}')[1].split('\\section{Verification code')[0]
headers=list(re.finditer(r'(g|h|a_\{*\d+\}*)\(\\beta[^\n]*?&:=',app))
for j,m in enumerate(headers):
 name=m[1].replace('{','').replace('}','').replace('_','')
 expr=app[m.end():headers[j+1].start() if j+1<len(headers) else app.index('\\end{align*}')]
 expr=expr.replace('\\beta','b').replace('&','').replace('\\\\','')
 expr=re.sub(r'\^\{([^{}]*)\}',r'^\1',expr)
 expr=expr.replace('{','').replace('}','');expr=re.sub(r'\s+','',expr).rstrip(',.')
 expr=re.sub(r'([ubXYZ]|\d|\))(?=[ubXYZ(])',r'\1*',expr)
 val=eval(expr.replace('^','**'),{},env)
 if isinstance(val,int):val=Poly([])
 print('appendix',name,val==env[name],flush=True); assert val==env[name]
