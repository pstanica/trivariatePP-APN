"""Exhaustive classification over GF(8) = GF(2)[t]/(t^3+t+1).
Elements 0,...,7 encode polynomial coefficients as binary digits.
Run with Python 3. No external dependencies are required.
"""
import itertools
mul=[[0]*8 for _ in range(8)]
for a,b in itertools.product(range(8),repeat=2):
 x=a;y=b;t=0
 while y:
  if y&1:t^=x
  x<<=1
  if x&8:x^=11
  y>>=1
 mul[a][b]=t
for q in [2,4]:
 def powr(a,n):
  x=1
  for _ in range(n):x=mul[x][a]
  return x
 qp=[powr(x,q) for x in range(8)]; gold=[mul[x][qp[x]] for x in range(8)]
 data=[(gold[x],mul[qp[x]][z],mul[y][qp[z]],gold[y],mul[x][qp[y]],mul[qp[y]][z],gold[z]) for x,y,z in itertools.product(range(8),repeat=3)]
 perms=[]
 for a1,a2,a3,a4 in itertools.product(range(8),repeat=4):
  seen=set()
  for g1,c1,c2,g2,c3,c4,g3 in data:
   val=((g1^mul[a1][c1]^mul[a2][c2])<<6)|((c1^g2)<<3)|(mul[a3][c3]^mul[a4][c4]^g3)
   if val in seen:break
   seen.add(val)
  else:perms.append((a1,a2,a3,a4))
 expected_type_ii={(a,1,1,a) for a in range(1,8)}
 assert len(perms)==20
 assert {p for p in perms if p[0]!=0}==expected_type_ii
 type_i={(p[1],p[2]) for p in perms if p[0]==0}
 assert all(p[0]==p[3]==0 for p in perms if p[0]==0)
 if q==2: type_i_q2=type_i
 else: assert type_i=={(b,a) for a,b in type_i_q2}
 print('q=',q,'count=',len(perms),'perms=',perms,flush=True)

