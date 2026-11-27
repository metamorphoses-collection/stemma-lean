import sympy as sp, itertools
q13,q123,p3,p4,al,rho,sg,b,tu,eps = sp.symbols('q13 q123 p3 p4 α ρ σ b τ ε')
def w(pi,x): return [1-pi, pi*al, pi*(1-al)][x]
def rd(e,x): return 1 if x==1 else 2+e
def rb(e,f,lo,hi):
    if lo!=0: return rd(e,lo)
    if hi!=0: return rd(f,hi)
    return 0
def U12(x1,x2,x3,x4): return (x2==x1 and x3!=x1 and x4!=x1) or (x4==x3 and x1!=x3 and x2!=x3)
def U13(x1,x2,x3,x4): return (x1==x3 and x2!=x1 and x4!=x1) or (x2==x4 and x1!=x2 and x3!=x2)
def U14(x1,x2,x3,x4): return (x4==x1 and x2!=x1 and x3!=x1) or (x3==x2 and x1!=x2 and x4!=x2)
def C(S):
    def f(*x):
        x=list(x); i=S[0]; v=x[i]
        if v==0: return False
        return all((x[j]==v)==(j in S) for j in range(4))
    return f
preds = {'U12':U12,'U13':U13,'U14':U14}
names = {'C12':[0,1],'C13':[0,2],'C14':[0,3],'C23':[1,2],'C24':[1,3],'C34':[2,3],'C123':[0,1,2],'C124':[0,1,3],'C134':[0,2,3],'C234':[1,2,3]}
for k,v in names.items(): preds[k]=C(v)
res={}
for k,P in preds.items():
    tot=0
    for e,h,c,d in itertools.product(range(3),repeat=4):
        x1=rb(0,1,e,h); x2=rb(1,1,0,h); x3=rd(2,c) if c!=0 else rb(0,1,e,h); x4=rb(3,3,0,d)
        if P(x1,x2,x3,x4):
            tot+=w(q13,e)*w(q123,h)*w(p3,c)*w(p4,d)
    res[k]=sp.expand(tot)
sub={q13:rho*eps**2,q123:sg*eps,p3:b*eps,p4:tu*eps}
for k,v in res.items():
    s=sp.expand(v.subs(sub))
    pw = 1 if k=='C123' else 2
    g=sp.expand(sp.simplify(s/eps**pw))
    assert sp.expand(g*eps**pw - s)==0 and g.is_polynomial(eps)
    print(k, 'closed:', v)
    print(k, 'g0:', sp.factor(g.subs(eps,0)), '| g:', g)
