import sympy as sp, itertools, re
r,s,p3,p4,al,rho,sg,b,tu,eps = sp.symbols('r s p3 p4 α ρ σ b τ ε')
exec(open('drift.py').read().split("preds = ")[0].split("def w(")[0].replace("q13,q123,p3,p4,al,rho,sg,b,tu,eps = sp.symbols('q13 q123 p3 p4 α ρ σ b τ ε')",""))
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
        x=list(x); v=x[S[0]]
        if v==0: return False
        return all((x[j]==v)==(j in S) for j in range(4))
    return f
order=['U12','U13','U14','C12','C13','C14','C23','C24','C34','C123','C124','C134','C234']
names = {'C12':[0,1],'C13':[0,2],'C14':[0,3],'C23':[1,2],'C24':[1,3],'C34':[2,3],'C123':[0,1,2],'C124':[0,1,3],'C134':[0,2,3],'C234':[1,2,3]}
preds={'U12':U12,'U13':U13,'U14':U14}
for k,v in names.items(): preds[k]=C(v)
lean={'U12':'Stemma.Coding.U12','U13':'Stemma.Quartet.U13','U14':'Stemma.Coding.U14'}
for k in names: lean[k]='Stemma.Coding.'+k
def L(e): return str(e).replace('**','^')
out=[]
sub={r:rho*eps**2,s:sg*eps,p3:b*eps,p4:tu*eps}
for k in order:
    P=preds[k]; tot=0
    for e,h,c,d in itertools.product(range(3),repeat=4):
        x1=rb(0,1,e,h); x2=rb(1,1,0,h); x3=rd(2,c) if c!=0 else rb(0,1,e,h); x4=rb(3,3,0,d)
        if P(x1,x2,x3,x4): tot+=w(r,e)*w(s,h)*w(p3,c)*w(p4,d)
    cl=sp.expand(tot)
    pw = 1 if k=='C123' else 2
    g=sp.expand(sp.expand(cl.subs(sub))/eps**pw)
    assert sp.expand(g*eps**pw-cl.subs(sub))==0 and g.is_polynomial(eps)
    z=sp.expand(g.subs(eps,0))
    lp = 'ε' if pw==1 else 'ε ^ 2'
    out.append(f"""theorem closed_{k} (r s p3 p4 α : ℝ) :
    suppD r s p3 p4 α {lean[k]} = {L(cl)} := by
  simp [suppD, w, readBelow, rd, {lean[k]}, Fin.sum_univ_three]; ring

/-- `{k}` divided by `{lp}` after the substitution. -/
def g{k} (ρ σ b τ α ε : ℝ) : ℝ := {L(g)}

theorem scale_{k} (ρ σ b τ α ε : ℝ) :
    suppD (ρ * ε ^ 2) (σ * ε) (b * ε) (τ * ε) α {lean[k]} = {lp} * g{k} ρ σ b τ α ε := by
  rw [closed_{k}]; unfold g{k}; ring

theorem cont_{k} (ρ σ b τ α : ℝ) : Continuous (g{k} ρ σ b τ α) := by
  unfold g{k}; fun_prop

theorem zero_{k} (ρ σ b τ α : ℝ) : g{k} ρ σ b τ α 0 = {L(z)} := by
  unfold g{k}; ring
""")
print("\n".join(out))
