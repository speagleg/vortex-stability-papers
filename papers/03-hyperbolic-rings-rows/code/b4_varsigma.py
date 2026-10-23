# Provenance: the author's earlier research code (unpublished), adapted for this paper.
# Changes: none
# Second-order large-N constants: varsigma, remainder O(N^-4), parity curves.
from mpmath import mp, mpf, cosh, sinh, tanh, coth, pi, sqrt, findroot, diff, taylor, log, nstr, acosh
mp.dps=50
Lan=lambda x: coth(x)-1/x
def ahat_inf(t): return ((4/t)*tanh(t/2)-Lan(t/2)**2)/8
tinf=findroot(ahat_inf,mpf('7.445'))
ell_s=2*pi/tinf
def chT(mh,t): return cosh(t)*cosh(mh*t)-mh*sinh(t)*sinh(mh*t)
def Psi(mh,t): return (1-mh**2)/8+chT(mh,t)/(4*sinh(t)**2)
def EN(N,t): X0=coth(t/N); return X0/N*coth(t)-X0**2/(2*N**2)-1/(2*mpf(N)**2)
def acrit(N,t):   # a^perp_{floor(N/2)}/N^2 (exact symbol, paper Thm 3.3)
    mh=mpf(1)/N if N%2 else mpf(0)
    return EN(N,t)-1/(4*sinh(t)**2)-Psi(mh,t)
# consistency with tanh-limit-symbol: ahat_inf = E_inf - 1/(4 sinh^2) - Psi(0)
t0=mpf('6.3'); print('limit-symbol consistency:',nstr(ahat_inf(t0)-(coth(t0)/t0-1/(2*t0**2)-1/(4*sinh(t0)**2)-Psi(0,t0)),5))
ap=diff(ahat_inf,tinf)
r2=lambda t: (t*coth(t)-1)/3-mpf(1)/2
Psimm0=lambda t: -mpf(1)/4+(t**2*cosh(t)-2*t*sinh(t))/(4*sinh(t)**2)
print('Psi_mm(0) closed form vs numeric:',nstr(Psimm0(tinf)-diff(lambda m: Psi(m,tinf),0,2),5))
e2=lambda t: -Psimm0(t)/2
de=(r2(tinf))/(-ap); do=(r2(tinf)+e2(tinf))/(-ap)
se=tinf/3-de/tinf**2; so=tinf/3-do/tinf**2
print('tau_inf',nstr(tinf,35)); print("ahat'(tau_inf)",nstr(ap,30))
print('r2(tau_inf)',nstr(r2(tinf),30),' e2(tau_inf)',nstr(e2(tinf),30))
print('delta_e',nstr(de,30),' delta_o',nstr(do,30))
print('varsigma_e',nstr(se,30)); print('varsigma_o',nstr(so,30))
Ce=2*pi*(se-tinf/2); Co=2*pi*(so-tinf/2)
print('C_e=2pi(vs_e-tinf/2)',nstr(Ce,25),' C_o',nstr(Co,25))
Se=2*Ce/tinf**2; So=2*Co/tinf**2
print('ring slopes dl/dkappa at kappa=1+: S_e',nstr(Se,25),' S_o',nstr(So,25))
# exact thresholds vs expansion
print(' N   N^2(tau*-tinf)-delta   N^4*[tau*-tinf-delta/N^2]   N^3*(X0*-N/tinf-vs/N)   N^4*(l_N-l_*-C/N^2)')
for N in [40,41,80,81,160,161,320,321,640,641,1280,1281]:
    ts=findroot(lambda t: acrit(N,t),tinf)
    d=de if N%2==0 else do; s=se if N%2==0 else so; C=Ce if N%2==0 else Co
    X0=coth(ts/N); lN=2*pi/(N*sinh(ts/N))
    print(N, nstr(N**2*(ts-tinf)-d,12), nstr(N**4*(ts-tinf-d/N**2),12), nstr(N**3*(X0-N/tinf-s/N),12), nstr(N**4*(lN-ell_s-C/N**2),12))
