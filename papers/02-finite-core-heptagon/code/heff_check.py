# Provenance: independent referee code, unmodified (session scratchpad referee2/heff_check.py, 2026-10-23). Only this header was added.
# independent numeric Hessian of H_eff for N-ring in log-polar coords; complex-step-free, mpmath finite differences
import mpmath as mp, sys
mp.mp.dps = 40
N = int(sys.argv[1]) if len(sys.argv)>1 else 7
zeta = mp.exp(2j*mp.pi/N)
def zs(x):  # x: list of 2N reals (s0,t0,s1,t1,...)
    return [zeta**k*mp.exp(x[2*k]+1j*x[2*k+1]) for k in range(N)]
def H(x):
    z = zs(x); return -sum(mp.log(abs(z[j]-z[k])) for j in range(N) for k in range(j+1,N))
def Phi(x):
    z = zs(x); return sum(abs(sum(1/(z[k]-z[l])**2 for l in range(N) if l!=k))**2 for k in range(N))/4
def J(x):
    z = zs(x); return sum(abs(w)**2 for w in z)/2
h = mp.mpf('1e-10')
def hess_row(f, i):  # second derivatives d^2 f / dx_i dx_j for all j
    x0 = [mp.mpf(0)]*(2*N)
    out = []
    for j in range(2*N):
        def ev(a,b):
            x = list(x0); x[i]+=a; x[j]+=b; return f(x)
        out.append((ev(h,h)-ev(h,-h)-ev(-h,h)+ev(-h,-h))/(4*h*h))
    return out
def grad0(f):
    x0=[mp.mpf(0)]*(2*N); xp=list(x0); xm=list(x0); xp[0]+=h; xm[0]-=h
    return (f(xp)-f(xm))/(2*h)
def block(rows, m):
    # rows: hessian rows for s0 (i=0) and t0 (i=1); block entries sum_j d2/d(q0)d(q_j) zeta^{mj}
    B = [[0,0],[0,0]]
    for a in range(2):
        for b in range(2):
            B[a][b] = sum(rows[a][2*j+b]*zeta**(m*j) for j in range(N))
    return B
Om0 = grad0(H)/grad0(J); Om1 = grad0(Phi)/grad0(J)
print('Omega0', mp.nstr(Om0,12), 'Omega1', mp.nstr(Om1,12))
RH=[hess_row(H,0),hess_row(H,1)]; RP=[hess_row(Phi,0),hess_row(Phi,1)]; RJ=[hess_row(J,0),hess_row(J,1)]
for m in range(1, N//2+1):
    BH, BP, BJ = block(RH,m), block(RP,m), block(RJ,m)
    B0 = [[BH[a][b]-Om0*BJ[a][b] for b in range(2)] for a in range(2)]
    B1 = [[BP[a][b]-Om1*BJ[a][b] for b in range(2)] for a in range(2)]
    print('m',m,'a_perp:',mp.nstr(B0[0][0].real,10),'+eps',mp.nstr(B1[0][0].real,10),' a_par:',mp.nstr(B0[1][1].real,10),'+eps',mp.nstr(B1[1][1].real,10),' offdiag eps:',mp.nstr(B1[0][1],10))
