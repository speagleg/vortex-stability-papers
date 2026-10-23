# Provenance: independent reviewer's code (session scratchpad cdcheck/ngon.py, 2026-10-22), copied unchanged except for this header.
# Dense finite-difference Jacobian, even M; used in Section 5.4 of the paper to show the spurious real eigenvalues.
# Usage: python ngon_reviewer.py a M N
import numpy as np, sys
N=int(sys.argv[3]) if len(sys.argv)>3 else 7; M=int(sys.argv[2]) if len(sys.argv)>2 else 64; a=float(sys.argv[1]); R=1.0; q=1.0
th=2*np.pi*np.arange(M)/M
k=np.fft.fftfreq(M,1.0/M)
def deriv(f):
    fh=np.fft.fft(f); fh[M//2]=0  # drop Nyquist
    return np.real(np.fft.ifft(1j*k*fh))
# Kress weights matrix W[i,j]: int log(4 sin^2((t_i-s)/2)) f(s) ds ~ sum_j W_ij f_j
d=th[:,None]-th[None,:]; n=M//2
W=-(2*np.pi/n)*sum(np.cos(m*d)/m for m in range(1,n))-(np.pi/n**2)*np.cos(n*d)
cent=[R*np.array([np.cos(2*np.pi*p/N),np.sin(2*np.pi*p/N)]) for p in range(N)]
phis=[2*np.pi*p/N for p in range(N)]
def geom(rhos):
    X=[];DX=[]
    for p in range(N):
        r=rhos[p]; rp=deriv(r); ang=th+phis[p]
        er=np.array([np.cos(ang),np.sin(ang)]); et=np.array([-np.sin(ang),np.cos(ang)])
        X.append(cent[p][:,None]+r*er); DX.append(rp*er+r*et)
    return X,DX
def vel(rhos):
    X,DX=geom(rhos); U=[]
    for p in range(N):
        x=X[p]; u=np.zeros((2,M))
        for l in range(N):
            if l==p: continue
            dd=np.hypot(x[0][:,None]-X[l][0][None,:],x[1][:,None]-X[l][1][None,:])
            L=np.log(dd)*(2*np.pi/M)
            u+= np.array([L@DX[l][0],L@DX[l][1]])
        # self
        dx=x[0][:,None]-x[0][None,:]; dy=x[1][:,None]-x[1][None,:]
        s2=4*np.sin(d/2)**2
        with np.errstate(divide='ignore',invalid='ignore'):
            sm=0.5*np.log((dx**2+dy**2)/s2)
        sp=np.hypot(DX[p][0],DX[p][1]); np.fill_diagonal(sm,np.log(sp))
        Ls=sm*(2*np.pi/M)+0.5*W
        u+=np.array([Ls@DX[p][0],Ls@DX[p][1]])
        U.append(-q/(2*np.pi)*u)
    return X,U
def rhs(rhos,Om):
    X,U=vel(rhos); out=[]
    for p in range(N):
        x=X[p]; u=U[p]-Om*np.array([-x[1],x[0]])
        ang=th+phis[p]; ur=u[0]*np.cos(ang)+u[1]*np.sin(ang); ut=-u[0]*np.sin(ang)+u[1]*np.cos(ang)
        r=rhos[p]; out.append(ur-ut/r*deriv(r))
    return out
# steady solve: one patch even rho
Om=q*np.pi*a**2*(N-1)/(4*np.pi*R**2)
cs=np.zeros(M//2+1); cs[0]=a
def rho_from(cs): return sum(cs[m]*np.cos(m*th) for m in range(len(cs)))
def res(v):
    cs=v[:-1]; Om=v[-1]; r=rho_from(cs)
    o=rhs([r]*N,Om)[0]
    area=0.5*np.mean(r**2)*2*np.pi
    return np.concatenate([o,[area-np.pi*a**2]])
v=np.concatenate([cs,[Om]])
for it in range(30):
    f=res(v); J=np.zeros((len(f),len(v))); h=1e-7
    for j in range(len(v)):
        e=np.zeros(len(v)); e[j]=h; J[:,j]=(res(v+e)-res(v-e))/(2*h)
    dv=np.linalg.lstsq(J,-f,rcond=1e-12)[0]; v=v+dv
    if np.linalg.norm(f)<1e-13: break
print('a',a,'M',M,'resid',np.linalg.norm(res(v)),'Om',v[-1],'Om_pv',Om)
r0=rho_from(v[:-1]); Om=v[-1]
X,_=vel([r0]*N); cx=np.mean(X[0][0]*0)  # unused
# centroid
x=X[0]; DX=geom([r0]*N)[1][0]; A=np.pi*a**2
# full Jacobian
base=np.concatenate([r0]*N)
def F(z): return np.concatenate(rhs(list(z.reshape(N,M)),Om))
J=np.zeros((N*M,N*M)); h=1e-7
for j in range(N*M):
    e=np.zeros(N*M); e[j]=h; J[:,j]=(F(base+e)-F(base-e))/(2*h)
ev=np.linalg.eigvals(J)
ev=ev[np.argsort(abs(ev))]
print('slowest 20 eigenvalues:'); 
for z in ev[:20]: print(f'{z.real:+.3e} {z.imag:+.6e}')
i=np.argsort(-ev.real)[:4]; print("max real part over all:",max(ev.real), "top:", ev[i])
lam_book=np.sqrt(84)*a**2; print('pred |slow m=3| ~ sqrt84 a^2 * Gamma_phys/2pi =',lam_book*q*np.pi*a**2/(2*np.pi))
