# Provenance: the author's earlier research code (unpublished), adapted for this paper.
# Changes: none
# Germs at the horocycle point (1, ell_*) in the (kappa, ell) plane.
from mpmath import mp, mpf, mpc, cos, sin, cosh, sinh, tanh, coth, pi, findroot, taylor, diff, nstr, acos, acosh, exp, re, im, sqrt, log, cot
mp.dps=50
Lan=lambda x: coth(x)-1/x
tinf=findroot(lambda t: ((4/t)*tanh(t/2)-Lan(t/2)**2)/8, mpf('7.445')); ls=2*pi/tinf
def chT(mh,t): return cosh(t)*cosh(mh*t)-mh*sinh(t)*sinh(mh*t)
def sinc_inv(al): return al/sin(al) if al!=0 else mpf(1)
# at fixed arc spacing ell, l_u = ell sin(alpha):  tau = 2 pi alpha/l_u = (2pi/ell) alpha/sin alpha
def Eeven(ell,al,mh2=0):   # F^mod_even(q) at fixed ell, m-hat^2 = mh2 ; 2pi^2 sin^2/l_u^2 = 2pi^2/ell^2
    t=(2*pi/ell)*sinc_inv(al); mh=sqrt(mpc(mh2))
    return pi*cos(al)/ell*coth(t)-cos(2*al)/4-(2*pi**2/ell**2)*((1-mh2)/8+(1+chT(mh,t))/(4*sinh(t)**2))
def Fmod(ell,al): return Eeven(ell,al)-2*al*cos(al)/ell
I=lambda ell: (lambda e: e*coth(2*e)-e**2/4*coth(e)**2-mpf(1)/4)(pi/ell)
Ip=diff(I,ls)
print("I'(ell_*)",nstr(Ip,30),'  c1 = 2/(ell_* I\') =',nstr(2/(ls*Ip),30))
# modular branch ell*_mod(alpha): Taylor in alpha
Lmod=lambda al: findroot(lambda l: Fmod(l,al),ls)
cm=taylor(Lmod,0,5)
print('ell*_mod(alpha) Taylor coeffs c0..c5:',[nstr(c,20) for c in cm])
# continued to alpha = i a: imaginary part, e.g. a=0.05
a=mpf('0.05'); print('ell*_mod(i a), a=0.05:',nstr(findroot(lambda l: Fmod(l,1j*a),mpc(ls,0.03)),20))
# even-N ring curve: E(ell, alpha^2)=0, as function of kappa=cos alpha (alpha real for kappa<1, alpha=ia for kappa>1)
def Le(kap,mh2fun=None,st=None):
    al=acos(mpc(kap)) if kap<=1 else 1j*acosh(kap)
    f=(lambda l: Eeven(l,al)) if mh2fun is None else (lambda l: Eeven(l,al,mh2fun(l,al)))
    return re(findroot(f,ls if st is None else st))
ce=taylor(lambda k: Le(1+k),0,3)
print('even curve L_e(kappa) coeffs in (kappa-1):',[nstr(c,20) for c in ce])
mh2=lambda l,al: -(l*sin(al))**2/(4*pi**2)
co=taylor(lambda k: Le(1+k,mh2),0,3)
print('odd  curve L_o(kappa) coeffs in (kappa-1):',[nstr(c,20) for c in co])
# check against actual thresholds
def Wk(k,N,xi): return xi**k*(k+(N-k)*xi**N)/(1-xi**N)**2
def aperp(N,m,xi):
    X0=(1+xi)/(1-xi); WN=Wk(N,N,xi); U=N*X0*(1+xi**N)/(1-xi**N)-X0**2/2-mpf(1)/2
    return U-mpf(m*(N-m))/2-N*WN-mpf(N)/2*(Wk(m,N,xi)+Wk(N-m,N,xi))
print(' N  kappa_N-1   ell_N   ell_N-L_e(kappa_N)  ell_N-L_o(kappa_N)')
for N in [8,9,16,17,64,65]:
    r=findroot(lambda r: aperp(N,N//2,tanh(r/2)**2), log(2*N/tinf)+0.1)
    k=coth(r); lN=2*pi*sinh(r)/N
    print(N,nstr(k-1,10),nstr(lN,20),nstr(lN-Le(k,None,lN),5),nstr(lN-Le(k,mh2,lN),5))
# rows: true threshold vs modular branch; R asymptotics
def Fpi_dual(ell,al,nmax=6):
    lu=ell*sin(al); qt=exp(-2*pi**2/lu)
    R=-(2*pi/lu)*sum(qt**(2*n)/(1-qt**(2*n))*(sin(2*al)*sinh(4*pi*n*al/lu)-4*pi*n*sin(al)**2/lu) for n in range(1,nmax))\
      -(2*pi**2*sin(al)**2/lu**2)*sum(n*qt**n/(1-qt**n)*(1+cosh(2*pi*n*al/lu)) for n in range(1,nmax))
    return Fmod(ell,al)+R, R
print(' alpha   ell*   ell*-ell*_mod   predicted (2pi^2/l*^2)(1+cosh(2pi/l*))e^{-2pi^2/(l* sin a)}/I\'')
for al in [mpf('0.3'),mpf('0.2'),mpf('0.12'),mpf('0.08')]:
    lt=findroot(lambda l: Fpi_dual(l,al)[0],ls); lm=Lmod(al)
    pred=(2*pi**2/ls**2)*(1+cosh(2*pi/ls))*exp(-2*pi**2/(ls*sin(al)))/Ip
    print(nstr(al,3),nstr(lt,20),nstr(lt-lm,8),nstr(pred,8))
# cross-check true threshold with value in the havelock note at kappa = 0.99 (ell* = 0.95376510728761)
al=acos(mpf('0.99')); print('ell*(0.99) from dual form:',nstr(findroot(lambda l: Fpi_dual(l,al)[0],ls),15))
