# Provenance: the author's earlier research code (unpublished), adapted for this paper.
# Changes: none
import os as _os, sys as _sys; _HERE=_os.path.dirname(_os.path.abspath(__file__)); _sys.path.insert(0,_HERE)
exec(open(_os.path.join(_HERE,'b7_curves.py')).read().split("print(' alpha")[0].split("print(\"I'(ell_*)\"")[0])
mp.dps=160
tinf=findroot(lambda t: ((4/t)*tanh(t/2)-Lan(t/2)**2)/8, mpf('7.445')); ls=2*pi/tinf
def Fpi_dual(ell,al,nmax=8):
    lu=ell*sin(al); qt=exp(-2*pi**2/lu)
    R=-(2*pi/lu)*sum(qt**(2*n)/(1-qt**(2*n))*(sin(2*al)*sinh(4*pi*n*al/lu)-4*pi*n*sin(al)**2/lu) for n in range(1,nmax))\
      -(2*pi**2*sin(al)**2/lu**2)*sum(n*qt**n/(1-qt**n)*(1+cosh(2*pi*n*al/lu)) for n in range(1,nmax))
    return Fmod(ell,al)+R, R
Lmod=lambda al: findroot(lambda l: Fmod(l,al),ls)
print(' alpha  ell*-ell*_mod   -R(ell*_mod)/dFmod/dell   R<0?')
for al in [mpf('0.3'),mpf('0.2'),mpf('0.12'),mpf('0.08')]:
    lt=findroot(lambda l: Fpi_dual(l,al)[0],ls); lm=Lmod(al)
    R=Fpi_dual(lm,al)[1]; d=diff(lambda l: Fmod(l,al),lm)
    print(nstr(al,3),nstr(re(lt-lm),10),nstr(re(-R/d),10),re(R)<0)
