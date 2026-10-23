# Provenance: independent referee code, unmodified (session scratchpad referee2/fitfreq.py, 2026-10-23). Only this header was added.
import re, numpy as np
for f,ex in [('lagr020.txt',(0.3544572,-0.4385848)),('lagr015.txt',(0.2015682,-0.2220472))]:
    t=[];d=[]
    for L in open(f):
        m=re.search(r't=\s*([\d.]+).*dr3=([+-]\d\.\d+e[+-]\d+)([+-]\d\.\d+e[+-]\d+)i',L)
        if m: t.append(float(m.group(1))); d.append(float(m.group(2))+1j*float(m.group(3)))
    t=np.array(t);d=np.array(d)
    ws=np.linspace(-0.8,0.8,3201)
    P=np.array([abs(np.mean(d*np.exp(-1j*w*t))) for w in ws]); idx=np.argsort(P)[::-1]
    peaks=[]
    for i in idx:
        if all(abs(ws[i]-p)>0.05 for p in peaks): peaks.append(round(ws[i],4))
        if len(peaks)==2: break
    n=len(d)
    print(f,'T=',t[-1],'max|dr3| first/last third',abs(d[:n//3]).max(),abs(d[2*n//3:]).max(),'peaks',peaks,'eig',ex)
