from fmin import *
print("eps^-1  delta   f_sup(x<=.3223,th=.5)  eps*f | f_sum(.49) th=.5 | eps*f")
for ie in (86e6,2e7,1e7,1e6):
    for d in (128/4095,0.02,0.01):
        e=1/ie
        fs=fmin_sup(e,d); fm=fmin_sum(e,d,0.49,0.5,True)
        print("%.0e %.4f  %.3e %.1f | %.3e %.1f"%(ie,d,fs,fs*e,fm,fm*e))
