from fmin import *
eps=1/86e6; d=128/4095
for cap in (True, False):
    for th in (0.5, 0.42, 0.6):
        f=fmin_sum(eps,d,0.49,th,cap)
        print("sum-over-E cap=%s theta=%.2f f_min=%.4g"%(cap,th,f), worst_n(f,eps,d,th,cap))
