s|^  have hfail := round1_and_PF_fail_fraction hm hn PF hPF$|  have hfail := round1_and_PF_fail_fraction hm hn PF hPF|
s|    (c := 1 / 100 + 483 / 1000) (by norm_num) hfail|    (c := 1 / 100 + 483 / 1000) (by norm_num) (by convert hfail using 2)|
