# Amplification kill test (LB-35)

DRAFT, numbers still landing. See the final section once runs finish.

Working verdict: amplification alone does not beat 3.2706 on any tested size.
The rule 'tr' (mean-rank pairing in the last K stages) repairs the LB-33
sharpness deficit at N_d with no extra depth, while the heights and wire
relaxations still pass. Sharp-and-placed stays >= 0.997 out to 16 N_d. Exact
sorting of random inputs lags N_d at about 0.2 bits per stage. Structured inputs
stay wrong by about 4% of n.
