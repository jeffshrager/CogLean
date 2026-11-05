# ACTR

ACT-R results that need real numbers, and the bridge from CogLib's rational
statements to their real-valued forms. This is the only package that uses
Mathlib (pinned to `v4.35.0`); CogLib stays core-only. After cloning, run
`lake exe cache get` here before `lake build`, or Mathlib will be compiled
from source.

| Module | What it proves |
|---|---|
| `ACTR/PowerLaw` | CogLib's scale invariance (`Phenomena.ScaleRatio`) agrees with its real form (`scaleRatio_iff_cast`); `a · n^(-b)` is scale-invariant with ratio `k^(-b)` (`rpow_scaleRatio`); conversely, scale invariance at doubling with ratio `r` is a power law on the doubling grid with exponent `-log₂ r` (`powerLaw_of_scaleRatio`); CogLib's `power a m` is the real power law (`power_cast`); ACT-R's spaced-practice curve with any decay (`spacedR`), which at decay 1 is CogLib's `Act.spaced` (`spaced_cast`) |
| `ACTR/Decay` | with decay `0 ≤ d < 1`, `Σ_{k ≤ n} k^(-d)` lies between integrals of `x^(-d)` (`baseSpaced_bounds`) and grows like `(n+1)^(1-d)/(1-d)` (`baseSpaced_div_tendsto`); the doubling ratio of latency tends to `2^(-(1-d))` (`spacedR_doubling_tendsto`); **so spaced practice is approximately a power law with exponent `1 - d`**, to within any tolerance beyond some trial (`spacedR_approx_powerLaw`). At decay 1 the same mechanism is logarithmic (`Act.spaced_not_powerLaw`, CogLib). |
