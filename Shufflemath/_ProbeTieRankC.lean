module

public import Shufflemath.TotalVariation

@[expose] public section

namespace Shufflemath

/-! Scratch: verifies the Batch 2 (e) integration — the generic same-source
    coupling inequality and its two helpers now live in
    `Shufflemath.TotalVariation` (namespace `Dist`). -/

#check Dist.tv_maps_le_mismatch
#check Dist.mismatch_mass_mul_boole_diff
#check Dist.boole_diff_abs_le_sum

end Shufflemath
