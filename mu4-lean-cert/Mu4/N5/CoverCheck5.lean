import Mu4.N5.CoverDefs5

/-! C1(5), C2(5) and the Frobenius table, checked by the kernel (`decide +kernel`) on all 1020 codes
`4 ≤ z < 1024`. No `native_decide`. -/

set_option autoImplicit false

namespace Mu4.N5

theorem ftab_ok5 : ftabOk5 = true := by decide +kernel
theorem c1_ok5 : (List.range' 4 1020).all c1Ok5 = true := by decide +kernel
theorem c2_ok5 : (List.range' 4 1020).all c2Ok5 = true := by decide +kernel

end Mu4.N5
