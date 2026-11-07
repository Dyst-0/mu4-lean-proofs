import Mu4.Normal.CoverDefs

/-! C2, checked by the kernel (`decide +kernel`) on all 4092 codes `4 ≤ z < 4096`, in chunks of 1023.
No `native_decide`. -/

namespace Mu4.Normal

theorem c2_ok1 : (List.range' 4 1023).all c2Ok = true := by decide +kernel
theorem c2_ok2 : (List.range' 1027 1023).all c2Ok = true := by decide +kernel
theorem c2_ok3 : (List.range' 2050 1023).all c2Ok = true := by decide +kernel
theorem c2_ok4 : (List.range' 3073 1023).all c2Ok = true := by decide +kernel

end Mu4.Normal
