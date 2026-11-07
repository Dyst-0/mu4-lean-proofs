import Mu4.Normal.CoverDefs

/-! C1 and the Frobenius table, checked by the kernel (`decide +kernel`) on all 4092 codes `4 ≤ z < 4096`, in chunks
of 1023. No `native_decide`. -/

namespace Mu4.Normal

theorem ftab_ok : ftabOk = true := by decide +kernel
theorem c1_ok1 : (List.range' 4 1023).all c1Ok = true := by decide +kernel
theorem c1_ok2 : (List.range' 1027 1023).all c1Ok = true := by decide +kernel
theorem c1_ok3 : (List.range' 2050 1023).all c1Ok = true := by decide +kernel
theorem c1_ok4 : (List.range' 3073 1023).all c1Ok = true := by decide +kernel

end Mu4.Normal
