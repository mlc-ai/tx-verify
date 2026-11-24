-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Memory

@[expose] public section

namespace PTX

/-- A read of a scalar value's launch footprint returns its bytes when there are no writers. -/
theorem Consistent.launch_value {K : Kernel} {A : List Assumption} {L : Launch}
    {m : Mem0} {X : Execution} (hX : Consistent L K A m X)
    {r : AsyncCopy.Ref} {a : Acc} {bs : List (Option Byte)} {v : Value}
    (hRead : X.MemReads r a bs) (hSize : a.size = v.bytes)
    (hNoWrite : ∀ i < a.size, ∀ w a' ws, X.MemWrites w a' ws → ¬ a'.Covers (a.loc.at i))
    (hLaunch : ∀ i < a.size, m (a.loc.at i) = some (some (v.byteAt i))) :
    bs = v.toBytes.map some := by
  have h := hX.read_length hRead
  apply List.ext_getElem?
  intro i
  by_cases hi : i < a.size
  · rw [hX.launch_byte hRead hi (hNoWrite i hi) (hLaunch i hi)]
    simp [Value.toBytes, ← hSize, hi]
  · rw [List.getElem?_eq_none (by omega)]
    simp [Value.toBytes, ← hSize, hi]

end PTX
