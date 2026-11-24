-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Access

@[expose] public section

/-! The `fmt` number of memory bytes (`memFloat`) when they are the bytes of one stored scalar
value: the value read as a `fmt` operand. -/
namespace PTX
noncomputable section

/-- The bytes of a whole scalar value rebuild to it. -/
theorem rebuild_scalar {v : Value} (hb : ∀ k, v.byteAt k = (v, k)) (hpos : 0 < v.bytes) :
    rebuild 3 ((List.range v.bytes).map fun k => some (v, k)) = .ok v := by
  obtain ⟨n, hn⟩ : ∃ n, v.bytes = n + 1 := ⟨v.bytes - 1, by omega⟩
  have he : (List.range v.bytes).map (fun k => some (v, k)) =
      some (v, 0) :: (List.range n).map (fun k => some (v, k + 1)) := by
    rw [hn, List.range_succ_eq_map]; simp
  rw [he]
  simp only [rebuild]
  rw [ite_eq_left ⟨by simp [hn], by
    rw [← he]; simp [Value.toBytes, hb]⟩]
  rfl

/-- Memory bytes that are the bytes of one stored scalar value of `fmt`'s width read as that
value's `fmt` number. -/
theorem memFloat_of_bytes {fmt : FloatFmt} {m : Loc → Option (Option Byte)} {l : Loc}
    {v : Value} (hb : ∀ k, v.byteAt k = (v, k)) (hn : v.bytes = fmt.bytes)
    (hm : ∀ k < fmt.bytes, m (l.at k) = some (some (v, k))) :
    memFloat fmt m l = valFloat fmt v := by
  have hpos : 0 < fmt.bytes := by cases fmt <;> decide
  have hl : ((List.range fmt.bytes).map fun k => (m (l.at k)).join) =
      (List.range v.bytes).map fun k => some (v, k) := by
    rw [hn]
    refine List.map_congr_left fun k hk => ?_
    rw [hm k (List.mem_range.mp hk)]; rfl
  simp only [memFloat, hl, rebuild_scalar hb (hn ▸ hpos)]
  rfl

/-- The bytes of a `fmt` payload read as its number. -/
theorem memFloat_float {fmt : FloatFmt} {m : Loc → Option (Option Byte)} {l : Loc} {x : ℝ}
    (hm : ∀ k < fmt.bytes, m (l.at k) = some (some (.float fmt x, k))) :
    memFloat fmt m l = .ok x := by
  rw [memFloat_of_bytes (fun _ => rfl) rfl hm]
  simp [valFloat, pure, Except.pure]

end

end PTX
