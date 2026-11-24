-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.ReadLast

@[expose] public section

namespace PTX

noncomputable section

/-- A register-based explicit local address is owned by the issuing thread. -/
theorem accessLoc_local_reg {L : Launch} {g r w : Nat} {t : TState} {a : MemAccess}
    {v : BitVec 64} (hs : a.space = some .local) (hb : a.addr.base = .reg r w)
    (hv : readBits L g t w (.reg r) = .ok v) :
    accessLoc L g t a = .ok ⟨.local, g, wrapAddr w v a.addr.off⟩ := by
  simp [accessLoc, hs, hb, hv, bind, Except.bind, pure, Except.pure]

/-- Local accesses owned by different threads cannot overlap, even at the same address. -/
theorem local_access_apart_of_owner {a b : Acc} (h : a.loc.cta ≠ b.loc.cta) :
    ¬ a.Overlap b := by
  rintro ⟨_, hx, hy⟩
  exact h (hx.2.1.symm.trans hy.2.1)

/-- The byte in a thread-local load is taken from its last overlapping write in the thread's
trace. The ownership hypothesis supplies the trace as the only possible source of writers. -/
theorem local_read_byte_of_last_write
    {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L K A mem0 X) {g w e k : Nat} {a dst : Acc}
    {bs : List (Option Byte)} {written : List Byte}
    (hr : X.Reads (g, e) a bs) (hw : X.Writes (g, w) dst written) (hk : k < a.size)
    (hc : dst.Covers (a.loc.at k)) (hwe : w < e)
    (howner : ∀ ref d bytes, X.MemWrites ref d bytes → d.Covers (a.loc.at k) →
      ∃ j, ref = .thread (g, j) ∧ X.Access (g, j) d true)
    (hlast : ∀ j d, X.Access (g, j) d true → d.Covers (a.loc.at k) → j ≤ w ∨ e < j) :
    bs[k]? = some (wbyte dst written (a.loc.at k)) := by
  have hwa : X.Access (g, w) dst true := Or.inr (Or.inl ⟨written, hw, rfl⟩)
  have hra : X.Access (g, e) a false := Or.inl ⟨bs, hr, rfl⟩
  have hca := Acc.covers_at hk
  apply read_byte_of_last_write hX (e := .thread (g, e)) (w := .thread (g, w))
    (Or.inl hr) hk (Or.inl hw) hc
  · exact .inl (.single (.inl (po_of_overlap hwa hra rfl hwe ⟨a.loc.at k, hc, hca⟩)))
  · intro ref d bytes hmem hcov
    obtain ⟨j, rfl, ha⟩ := howner ref d bytes hmem hcov
    by_cases hj : j = w
    · exact Or.inl (by rw [hj])
    · rcases hlast j d ha hcov with hjw | hej
      · exact Or.inr (Or.inl (.inl (.single
          (.inl (po_of_overlap ha hwa rfl (by omega) ⟨a.loc.at k, hcov, hc⟩)))))
      · exact Or.inr (Or.inr (.inl (.single
          (.inl (po_of_overlap hra ha rfl hej ⟨a.loc.at k, hca, hcov⟩)))))


/-- A four-byte element of a vector load reassembles the low or high half of the saved
64-bit address. -/
theorem rebuild_b64_half (v : BitVec 64) (high : Bool) :
    let offset := if high then 4 else 0
    rebuild 3 ((List.range 4).map fun k => some ((Value.bits 64 v).byteAt (offset + k))) =
      .ok (.bits 32 (BitVec.ofNat 64 (v.toNat / 256 ^ offset % 2 ^ 32))) := by
  cases high <;>
    simp [rebuild, rebuild.halves, rebuildBits, littleEndianBits, byteBits, intByte,
      Value.bytes, Value.byteAt, Value.bitPattern, List.range_succ_eq_map]
  all_goals (congr 3; omega)

end

end PTX
