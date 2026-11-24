-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2GatherWord
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawReadback

@[expose] public section

/-! # The actual raw and scale loads return the logical cache bytes -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open PTX PTX.Flow Wg2

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem load_values
    {g i issuer block off : Nat} {row : Fin 4} {a : Acc} {bs : List (Option Byte)}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hRead : X.Reads (g, i) a bs) (hc : ctaOf L issuer = ctaOf L g)
    (hSource : GatherSources P L X (g, i) issuer block row off a.size)
    (hEnd : off + a.size ≤ 528) :
    bytesNat bs < 256 ^ a.size ∧
      ∀ j < a.size,
        Numeric.byteAt (bytesNat bs) j =
          gatheredByte P L g block (rawRow L g row.val) (off + j) := by
  have hLen := (hX.rf (.thread (g, i)) a bs (.inl hRead)).1
  have hData := gather_window_bytes hpre hX hs hRead hSource hEnd
  have hBytes := unpack_gathered_word (g := issuer) (block := block) (off := off)
    (fun k hk => hData k (hLen ▸ hk))
  rw [hLen] at hBytes
  refine ⟨hBytes.1, fun j hj => (hBytes.2 j hj).trans (gatheredByte_same_cta hc)⟩

variable {g i : Nat} {d : D} {e : Event} {a : Acc} {bs : List (Option Byte)}

private theorem fired_read (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d))) (hk : e.kind = .rd a bs) :
    X.Reads (g, i) a bs ∧ ∃ u, (Machine.machine P L g).Fired (some (.wg2 d)) e (some u) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨o, hf⟩ := ((hs g hg).machine.produces (hX.thr g hg)).fired_at he hd
  have hr : X.Reads (g, i) a bs := by
    obtain ⟨tag, kind⟩ := e
    exact ⟨tag, by rw [he]; cases hk; rfl⟩
  cases o with
  | none =>
    obtain ⟨_, _, hf⟩ := hf
    rcases fires_none_ends hf with ⟨_, h⟩ | h <;> rw [hk] at h <;> cases h
  | some u => exact ⟨hr, u, hf⟩

/-- Each of the four bytes in an actual scale load agrees with its selected cache row. -/
theorem scale_load_bytes {row scale : Fin 4} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d)))
    (hSite : d.site = .scale row scale) (hk : e.kind = .rd a bs) :
    ∀ j < 4, Numeric.byteAt (scaleBits bs) j =
      gatheredByte P L g d.block (rawRow L g row.val) (512 + 4 * scale.val + j) := by
  obtain ⟨hr, u, hf⟩ := fired_read hX hs he hd hk
  obtain ⟨a', bs', hk', _, hz⟩ := fired_scale_event hpre hSite
    (show (Wg2.machine P L g).Fired (some (.inr d)) e (some u) from hf)
  obtain ⟨rfl, rfl⟩ := Kind.rd.inj (hk.symm.trans hk')
  obtain ⟨issuer, _, hc, hScale, _⟩ :=
    Protocol.RawReadback.actual_dequant_load_sources hpre hX hs he hd hf
  have hEnd : 512 + 4 * scale.val + a.size ≤ 528 := by have := scale.isLt; omega
  have hSource : GatherSources P L X (g, i) issuer d.block row (512 + 4 * scale.val) a.size := by
    rw [hz]
    exact hScale row scale hSite
  have hv := load_values hpre hX hs hr hc hSource hEnd
  rw [hz] at hv
  simpa only [scaleBits, Nat.mod_eq_of_lt hv.1] using hv.2

/-- Each of the eight bytes in an actual raw load agrees with its selected cache row. -/
theorem raw_load_bytes {row : Fin 4} {step : Fin 8} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d)))
    (hSite : d.site = .raw row step) (hk : e.kind = .rd a bs) :
    ∀ j < 8, Numeric.byteAt (rawBits bs) j =
      gatheredByte P L g d.block (rawRow L g row.val) (elemByte L g step.val j) := by
  obtain ⟨hr, u, hf⟩ := fired_read hX hs he hd hk
  obtain ⟨a', bs', hk', _, hz⟩ := fired_raw_event hpre hSite
    (show (Wg2.machine P L g).Fired (some (.inr d)) e (some u) from hf)
  obtain ⟨rfl, rfl⟩ := Kind.rd.inj (hk.symm.trans hk')
  obtain ⟨issuer, _, hc, _, hRaw⟩ :=
    Protocol.RawReadback.actual_dequant_load_sources hpre hX hs he hd hf
  have hz : a.size = 8 := hz
  have hEnd : elemByte L g step.val 0 + a.size ≤ 528 := by
    have h := elemByte_lt (L := L) (g := g) step.isLt (e := 7) (by decide)
    simp only [elemByte, quantBytes, Nat.add_zero] at h ⊢
    omega
  have hSource : GatherSources P L X (g, i) issuer d.block row
      (elemByte L g step.val 0) a.size := by
    rw [hz]
    exact hRaw row step hSite
  have hv := load_values hpre hX hs hr hc hSource hEnd
  rw [hz] at hv
  have hWord : bytesNat bs < 2 ^ 64 := hv.1
  intro j hj
  simpa only [rawBits, Nat.mod_eq_of_lt hWord, elemByte, Nat.add_zero] using hv.2 j hj

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
