-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.StrictIndexRecv
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.NoUbAlign
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollIxCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexLive
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where

@[expose] public section

/-! # What an index event is, from its strictly good state

`ix_event`: the event at an index state is the site's (`Index.Ev`), no undefined behaviour, its
stores write the bytes of 32-bit (coordinates) or 8-bit (validity byte) values (`Index.Bits`), and
its loaded words are 32-bit. -/

/-! # An event at an index state fires from a strictly good state

`ix_strictAt`: at any position of an index lane, the state before the event is strictly good and
satisfies the tag invariant and the window's invariant, and fires its event; the event's own
well-formedness (`IxWfT`) holds. The window from the head's shuffle (`index_origin`) is
well formed (`ix_win` with `ix_shRecv`, counting the shuffles before the position). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc Index

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The strict state before an index event.** -/
theorem ix_strictAt (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {k : Nat} {e : Event} (he : X.get (g, k) = some e) {d : Index.D}
    {n : Cls → Nat} (hσ : Frame.stateAt (thread P L) X g k = some (some (idxState P L g d n))) :
    warpOf L g = 7 ∧ IxWfT P e ∧ IxInv P d ∧
      ∃ t1 o', (thread P L g).Good (some (idxState P L g d n)) t1 ∧ QT ixQt t1 ∧
        EStep kernel Assumptions.all L g t1 e o' := by
  have hg := Frame.lt_of_get hX he
  have hF := follow_iff.mp hFw g hg k
  obtain ⟨-, hR, -, -⟩ := hF.2 _ hσ
  obtain ⟨-, hgate, -⟩ : 3 ≤ n .shfl ∧ subOk L g .index = true ∧
      (n .ub = 0 → Index.Ref P L g d (fun c => n (.index c))) := hR
  have hw : warpOf L g = 7 := by simpa [subOk] using hgate
  obtain ⟨k0, n0, hlt, hk0⟩ := index_origin hσ
  have hW := ix_win hp hX hFw (ix_shRecv hp hX hFw (((X.tr g).take k).countP Execution.isShfl))
    hg hw hk0 (k - k0) (by rw [show k0 + (k - k0) = k by omega])
  rw [show k0 + (k - k0) = k by omega] at hW
  have hwf := ix_evWf hp hX hFw hg hw hk0 hlt he hW (fun md a b cc r ok hk =>
    ix_shRecv hp hX hFw (((X.tr g).take k).countP Execution.isShfl + 1) g k0 k n0 e md a b cc r ok
      hg hw hk0 hlt he hk (Nat.lt_succ_self _))
  obtain ⟨hok, t1, o', hgood, hq, hes⟩ := ix_windowAt hp hX hg hgate hk0 hlt hσ he hW
  rcases hok with ⟨-, n', h'⟩ | ⟨d', n', h', hi⟩
  · exact absurd (congrArg (fun x => x.1) h') (by simp)
  · obtain ⟨-, hd⟩ := Prod.mk.inj h'
    simp only [idxState, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and]
      at h'
    obtain ⟨rfl, -⟩ := h'
    exact ⟨hw, hwf, hi, t1, o', hgood, hq, hes⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The event at an index state.** -/
theorem ix_event (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {k : Nat} {e : Event} (he : X.get (g, k) = some e) {d : Index.D}
    {n : Cls → Nat} (hσ : Frame.stateAt (thread P L) X g k = some (some (idxState P L g d n))) :
    Index.Ev P L g d e ∧ (∀ f, e.kind ≠ .ub f) ∧ Index.Bits d e ∧
      (∀ a bs, e.kind = .nc a bs → ∃ y, rebuild 3 bs = .ok (.bits 32 y)) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨-, hwf, hi, t1, o', hgood, hq, hes⟩ := ix_strictAt hp hX hFw he hσ
  have hubK := noUbBefore_of_get hX he
  obtain ⟨-, hR, -, -⟩ := (follow_iff.mp hFw g hg k).2 _ hσ
  obtain ⟨-, -, hR'⟩ : 3 ≤ n .shfl ∧ subOk L g .index = true ∧
      (n .ub = 0 → Index.Ref P L g d (fun c => n (.index c))) := hR
  obtain ⟨i, -, -, -, -, hct⟩ := hR' (state_noUb hubK hσ) (state_noUbIx hubK hσ)
  obtain ⟨hok, -, -⟩ := ix_ok hp hX hσ d n rfl
  have hA : d.site = .lenA → eqz64 (pw8 (P.topkLenBase.getD 0)) = false := fun hs => by
    simp only [ixLenOk, hs] at hok
    exact hok.1
  have hB : d.site = .lenB → eqz64 (pw8 (P.extraTopkLenBase.getD 0)) = false := fun hs => by
    simp only [ixLenOk, hs] at hok
    exact hok.1
  have hal : Index.isLd d.site = true → (truncBits 64 (Index.ldAddr P L g d) +
      BitVec.ofInt 64 0).toNat % 8 = 0 := fun hl => by
    have hA' : d.site ≠ .lenA := fun h => by rw [h] at hl; simp [Index.isLd] at hl
    have hB' : d.site ≠ .lenB := fun h => by rw [h] at hl; simp [Index.isLd] at hl
    obtain ⟨h0, h1⟩ := ix_words_of hA' hB' hok
    exact Index.ldAddr_m8 hp hct.1 hl h0 h1
  obtain ⟨ins, hc, hf⟩ := Code.fired_of_good (thread_sound hp) hgood hes
  obtain ⟨hat, hinv⟩ := hgood
  have hnb := Index.noUbq_site hp d hA hB hal t1 ins e o' hat hinv.1 hc hq hf
  obtain ⟨hev, -, -⟩ := ix_evAt hp hX hFw he hnb.1 hσ
  exact ⟨hev, hnb.1, hnb.2, hwf.1.nc⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
