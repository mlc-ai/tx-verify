-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.RefStep
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LenRead
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.NcRead

@[expose] public section

/-! # Warpgroup 0's two length loads read the row's lengths

-- domain: consistent

At a length load (`lenA`, pc 168; `lenB`, pc 181) the launch facts (`LaunchOk`) say the pointer
is set, so the event the state fires is the `.nc` read of the row's four bytes (`len_read`), and
in a consistent execution the read returns the row's length word (`rebuild_topk`,
`rebuild_extra`): `LenOk`, proved by `lenOk`. With it the machine never stops (`succ_live`): the
length loads continue with the launch's words (`succ_lenA`, `succ_lenB`), and no other site
stops; every step keeps the launch facts (`launch_step`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat} {w : BitVec 64}

/-- **The length reads of a step**: a `.nc` read at a length load returns the launch's word. -/
def LenOk (P : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  ∀ a bs, e.kind = .nc a bs →
    (d.site = .lenA → rebuild 3 bs = .ok (b32 (P.topkLen (ctaidY L g)))) ∧
      (d.site = .lenB → rebuild 3 bs = .ok (b32 (P.extraTopkLen (ctaidY L g))))

section
variable {X : Execution} {i : EvId} {d : D} {e : Event}
  (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hget : X.get i = some e)
include hp hX hget

/-- **A length load reads the launch's word**, from the state's launch facts and the site the
event fires from. -/
theorem lenOk (hl : LaunchOk P L g d)
    (hsite : (∀ f, e.kind ≠ .ub f) → ∃ t ins o, (code P L g w).AtD d t ∧
      (code P L g w).inv d ∧ kernel.code[(code P L g w).pc d]? = some ins ∧
      Fires ((code P L g w).pc d) (eventTmpl Assumptions.all L g t ins.op) e o) :
    LenOk P L g d e := by
  intro a bs hk
  obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ := hsite fun f h => by rw [hk] at h; cases h
  have hrow := (ctaid_lt hp g).2
  obtain ⟨hlA, hlB, -, -⟩ := hl
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · obtain ⟨x, hx⟩ := len_ptr (hlA hs)
    obtain ⟨bs', hk', hpcE⟩ := topk_read hp hx hs hat hinv hc hf
    obtain rfl : bs' = bs := by rw [hk] at hk'; cases hk'; rfl
    exact rebuild_topk hp hX hrow hx hget ⟨hk', hpcE⟩
  · obtain ⟨x, hx⟩ := len_ptr (hlB hs)
    obtain ⟨bs', hk', hpcE⟩ := extra_read hp hx hs hat hinv hc hf
    obtain rfl : bs' = bs := by rw [hk] at hk'; cases hk'; rfl
    exact rebuild_extra hp hX hrow hx hget ⟨hk', hpcE⟩

end

/-- A length load's read of the launch's word continues with that word. -/
theorem ncWord_launch {f : BitVec 64 → D} {e : Event} {n : Nat}
    (h : ∀ a bs, e.kind = .nc a bs → rebuild 3 bs = .ok (b32 n)) :
    ncWord e f ≠ some none := by
  unfold ncWord
  split
  · rename_i a bs hk
    rw [h a bs hk]
    simp [b32]
  · simp

set_option linter.unusedSimpArgs false in
/-- **The machine does not stop** at a step whose length reads are the launch's. -/
theorem succ_live {d : D} {e : Event} (hok : LenOk P L g d e) : succ P L g w d e ≠ some none := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases s with
  | lenA => exact ncWord_launch fun a bs hk => (hok a bs hk).1 rfl
  | lenB => exact ncWord_launch fun a bs hk => (hok a bs hk).2 rfl
  | _ =>
    intro h
    simp only [succ, dataRd, tcLoad, poll] at h
    repeat' split at h
    all_goals simp_all

/-- A length load the machine follows read a 32-bit word. -/
theorem ncWord_some {f : BitVec 64 → D} {e : Event} {d' : D} (h : ncWord e f = some (some d')) :
    ∃ a bs x, e.kind = .nc a bs ∧ rebuild 3 bs = .ok (.bits 32 x) ∧ d' = f x := by
  unfold ncWord at h
  split at h
  · rename_i a bs hk
    split at h
    · rename_i x hr
      exact ⟨a, bs, x, hk, hr, (Option.some.inj (Option.some.inj h)).symm⟩
    all_goals simp at h
  · simp at h

/-- **Every step keeps the launch facts**: the length loads set the launch's words. -/
theorem launch_step (hp : Pre P L m) {d d' : D} {e : Event} (hL : LaunchOk P L g d)
    (hok : LenOk P L g d e) (hn : succ P L g w d e = some (some d')) : LaunchOk P L g d' := by
  have hb := batch_in hp g
  by_cases hsA : d.site = .lenA
  · simp only [succ, hsA] at hn
    obtain ⟨a, bs, x, hk, hr, rfl⟩ := ncWord_some hn
    rw [(hok a bs hk).1 hsA] at hr
    obtain rfl : W (P.topkLen (ctaidY L g)) = x := by simpa [b32] using hr
    obtain ⟨hA, -, -, -⟩ := hL
    unfold afterA
    split <;> simp_all [LaunchOk, Site.lens, lenWA, lenWB, rowOf_cta]
  by_cases hsB : d.site = .lenB
  · simp only [succ, hsB] at hn
    obtain ⟨a, bs, x, hk, hr, rfl⟩ := ncWord_some hn
    rw [(hok a bs hk).2 hsB] at hr
    obtain rfl : W (P.extraTopkLen (ctaidY L g)) = x := by simpa [b32] using hr
    obtain ⟨-, hB, h0, -⟩ := hL
    simp_all [LaunchOk, Site.lens, lenWA, lenWB, rowOf_cta]
  exact launch_plain hb hL hsA hsB hn

/-- **The block count of a state that has both words** is its CTA's (`blocksOf`). -/
theorem rounds_blocks {d : D} (hL : LaunchOk P L g d) (h : 2 ≤ d.site.lens) :
    rounds d.l0 d.l1 = blocksOf P L (g / L.block) := by
  obtain ⟨-, -, h0, h1⟩ := hL
  rw [h0 (by omega), h1 h]
  rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
