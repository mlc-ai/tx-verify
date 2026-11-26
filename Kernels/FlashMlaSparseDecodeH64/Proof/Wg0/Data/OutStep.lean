-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.EldStep
public import Lemmas.Flow.DataElect

@[expose] public section

/-! # The output chunks' tails

After the last staging store of a chunk the proxy fence, the named barrier, the election and the
TMA store keep the factor pair; the barrier and the election branch either on to the next chunk
or to the next site of the chunk: the sites of these facts form one class (`.old 0`), so the
successors of each are equal in it (`cls_obar`, `cls_oel`, `cls_otma`). `ds_el` is the data step
of the election, which writes a leader and a predicate. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

theorem cls_mem3 {s : Site} (h : s ∈ [Site.old 1, Site.old 2, Site.old 3]) :
    wcls s = wcls (.old 1) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h <;> simp [h, wcls]

theorem cls_obar (k : Fin 4) {c c' : Control.D} (hs : c.site = .obar k)
    (h : succOk c c' = true) : wcls c'.site = wcls (.oel k) := by
  simp only [succOk, hs, decide_eq_true_eq] at h
  rcases h with h | h
  · rw [h]
  · rw [cls_mem3 h]; simp [wcls]

theorem cls_oel (k : Fin 4) {c c' : Control.D} (hs : c.site = .oel k)
    (h : succOk c c' = true) : wcls c'.site = wcls (.otma k) := by
  simp only [succOk, hs, decide_eq_true_eq] at h
  rcases h with h | h
  · rw [h]
  · rw [cls_mem3 h]; simp [wcls]

theorem cls_otma (k : Fin 4) {c c' : Control.D} (hs : c.site = .otma k)
    (h : succOk c c' = true) : wcls c'.site = wcls (.old 1) := by
  simp only [succOk, hs, decide_eq_true_eq] at h
  exact cls_mem3 h

/-- **An election** into a leader register and a predicate the facts do not name. -/
theorem ds_el {d : D} {s s' : Site} {ty : Option DType} {r p : Nat} {mask : Opnd}
    (hs : d.c.site = s) (hna : s ≠ .arrS)
    (hc : kernel.code[s.pc]? = some ⟨none, .warp ⟨.elect, ty, [some r, some p], [], some mask⟩⟩)
    (he : Control.elems s = 1) (hsucc : ∀ c', succOk d.c c' = true → wcls c'.site = wcls s')
    (hst : isStart s = true → wF (scX L) s d.b = [])
    (hr : ∀ q ∈ wF (scX L) s d.b, q.1 ≠ r) (hp : ∀ q ∈ wF (scX L) s d.b, q.1 ≠ p)
    (hR : ∀ e, Reach kernel Assumptions.all L g (s.pc + 1) (wF (scX L) s d.b)
      (wF (scX L) s' (record d.c e d.b))) :
    DataStep (code P L g w) (dF L) d := by
  refine DataStep.elect (C' := code P L g w) (dF := dF L) (by rw [pc_eq hs]; exact hc) ?_
  intro hi mk inst ld d' t hn hat
  obtain ⟨c', -, rfl⟩ := next_ctl hn
  refine fin_reach (hs ▸ hna) (hsucc c') (fun h1 => ?_) (fun _ _ => hR _)
  obtain ⟨hp', hsb, ha, hf, hF⟩ := at_site hs hat (el0 hs hi he) (hs ▸ h1) hst
  exact ⟨by simp only [PTX.next, setReg]; omega, hsb, ha, hf,
    holds_update (holds_update hF hr) (fun q hq => hp q hq)⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
