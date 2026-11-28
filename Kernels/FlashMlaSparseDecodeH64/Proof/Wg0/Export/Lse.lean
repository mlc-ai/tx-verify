-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Wg0
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Pred
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.LseSeq
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Addr

@[expose] public section

/-! # The LSE store's lane has an index below 64

The LSE store (pc 1178) is entered from the row-sum read only for a thread index word below 64
(`Wg0.lse_pred`), so the store of a followed lane writes row `64 (s_q ctaid.y + ctaid.x) + t`
with `t < 64`: the LSE output holds it (`MemRow.wg0Lse_in`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The site at pc 1178 is the LSE store. -/
private theorem site_lse {s : Wg0.Site} (h : s.pc = 1178) : s = .lse := by
  cases s
  case lse => rfl
  all_goals exfalso
  all_goals simp only [Wg0.Site.pc] at h
  all_goals try omega
  case sld arm k => cases arm <;> fin_cases k <;> simp at h
  case ost2 c k => fin_cases c <;> simp [Wg0.ost2Base] at h <;> omega
  all_goals (rename_i c; fin_cases c <;> simp at h)

/-- **The LSE store's lane**: a global write of warpgroup 0 at the LSE store's pc is made by a
lane whose thread index (mod 128) is below 64. -/
theorem wg0_lseLane (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} {a : Acc}
    {bs : List Byte} (he : X.get (g, k) = some e) (hat : Wg0At L g e.pc)
    (hk : e.kind = .wr a bs) (hpc : e.pc = 1178) : (L.tidOf g).x % 128 < 64 := by
  have hg := Frame.lt_of_get hX he
  have hkl : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hub : ∀ f, e.kind ≠ .ub f := fun f h => by rw [hk] at h; cases h
  obtain ⟨σ, hσ, hJ, hi, hev, hpcσ⟩ := ev_at hp hX hFw he hub
  obtain ⟨-, hlo, hhi⟩ := hat
  obtain ⟨d, n, rfl, -, -, hw⟩ := wg0_state hJ hi hev hpcσ ⟨hlo, hhi⟩
  have hs : d.site = .lse := site_lse (by rw [← hpc]; exact hpcσ.symm)
  rcases wg0_pred_pre hFw (noUbBefore_of_get hX he) hw hg hkl.le hσ with
      ⟨t', -, d', n', e', -, -, hS⟩ | h
  · obtain ⟨-, hc⟩ := Wg0.lse_pred hS hs
    have ht := tidOf_lt hp g
    have h4 : Wg0.Control.r5W L g = W (tidOf L g % 128) := andi_W_low (k := 7) ht (by decide)
    have h5 : pw 64 = W 64 := by simp only [pw, leNat_eq, pow_zero, Nat.div_one]; rfl
    rw [h4, h5, scmp_ge_W (by omega) (by omega)] at hc
    have := of_decide_eq_false hc
    show tidOf L g % 128 < 64
    omega
  · rw [hs] at h; cases h

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
