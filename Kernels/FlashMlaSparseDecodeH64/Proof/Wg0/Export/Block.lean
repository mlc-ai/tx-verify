-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Wg0
public import Lemmas.Flow.Polls
public import Lemmas.Flow.Counted
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Lane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Objs
import Lemmas.Kernel.UbLast

@[expose] public section

/-! # Warpgroup 0's block of a Tensor Memory store

-- domain: consistent

Warpgroup 0's Tensor Memory stores are the rescale arm's (`rst c`, pcs 814/915/1016/1117) of some
block `r` of the loop. At such a store the lane has polled `qk_done` once per block up to `r`
(the poll at 272 of block `r` included) and arrived on `so_ready` once per block before `r` (the
arrival at 1122 of block `r` comes later): `wg0_stBlock`, read off the reference invariant's
counts at the site (`Wg0.acq_qk`, `Wg0.arr_so`). The machine steps from `rst c` to its wait
`rstw c` (`tcgen05.wait::st`), so a lane with any later event that is not undefined behaviour
has its store's wait as its next event (`wg0_stWait`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A site whose event is a Tensor Memory store is a rescale store. -/
private theorem st_site {g : Nat} {w : BitVec 64} {d : Wg0.Control.D} {e : Event} {a : Nat}
    {vals : List Value} {sh : TcShape} (h : Wg0.EvK P L g w d e)
    (hk : e.kind = .tc (.st a vals sh)) : ∃ c, d.site = .rst c := by
  obtain ⟨site, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases site <;> simp [Wg0.EvK, Wg0.PollEv, Wg0.ArrEv, GWrAt, RdAt, WrAt, GenWrAt, Wg0.NcEv,
    Wg0.TcLdEv, Wg0.TcStEv, hk] at h ⊢

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
include hp hX hFw

/-- **The block of a store of warpgroup 0**: at a store of block `r` the lane's successful polls
of `qkDone j` are the uses of slot `j` among blocks `0 … r`, its arrivals on `soReady j` those
among blocks `0 … r - 1`. -/
theorem wg0_stBlock {h k pc a : Nat} {vals : List Value} {sh : TcShape}
    (he : X.get (h, k) = some ⟨pc, .tc (.st a vals sh)⟩) (hat : MbarRow.Wg0At L h pc) :
    ∃ r, ∀ j : Fin 2,
      okPolls (mbarLoc L (h / L.block) (.qkDone j)) ((X.tr h).take k) = ringUses 2 j (r + 1) ∧
      arrivals (mbarLoc L (h / L.block) (.soReady j)) ((X.tr h).take k) = ringUses 2 j r := by
  obtain ⟨hw, hlo, hhi⟩ := hat
  have hub : ∀ f, (⟨pc, .tc (.st a vals sh)⟩ : Event).kind ≠ .ub f := fun _ h => by cases h
  obtain ⟨d, hR, ⟨-, hk⟩, -⟩ := wg0_at hp hX hFw he hub ⟨hlo, hhi⟩
  obtain ⟨hc, -⟩ := hR (wg0_take_noUb hX he)
  obtain ⟨c, hs⟩ := st_site hk rfl
  simp only [Wg0.RefCore, hs, Wg0.Site.reg, Wg0.Site.idx, Wg0.RefAt] at hc
  obtain ⟨r, -, hq, ha⟩ := hc
  dsimp only at hq ha
  refine ⟨r, fun j => ⟨?_, ?_⟩⟩
  · rw [show mbarLoc L (h / L.block) (.qkDone j) = loc L h (.qkDone j) from rfl,
      wg0_okPolls hp hX hFw hw, hq, Wg0.acq_qk hp]
    have := j.isLt
    unfold Wg0.use Wg0.ind ringUses
    split_ifs <;> omega
  · rw [show mbarLoc L (h / L.block) (.soReady j) = loc L h (.soReady j) from rfl,
      wg0_arrivals hp hX hFw hw, ha, Wg0.arr_so hp]

/-- **A store's wait follows it**: a lane of warpgroup 0 with an event past its store that is not
undefined behaviour has the store's `tcgen05.wait::st` as its next event. -/
theorem wg0_stWait {h k e pc a : Nat} {vals : List Value} {sh : TcShape} {f : Event}
    (hst : X.get (h, k) = some ⟨pc, .tc (.st a vals sh)⟩) (hat : MbarRow.Wg0At L h pc)
    (hf : X.get (h, e) = some f) (hu : ∀ fl, f.kind ≠ .ub fl) (hke : k < e) :
    ∃ pc', X.get (h, k + 1) = some ⟨pc', .tc .waitSt⟩ := by
  have hub : ∀ f, (⟨pc, .tc (.st a vals sh)⟩ : Event).kind ≠ .ub f := fun _ h => by cases h
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw hst hub
  obtain ⟨d, n, rfl, -, ⟨-, hk⟩, -⟩ := wg0_state hJ hi hev hpc ⟨hat.2.1, hat.2.2⟩
  obtain ⟨c, hs⟩ := st_site hk rfl
  have hlen : e < (X.tr h).length := (List.getElem?_eq_some_iff.mp hf).1
  obtain ⟨f', hf'⟩ : ∃ f', X.get (h, k + 1) = some f' :=
    ⟨_, List.getElem?_eq_getElem (l := X.tr h) (by omega)⟩
  have hu' : ∀ fl, f'.kind ≠ .ub fl := by
    intro fl hfl
    obtain ⟨pc'', kd⟩ := f'
    simp only at hfl
    subst hfl
    have hle := ub_last hX hf' hf
    obtain rfl : e = k + 1 := by omega
    rw [hf] at hf'
    cases hf'
    exact hu fl rfl
  have hn : (frag P L h .wg0).next d ⟨pc, .tc (.st a vals sh)⟩ =
      some (some { d with site := .rstw c }) := by
    show Wg0.Control.succ P L h (warpW L h) d _ = _
    unfold Wg0.Control.succ
    rw [hs]
  have hσ' : Frame.stateAt (thread P L) X h (k + 1) =
      some (some (.inr ⟨.inl .wg0, { d with site := .rstw c }⟩,
        Code.bump cls n ⟨pc, .tc (.st a vals sh)⟩)) := by
    rw [Frame.stateAt_succ hst, hσ]
    show (thread P L h).next _ _ = _
    rw [next_frag, hn]
    rfl
  obtain ⟨σ', hσ'', hJ', hi', hev', hpc'⟩ := ev_at hp hX hFw hf' hu'
  rw [hσ'] at hσ''
  obtain rfl := Option.some.inj (Option.some.inj hσ'')
  have hr : 103 ≤ f'.pc ∧ f'.pc < 1842 := by
    rw [hpc']
    show 103 ≤ Wg0.Site.pc (.rstw c) ∧ Wg0.Site.pc (.rstw c) < 1842
    fin_cases c <;> decide
  obtain ⟨d', n', ⟨⟩, -, ⟨-, hk'⟩, -⟩ := wg0_state hJ' hi' hev' hpc' hr
  simp only [Wg0.EvK] at hk'
  obtain ⟨pc', kd⟩ := f'
  rcases hk' with hk' | ⟨fl, hk'⟩
  · simp only at hk'
    subst hk'
    exact ⟨pc', hf'⟩
  · exact absurd hk' (hu' fl)

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
