-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.DataState
public import Kernels.InklingRelDecode.Proof.Common.WarpColl
public import Lemmas.Kernel.Progress.WarpCls
import Kernels.InklingRelDecode.Proof.Common.DataColl
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Kernels.InklingRelDecode.Proof.Common.ElectOrdinal
import Kernels.InklingRelDecode.Proof.Common.LaunchRounds
import Kernels.InklingRelDecode.Proof.Common.PreloadOrder
import Kernels.InklingRelDecode.Proof.Common.StartupEvents
import Kernels.InklingRelDecode.Proof.Common.TcCount
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent

@[expose] public section

/-! # The collectives a data lane has made, against its script

`data_cnt`: at every state a data lane reaches, the number of warp collectives it has made is what
`DataCnt` says of its state, from the ordinals of its shuffles and elections. -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

private theorem pro_block_pc (s : Prologue.Site) (b : Fin 3) (h : s.block = some b) :
    41 < s.pc := by
  have ck : Prologue.allSites.all (fun s => s.block.isNone || decide (41 < s.pc)) = true := by
    decide +kernel
  have := List.all_eq_true.mp ck s (ds_mem_all s)
  simp only [h, Option.isNone_some, Bool.false_or, decide_eq_true_eq] at this
  exact this

private theorem shuf_loop (s : Softmax.Site) (h : s.isShuffle = true) :
    s ≠ .setMaxReg ∧ s ≠ .bar0 ∧ (∀ j, s ≠ .pre j) ∧ s ≠ .epilogue := by
  cases s <;> simp_all [Softmax.Site.isShuffle]

/-- A prologue site of a block is one of the preloaded blocks. -/
private theorem gate_of {w d n} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hk : k ≤ (X.tr g).length)
    (hs : stateAt (thread Q L) X g k = some (some (proState w d n))) (nu : NoUbBefore X g k) :
    ∀ b : Fin 3, d.site.block = some b → b.val < Iface.preloadCount Q L (g / L.block) := by
  intro b hb
  have hist := (data_reference hp hX hk hs (prefix_ub_zero hs nu)).1
  have c41 := pro_block_pc _ b hb
  have cap := Prologue.preload_count hp hg (hist.known.first (by omega))
    (hist.known.last (by omega)) (hist.known.seq (by omega))
  have := hist.block b hb
  have := b.isLt
  omega

private theorem data_n {σ : (thread Q L g).D} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (lane : g % L.block < 128)
    (hs : stateAt (thread Q L) X g k = some (some σ)) (nu : NoUbBefore X g k) :
    Sched.collCount X g k = σ.2 .shfl + σ.2 .elect := by
  rw [data_collCount hp hX lane nu, fcount hs, fcount hs]
  rfl

/-- **A data lane's state** says how many collectives the lane has made. -/
theorem data_cnt {σ : (thread Q L g).D} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hg : g < L.threads)
    (lane : g % L.block < 128) (hk : k ≤ (X.tr g).length)
    (hs : stateAt (thread Q L) X g k = some (some σ)) (nu : NoUbBefore X g k) :
    DataCnt (Iface.preloadCount Q L (g / L.block)) (Lib.blocksOf Q L (g / L.block)) σ
      (Sched.collCount X g k) := by
  rw [data_n hp hX lane hs nu]
  obtain ⟨s, n⟩ := σ
  rcases s with st | ⟨r, d⟩
  · have a := shfl_startup_exact hp hX hk hs nu
    have b := elect_startup hp hX hk hs nu
    change n .shfl + n .elect = startCount st.site
    rw [a, b]
    cases st.site <;> rfl
  rcases r with r | r
  · cases r with
    | dispatch w x => exact absurd (worker_warp hp hX hk hs).1 (by omega)
    | prologue w =>
      rcases d with d | ⟨ent, d | ⟨u, d⟩⟩
      · have a := shfl_prologue hp hX hk hs nu
        have b := elect_prologue hp hX hk hs nu
        refine ⟨?_, gate_of hp hX hg hk hs nu⟩
        show n .shfl + n .elect = proCount _ d.site
        unfold proCount
        omega
      · have a := shfl_ordinal hp hX hk hs nu
        have b := elect_late hp hX hk hs nu
        have tbl := reached_table hf hg nu hs
        have inv : Softmax.Control.Inv ent (g % L.block) d := tbl.1.1
        have lim := reached_limit hp hX hg hk hs
        have pv := shfl_previous hp hX hk hs nu
        have noEpi : d.site ≠ .epilogue := fun e => by have := tbl.1.2; simp [epiExit, e] at this
        have early : d.i < ent.limit ∨ ent.limit = 0 := by
          by_cases e0 : d.i = 0
          · by_cases l0 : ent.limit = 0
            · exact .inr l0
            · exact .inl (by omega)
          · exact .inl (inv.loop noEpi (fun e => e0 (inv.init (.inl e)))
              (fun e => e0 (inv.init (.inr e))) fun j e => e0 (inv.pre j e).1)
        refine ⟨?_, noEpi, fun sh => ?_, ?_, pv⟩
        · show n .shfl + n .elect = softCount _ d.i d.site
          unfold softCount
          rw [a, b]
          simp only [Softmax.shflCount]
          omega
        · obtain ⟨h1, h2, h3, h4⟩ := shuf_loop _ sh
          rw [← lim]
          exact inv.loop h4 h1 h2 h3
        · rw [← lim]
          exact early
      · have a1 := shfl_epilogue hp hX hk hs nu
        have a2 := (shfl_epi hp hX hk hs nu).1
        have a3 := (shfl_epi hp hX hk hs nu).2.2
        have b := elect_epi hp hX hk hs nu
        have lim := reached_both hp hX hg hk hs
        have live := (tc_inv hp hX hf hg hk hs nu).2
        have sk : (epiEntry ent (g % L.block)).skip = decide (ent.limit = 0) := lim.1.2
        refine ⟨?_, fun sh => ?_, fun nw nh nz => ?_⟩
        · show _ ≤ n .shfl + n .elect
          unfold epiBase
          rw [← lim.1.1]
          omega
        · have lv : (epiEntry ent (g % L.block)).skip = false := live (.inl sh)
          rw [sk] at lv
          have nz : ent.limit ≠ 0 := by simpa using lv
          refine ⟨?_, by rw [← lim.1.1]; exact nz⟩
          show n .shfl + n .elect = epiBase _ _
          unfold epiBase
          rw [← lim.1.1]
          have := a2 (.inr sh)
          omega
        · have past : Epilogue.pastShfl d.site = true := by
            cases h : d.site <;> simp_all [Epilogue.pastShfl]
          have lv : (epiEntry ent (g % L.block)).skip = false := by
            rw [sk]; simpa using fun h => nz (by rw [← lim.1.1]; exact h)
          have := a3 past lv
          show epiBase _ _ + 1 ≤ n .shfl + n .elect
          unfold epiBase
          rw [← lim.1.1]
          omega
  · exact no_stub hp hX hk hs

end PTX.Kernels.InklingRelDecode.Proof
