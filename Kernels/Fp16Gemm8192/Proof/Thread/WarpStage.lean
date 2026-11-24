-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.WarpFire
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaLeader
public import Kernels.Fp16Gemm8192.Proof.Thread.Tracked
public import Kernels.Fp16Gemm8192.Proof.Thread.ExitSite
public import Kernels.Fp16Gemm8192.Proof.Thread.TmemFacts
public import Kernels.Fp16Gemm8192.Proof.Thread.RoleWarp
public import Lemmas.Flow.Alloc

@[expose] public section

/-! # The prologue's collective sites along a thread's run

The prologue runs warp 0 through the shuffle, its election and its warp barrier at fixed
positions of the thread's events (`Prologue.index`): 0, 1 and `wbIdx` (3, or 22 for the CTA's
thread 0, which initializes the mbarriers and writes the Tensor Memory column first). A thread
at such a site has made none of its events (`coll_none_fact`); a lane of its warp has made the
site's
event, or is at the site, or at an earlier site, or stopped before it (`coll_lane_fact`). Only the
warp
barrier instruction fires a warp barrier (`fires_notWarpBar_op`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

/-! ## Warp barrier events of instructions that are not warp barriers -/

/-- A template that is not a warp barrier. -/
def NotWarpBar : Tmpl → Prop
  | .warpBar .. => False
  | _ => True

theorem fires_notWarpBar {pc : Nat} {m : Tmpl} {e : Event} {o : Option TState}
    (hm : NotWarpBar m) (hf : Fires pc m e o) : ∀ mask inst, e.kind ≠ .warpBar mask inst := by
  intro mask inst he
  obtain ⟨pe, ke⟩ := e
  cases m <;> simp only [NotWarpBar] at hm <;> simp only [Fires] at hf <;> aesop

theorem ofExec_notWarpBar {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotWarpBar r) :
    NotWarpBar (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

theorem widen_notWarpBar {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotWarpBar m) :
    NotWarpBar (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m
    all_goals try exact h
    case arrive m tx t count release scope =>
      cases release <;> cases scope <;> exact trivial
    case wait m parity k acquire scope =>
      cases acquire <;> cases scope <;> exact trivial
  · exact h

/-- Every instruction other than a warp barrier fires no warp barrier event. -/
theorem eventTmpl_notWarpBar {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : ∀ w : WarpInstr, op = .warp w → w.kind ≠ .barWarp) :
    NotWarpBar (eventTmpl A L g t op) := by
  cases op
  case warp w =>
    rcases w with ⟨⟨⟩, _, _, _, _⟩ <;> first
      | exact absurd rfl (hop _ rfl)
      | (simp only [eventTmpl, warpTmpl, electTmpl, shflTmpl, voteTmpl,
           voteModeTmpl, reduxTmpl, matchTmpl, activemaskTmpl]
         repeat' first
           | trivial
           | split)
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine Flow.tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notWarpBar
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notWarpBar)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | dsimp only)
    | (simp only [memTmpl, accessTmpl, atomTmpl, bulkInitTmpl, acquireLoadTmpl,
        releaseStoreTmpl, loadTmpl, storeTmpl,
        barTmpl, SetMaxNReg.tmpl, fenceTmpl, cpAsyncTmpl, asyncStoreTmpl,
        matrixTmpl, matrixMoveTmpl, tensorTmpl, tensorStoreTmpl,
        tensorPrefetchTmpl, clcTmpl, tcCommitTmpl,
        tcTmpl, mmaTmpl, localSregTmpl, sregTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notWarpBar)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | (dsimp only; done)
         | dsimp only)
    | trivial

theorem fires_notWarpBar_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState}
    (hop : ∀ w : WarpInstr, op = .warp w → w.kind ≠ .barWarp)
    (hf : Fires pc (eventTmpl A L g t op) e o) : ∀ mask inst, e.kind ≠ .warpBar mask inst :=
  fires_notWarpBar (eventTmpl_notWarpBar hop) hf

/-- The prologue sites other than the warp barrier are not warp barriers. -/
theorem Prologue.notWarpBar_site {s : Prologue.Site} (hs : s ≠ .warpBar) {ins : Instr}
    (hc : kernel.code[s.pc]? = some ins) :
    ∀ w : WarpInstr, ins.op = .warp w → w.kind ≠ .barWarp := by
  intro w h
  cases s with
  | shfl => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_0); cases h; nofun
  | elect => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_0); cases h; nofun
  | init i =>
    rw [code_init_op i] at hc
    obtain rfl := Option.some.inj hc
    cases h
  | alloc => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0); cases h
  | allocWrite => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0); cases h
  | warpBar => exact (hs rfl).elim
  | fence => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceProxy_0); cases h
  | fenceInit => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceMbarInit_0); cases h
  | arrive => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterArrive_0); cases h
  | wait => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterWait_0); cases h
  | setMaxReg => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_0); cases h
  | roleElect => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_1); cases h; nofun

/-- The warp barrier fires a full-mask warp barrier event. -/
theorem fires_warpBar_full {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {pc : Nat}
    {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t (.warp ⟨.barWarp, none, [], [], some (.imm (-1))⟩)) e o) :
    ∃ inst, e = ⟨pc, .warpBar fullMask inst⟩ := by
  have hlane : laneOf L g < 32 := Nat.mod_lt _ (by norm_num)
  have hb : (truncBits 32 (BitVec.ofInt 64 (-1))).toNat = fullMask := by decide
  have hmem : electMember (truncBits 32 (BitVec.ofInt 64 (-1))).toNat (laneOf L g) := by
    refine ⟨hlane, ?_⟩
    have h32 : (4294967295 : Nat) = 2 ^ 32 - 1 := by norm_num
    rw [hb, fullMask, h32, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hlane
  simp only [eventTmpl, warpTmpl_barWarp, warpBarTmpl, readBits, pure, Except.pure] at hf
  rw [ite_eq_left hmem] at hf
  obtain ⟨inst, rfl, -⟩ := hf
  exact ⟨inst, by rw [hb]⟩

/-- Lane 0's address store fires a write, unless it is undefined behaviour. -/
theorem fires_tcAlloc_wr {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {group : CtaGroup} {base : Nat} {off : Int} {nc : Opnd} {pc : Nat} {e : Event}
    {o : Option TState} (hs : t.sub = 1)
    (hf : Fires pc (eventTmpl A L g t (.tcAlloc group base off nc)) e o)
    (hnu : ∀ f, e ≠ ⟨pc, .ub f⟩) : ∃ a bs, e = ⟨pc, .wr a bs⟩ := by
  simp only [eventTmpl, tcTmpl] at hf
  cases hd : effAddr L g t .shared base off with
  | error f =>
    simp [ofExec, hd, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, Fires] at hf
    split_ifs at hf <;> simp at hf <;> exact absurd hf.1 (hnu _)
  | ok dst =>
    cases hn : readBits L g t 32 nc with
    | error f =>
      simp [ofExec, hd, hn, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, Fires] at hf
      split_ifs at hf <;> simp at hf <;> exact absurd hf.1 (hnu _)
    | ok n =>
      simp [ofExec, hd, hn, hs, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw] at hf
      split_ifs at hf
      all_goals first
        | (simp only [Fires] at hf; obtain ⟨_, -, he, -⟩ := hf; exact ⟨_, _, he⟩)
        | (simp only [Fires] at hf; exact absurd hf.1 (hnu _))

end
end PTX.Kernels.Fp16Gemm8192.Proof
