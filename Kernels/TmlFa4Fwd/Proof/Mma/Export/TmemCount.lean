-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Flow.GlueStep
public import Kernels.TmlFa4Fwd.Proof.Lib.WarpIndex
public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.Mma.Shape
public import Kernels.TmlFa4Fwd.Proof.Startup.Shape
public import Kernels.TmlFa4Fwd.Proof.Mma.Tmem.Site
public import Lemmas.Kernel.Frame
public import Lemmas.Tmem.PairProtocol
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Common.SharedSites
import Kernels.TmlFa4Fwd.Proof.Mma.Export.SafePre
import Kernels.TmlFa4Fwd.Proof.Mma.Warp
import Lemmas.Kernel.UbLast
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The MMA warp's Tensor Memory operations, counted along its trace

The thread's count of Tensor Memory resource events before a position (`Tmem.Pair.tmemOps`) is a
function of the thread machine's state there (`tcnt`): `0` until the allocation, `1` after it,
`2` after the relinquishment, `3` after the deallocation. The MMA warp's role reaches its last
three sites only in the order relinquish, barrier, deallocate, exit (`mma_succ_tsite`); its
allocation prefix allocates once; no other site fires a resource event. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The resource operations before a state of the thread machine. -/
def tcnt (p : Params) (L : Launch) (g : Nat) : (thread p L g).D → Nat
  | (.inr ⟨.mma, .inl s⟩, _) => match s with
    | .set | .alloc => 0
    | .wr | .enter => 1
  | (.inr ⟨.mma, .inr ⟨_, d⟩⟩, _) => Mma.tsite d.site
  | _ => 0

/-- The output warp fires no resource event. -/
theorem epi_nores {d : Epilogue.D} {e : Event} {grp : CtaGroup} {dst : Option Loc}
    {act : Tmem.Request} (hev : Epilogue.Ev p L g d e) (hk : e.kind = .tc (.resource grp dst act)) :
    False := by
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  unfold Epilogue.Ev at hev
  split at hev <;> simp_all [Epilogue.isStore]

set_option maxHeartbeats 4000000 in
/-- **Only the relinquish and deallocation sites of the MMA warp's role fire a resource event.** -/
theorem Mma.ev_res {d : Mma.D} {e : Event} {grp : CtaGroup} {dst : Option Loc}
    {act : Tmem.Request} (hev : Mma.Ev p L g d e) (hk : e.kind = .tc (.resource grp dst act)) :
    Mma.isRD d.site = true := by
  obtain ⟨site, v⟩ := d
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  unfold Mma.Ev at hev
  split at hev <;> first
    | rfl
    | (subst ‹site = _›; rfl)
    | exact (epi_nores hev rfl).elim
    | simp_all

set_option maxHeartbeats 4000000 in
/-- **The resource events of the MMA warp's role**: at the relinquish site the relinquishment, at
the deallocation site the deallocation of 512 columns, in group one. -/
theorem Mma.rd_kind (hp : Pre p L m) {d : Mma.D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (h : (Mma.code p L g (Mma.ent p L)).AtD d t)
    (hc : kernel.code[(Mma.code p L g (Mma.ent p L)).pc d]? = some ins)
    (hf : Fires ((Mma.code p L g (Mma.ent p L)).pc d)
      (eventTmpl Assumptions.all L g t ins.op) e o)
    (hub : ∀ f, e.kind ≠ .ub f) :
    ((∃ l, d.site = .relinq l) → e.kind = .tc (.resource .one none .relinquish)) ∧
    ((∃ l, d.site = .dealloc l) → ∃ a, e.kind = .tc (.resource .one none (.dealloc a 512))) := by
  have hb : L.block % 32 = 0 := by rw [hp.block]
  replace h : At t d.site.pc (Mma.facts p L g (Mma.ent p L) d) :=
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  replace hc : kernel.code[d.site.pc]? = some ins := hc
  obtain ⟨site, v⟩ := d
  refine ⟨fun ⟨l, hl⟩ => ?_, fun ⟨l, hl⟩ => ?_⟩
  · simp only at hl
    subst hl
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2763)
    simp only [eventTmpl, tcTmpl, ofExec, hb, bind, Except.bind, pure, Except.pure] at hf
    simp at hf
    exact hf.1 ▸ rfl
  · simp only at hl
    subst hl
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2766)
    have h2 : t.regs 2682 = some (b32 512) :=
      Mma.reg_bits h (by show 2682 ∈ Flow.live 2766; lit_mem) rfl
    have hn := readBits_b32 (L := L) (g := g) h2 (by decide)
    revert hf
    cases hta : readBits L g t 32 (.reg 1179) with
    | error f' =>
      simp [eventTmpl, tcTmpl, ofExec, hb, hta, bind, Except.bind, Fires]
      intro hf _
      exact absurd hf (fun h => hub f' (by rw [h]))
    | ok a =>
      simp [eventTmpl, tcTmpl, ofExec, hb, hta, hn, bind, Except.bind, pure, Except.pure,
        Tmem.validColumns, Fires]
      intro hf _
      exact ⟨_, by rw [hf]⟩

/-- The startup fires no resource event. -/
theorem start_nores {s : Startup.D} {e : Event} (hev : Startup.Ev L g s e)
    (hx : exit L g s = none) : Tmem.Pair.isTmemOp e = false := by
  obtain ⟨site, x1, x2, x3⟩ := s
  obtain ⟨pc, kind⟩ := e
  cases site with
  | sh j =>
    fin_cases j <;> simp only [Startup.Ev] at hev <;> obtain ⟨r, ok, hk⟩ := hev <;>
      (try simp only at hk) <;> subst hk <;> rfl
  | elect j =>
    simp only [Startup.Ev] at hev
    rcases hev with ⟨_, _, _, hk⟩ | ⟨f, hk⟩ <;> (try simp only at hk) <;> subst hk <;> rfl
  | init q =>
    simp only [Startup.Ev] at hev
    rcases hev with ⟨l', c, hk⟩ | ⟨f, hk⟩ <;> (try simp only at hk) <;> subst hk <;> rfl
  | fence => simp only [Startup.Ev] at hev; subst hev; rfl
  | bar => simp only [Startup.Ev] at hev; subst hev; rfl
  | enter r => simp [exit] at hx

/-- A role's first state counts no resource operation. -/
theorem tcnt_enter (s : Startup.D) (n : Cls → Nat) :
    tcnt p L g (Code.enter (Startup.code p L g) (frag p L g) (exit L g) s, n) = 0 := by
  unfold Code.enter
  split
  · rename_i i _
    cases i <;> rfl
  · rfl

theorem isTmemOp_eq {e : Event} (h : Tmem.Pair.isTmemOp e = true) :
    ∃ grp dst act, e.kind = .tc (.resource grp dst act) := by
  obtain ⟨pc, kind⟩ := e
  cases kind <;> simp [Tmem.Pair.isTmemOp] at h
  rename_i k
  cases k <;> simp at h
  exact ⟨_, _, _, rfl⟩

theorem tmemOps_snoc {es : List Event} {e : Event} :
    Tmem.Pair.tmemOps (es ++ [e]) = Tmem.Pair.tmemOps es +
      (if Tmem.Pair.isTmemOp e then 1 else 0) := by
  simp only [Tmem.Pair.tmemOps, List.countP_append, List.countP_singleton]

set_option maxHeartbeats 8000000 in
/-- A lane of the MMA warp has made `tcnt` resource operations before each state with no undefined
behaviour so far. -/
theorem mma_count_at (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (h12 : Prologue.warpIndex L g = 12) :
    ∀ k, k ≤ (X.tr g).length → (∀ j < k, ∀ e f, X.get (g, j) = some e → e.kind ≠ .ub f) →
      ∀ σ, Frame.stateAt (thread p L) X g k = some (some σ) →
      Tmem.Pair.tmemOps ((X.tr g).take k) = tcnt p L g σ := by
  have hReads := cuQReadsFromLaunch hp hX
  intro k
  induction k with
  | zero =>
    intro _ _ σ hσ
    rw [Frame.stateAt_zero] at hσ
    cases hσ
    simp only [List.take_zero, Tmem.Pair.tmemOps, List.countP_nil]
    exact (tcnt_enter _ _).symm
  | succ k ih =>
    intro hk hno σ hσ
    obtain ⟨e, he⟩ : ∃ e, X.get (g, k) = some e :=
      ⟨_, List.getElem?_eq_getElem (show k < (X.tr g).length by omega)⟩
    have hub : ∀ f, e.kind ≠ .ub f := fun f => hno k (by omega) e f he
    have hstep := Frame.stateAt_succ (C := thread p L) (show (X.tr g)[k]? = some e from he)
    rw [hσ] at hstep
    have htake : (X.tr g).take (k + 1) = (X.tr g).take k ++ [e] := by
      rw [List.take_add_one, show (X.tr g)[k]? = some e from he, Option.toList_some]
    rw [htake, tmemOps_snoc]
    cases hσ0 : Frame.stateAt (thread p L) X g k with
    | none => rw [hσ0] at hstep; simp at hstep
    | some o =>
      cases o with
      | none => rw [hσ0] at hstep; simp [Code.toMachine] at hstep
      | some σ0 =>
        rw [hσ0] at hstep
        have hn : (thread p L g).next σ0 e = some (some σ) := hstep.symm
        rw [ih (by omega) (fun j hj => hno j (by omega)) σ0 hσ0]
        have hJ := (Mma.good hp hX hReads hg h12 k).2 σ0 hσ0
        obtain ⟨σ1, n0⟩ := σ0
        obtain ⟨σ', n'⟩ := σ
        obtain ⟨h1, -⟩ := Code.counted_next_some (C := glued p L g) hn
        rcases σ1 with s | ⟨i, d⟩
        · have hE := start_fired hp hX he hσ0
          rw [start_nores hE.1 hE.2.1]
          obtain ⟨s', -, rfl⟩ := Code.glue_inl_some h1
          show 0 + 0 = tcnt p L g (Code.enter (Startup.code p L g) (frag p L g) (exit L g) s',
            n')
          rw [tcnt_enter]
        cases i with
        | mma =>
          rcases d with s0 | ⟨⟨⟩, d⟩
          · obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ :=
              strict_fired_site hp hX he hσ0 rfl
            have hk3 := Mma.pre_kind hp hat hc hf
            simp only [glued, Code.glue, frag, Mma.M, Mma.G, Mma.S] at h1
            cases s0 with
            | set =>
              obtain ⟨inst, hki⟩ := hk3.1 rfl
              simp only [Option.map_some, Option.some.injEq] at h1
              subst h1
              simp [Tmem.Pair.isTmemOp, hki, tcnt, Code.enter, Mma.Start.exit]
            | alloc =>
              have hki := hk3.2.1 rfl
              simp only [Option.map_some, Option.some.injEq] at h1
              subst h1
              by_cases hl : laneOf L g = 0
              · simp [hl, Tmem.Pair.isTmemOp, hki, tcnt, Code.enter, Mma.Start.exit]
              · simp [hl, Tmem.Pair.isTmemOp, hki, tcnt, Code.enter, Mma.Start.exit]; rfl
            | wr =>
              obtain ⟨col, hki⟩ := hk3.2.2 rfl
              simp only [Option.map_some, Option.some.injEq] at h1
              subst h1
              simp [Tmem.Pair.isTmemOp, hki, tcnt, Code.enter, Mma.Start.exit]
              rfl
            | enter => exact absurd hinv.2 (by simp [Mma.Start.exit])
          · have hev := (Mma.mfired hp hX he hσ0).1
            simp only [glued, Code.glue, frag, Mma.M, Mma.G] at h1
            cases hs : Mma.succ p L g d e with
            | none => simp [Mma.code, hs] at h1
            | some o' =>
              cases o' with
              | none => simp [Mma.code, hs] at h1
              | some d' =>
                simp only [Mma.code, hs, Option.map_some, Option.some.injEq] at h1
                subst h1
                show Mma.tsite d.site + _ = Mma.tsite d'.site
                rw [Mma.succ_tsite hs]
                congr 1
                cases hrd : Mma.isRD d.site
                · cases hop : Tmem.Pair.isTmemOp e
                  · rfl
                  · exfalso
                    obtain ⟨grp, dst, act, hk'⟩ := isTmemOp_eq hop
                    have := Mma.ev_res hev hk'
                    rw [hrd] at this; cases this
                · obtain ⟨site, v⟩ := d
                  obtain ⟨pc, kind⟩ := e
                  cases site <;> simp only [Mma.isRD, reduceCtorEq] at hrd <;>
                    simp only [Mma.Ev] at hev <;>
                    rcases hev with ⟨dst, act, hk'⟩ | ⟨f, hk'⟩ <;>
                    first
                      | ((try simp only at hk'); subst hk'; rfl)
                      | exact absurd hk' (hub f)
        | _ =>
          exfalso
          simp [Mma.Ref] at hJ

/-- **A lane of the MMA warp has made `tcnt` resource operations before each event.** -/
theorem mma_count (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (h12 : Prologue.warpIndex L g = 12) :
    ∀ k, k < (X.tr g).length → ∀ σ, Frame.stateAt (thread p L) X g k = some (some σ) →
      Tmem.Pair.tmemOps ((X.tr g).take k) = tcnt p L g σ := by
  intro k hk
  refine mma_count_at hp hX hg h12 k hk.le fun j hj e f he hf => ?_
  obtain ⟨e1, he1⟩ : ∃ e, X.get (g, k) = some e := ⟨_, List.getElem?_eq_getElem hk⟩
  have := ub_last hX (show X.get (g, j) = some ⟨e.pc, .ub f⟩ by rw [he, ← hf]) he1
  omega

end
end PTX.Kernels.TmlFa4Fwd.Proof
