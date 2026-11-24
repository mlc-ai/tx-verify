-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.KvPre
public import Kernels.InklingRelDecode.Proof2.Lib.Elect

@[expose] public section

/-! # The lanes the elections elect: the ring's copying and committing threads

The loader's copies and the MMA warp's commits are guarded by an `elect.sync`: a lane reaches a
copy site of the loader, or the PV half's MMAs and commit, only after an election that returned
its own lane (`ld_cp_elected`, `mm_pv_elected`). Every election of the kernel has the full mask,
so such a lane led every election of its trace (`electLead_of_elected`), and one lane of a warp
does (`electLead_unique`). `leadT L X c w` is that lane of warp `w` of CTA `c` (`leadT_eq`): the
ring's copying thread is `leadT … 6` and its committing thread `leadT … 7`. -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame
open PTX.Kernels.InklingRelDecode.Proof.Interface (electLead_of_elected electMask_full)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-! ### The elected lane of a warp -/

open Classical in
/-- The thread of warp `w` of CTA `c` that led its elections, if one elected. -/
def leadT (L : Launch) (X : Execution) (c w : Nat) : Nat :=
  if h : ∃ h', h' < L.threads ∧ h' / L.block = c ∧ h' % L.block / 32 = w ∧
      ElectLead L h' (X.tr h') ∧ ∃ ld, Elected (X.tr h') ld then Classical.choose h
  else c * L.block + 32 * w

/-- **The lane an election returned is the warp's elected lane.** -/
theorem leadT_eq (hX : Consistent L kernel Assumptions.all m X) {h : Nat} (hh : h < L.threads)
    (hel : Elected (X.tr h) (laneOf L h)) :
    leadT L X (h / L.block) (h % L.block / 32) = h := by
  have hl := electLead_of_elected hX hel
  have hex : ∃ h', h' < L.threads ∧ h' / L.block = h / L.block ∧
      h' % L.block / 32 = h % L.block / 32 ∧ ElectLead L h' (X.tr h') ∧
      ∃ ld, Elected (X.tr h') ld := ⟨h, hh, rfl, rfl, hl, _, hel⟩
  unfold leadT
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨h1, h2, h3, hl', ld', he'⟩ := Classical.choose_spec hex
  exact electLead_unique hX.elect ⟨⟨h1, hh, h2⟩, h3⟩ (electMask_full hX _) (electMask_full hX h)
    he' hel hl' hl

theorem elected_of_get {k pc mask inst : Nat}
    (he : (X.tr g)[k]? = some ⟨pc, .elect mask inst (laneOf L g)⟩) :
    Elected (X.tr g) (laneOf L g) :=
  ⟨_, List.mem_of_getElem? he, mask, inst, rfl⟩

/-! ### The loader's copies -/

/-- The loader's copy sites. -/
def isCpS : Proof.Loader.Site → Bool
  | .cp0a | .cp0b | .cp1a | .cp1b | .cp2a | .cp2b | .cp3a | .cp3b => true
  | _ => false

/-- The step into a copy site is an election that returned the thread's lane, or a step from a
copy site. -/
theorem ld_next_into_cp {d0 d : Proof.Loader.D} {e : Event}
    (hn : Proof.Loader.next L g d0 e = some (some d)) (hs : isCpS d.site = true) :
    (∃ mask inst, e.kind = .elect mask inst (laneOf L g)) ∨ isCpS d0.site = true := by
  obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d0
  cases s <;> simp only [Proof.Loader.next, Proof.Loader.readI, Proof.Loader.readN] at hn
  all_goals (repeat' split at hn)
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (cases hn; done)
    | (simp only [Option.some.injEq] at hn
       subst hn
       first
         | (right; rfl)
         | (simp [isCpS] at hs; done)
         | (left; exact ⟨_, _, by subst_vars; assumption⟩)
         | (simp only [Proof.Loader.afterIter] at hs; split at hs <;> simp [isCpS] at hs))

/-- The loader's copy states. -/
def LdCp (Q : Params) (L : Launch) (g : Nat) : (thread Q L g).D → Prop
  | (.inr ⟨.inl (.worker _), .loader d _⟩, _) => isCpS d.site = true
  | _ => False

/-- **A loader thread at a copy site has an election that returned its lane.** -/
theorem ld_cp_elected (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) :
    ∀ k, k ≤ (X.tr g).length → ∀ σ, Frame.stateAt (thread Q L) X g k = some (some σ) →
      LdCp Q L g σ → Elected (X.tr g) (laneOf L g) := by
  intro k
  induction k with
  | zero =>
    intro _ σ hσ hc
    rw [Frame.stateAt_zero, thread_init_eq] at hσ
    obtain rfl := Option.some.inj (Option.some.inj hσ)
    exact hc.elim
  | succ k ih =>
    intro hk σ' hσ' hc
    have hlt : k < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    rw [Frame.stateAt_succ he] at hσ'
    rcases hk0 : Frame.stateAt (thread Q L) X g k with _ | _ | σ
    · rw [hk0] at hσ'; cases hσ'
    · rw [hk0] at hσ'; cases hσ'
    · rw [hk0] at hσ'
      have hn : (thread Q L g).next σ e = some (some σ') := hσ'
      obtain ⟨x, n⟩ := σ
      rcases x with s | ⟨_ | r, d⟩
      · exfalso
        rw [next_start] at hn
        obtain ⟨s', -, rfl⟩ := mm_some hn
        revert hc
        simp only [Code.enter]
        split
        · rename_i j _
          rcases j with (_ | _) | _
          · exact id
          · exact id
          · exact id
        · exact id
      · rename_i i
        obtain ⟨d', hd'⟩ := next_same_role hn
        obtain ⟨x', n'⟩ := σ'
        simp only at hd'
        subst hd'
        cases i with
        | dp tm bw => exact hc.elim
        | worker w =>
          rw [next_worker] at hn
          obtain ⟨σw', hσw, he'⟩ := mm_some hn
          simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq, true_and] at he'
          obtain ⟨he1, -⟩ := he'
          subst he1
          cases σw' with
          | loader d' P' =>
            have hcs : isCpS d'.site = true := hc
            rcases w_next_loader hσw with hst | ⟨dl, rfl, -, hld⟩
            · rw [hst] at hcs; cases hcs
            · rcases ld_next_into_cp hld hcs with ⟨mask, inst, hk'⟩ | hcp
              · obtain ⟨pc, kd⟩ := e
                simp only at hk'
                subst hk'
                exact elected_of_get he
              · exact ih hlt.le _ hk0 hcp
          | _ => exact hc.elim
      · exact ((good_all' hp hX hg k).2 _ hk0).elim

/-! ### The MMA warp's PV half -/

/-- The MMA and first commit sites of both halves (each after the half's election). -/
def isPvS : Proof.Mma.Site → Bool
  | .qk _ | .qkCommit | .pv _ | .pvCommit1 => true
  | _ => false

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- The step into a PV MMA or the PV half's first commit is an election that returned the
thread's lane, or a step from such a site. -/
theorem mm_next_into_pv {d0 d : Proof.Mma.D} {e : Event}
    (hn : Proof.Mma.next L g d0 e = some (some d)) (hs : isPvS d.site = true) :
    (∃ mask inst, e.kind = .elect mask inst (laneOf L g)) ∨ isPvS d0.site = true := by
  obtain ⟨s, i, n, tm, pro⟩ := d0
  cases s <;> simp only [Proof.Mma.next, Proof.Mma.start, Proof.Mma.afterQk,
    Proof.Mma.iterNext, Proof.Mma.qkNext, Proof.Mma.pvNext] at hn
  all_goals (repeat' split at hn)
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (cases hn; done)
    | (simp only [Option.some.injEq] at hn
       subst hn
       first
         | (right; rfl)
         | (simp [isPvS] at hs; done)
         | (left; exact ⟨_, _, by subst_vars; assumption⟩)
         | (simp only at hs; split at hs <;> simp [isPvS] at hs))

/-- A worker step into an MMA state is the dispatch's entry or a step of the MMA machine. -/
theorem w_next_mma' {s : Proof.WComp.WSt} {e : Event} {d' : Proof.Mma.D}
    {P' : Proof.Loader.Pro} (h : Proof.WComp.next L g s e = some (some (.mma d' P'))) :
    d'.site = .setMaxReg ∨ ∃ d, s = .mma d P' ∧ Proof.Mma.next L g d e = some (some d') := by
  cases s with
  | worker w => exact .inl (w_next_mma h)
  | idle d =>
    by_cases hs : d.site = .inc
    · obtain ⟨s, P⟩ := d
      simp only at hs
      subst hs
      cases h
    · rw [Proof.EvW.next_idle_map hs] at h
      obtain ⟨a, -, ha⟩ := Proof.EvW.map_map_some h
      cases ha
  | loader d P =>
    by_cases hs : d.site = .setMaxInc
    · obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
      simp only at hs
      subst hs
      cases h
    · rw [Proof.EvW.next_loader_map P hs] at h
      obtain ⟨a, -, ha⟩ := Proof.EvW.map_map_some h
      cases ha
  | mma d P =>
    by_cases hs : d.site = .setMaxRegInc
    · obtain ⟨s, i, n, tm, pro⟩ := d
      simp only at hs
      subst hs
      cases h
    · rw [Proof.EvW.next_mma_map P hs] at h
      obtain ⟨a, ha, he⟩ := Proof.EvW.map_map_some h
      simp only [Proof.WComp.WSt.mma.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact .inr ⟨d, rfl, ha⟩
  | exit x =>
    obtain ⟨s, P⟩ := x
    cases s <;> cases h

/-- The MMA warp's PV states. -/
def MmPv (Q : Params) (L : Launch) (g : Nat) : (thread Q L g).D → Prop
  | (.inr ⟨.inl (.worker _), .mma d _⟩, _) => isPvS d.site = true
  | _ => False

/-- **An MMA-warp thread at a PV MMA or the PV half's first commit has an election that returned
its lane.** -/
theorem mm_pv_elected (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) :
    ∀ k, k ≤ (X.tr g).length → ∀ σ, Frame.stateAt (thread Q L) X g k = some (some σ) →
      MmPv Q L g σ → Elected (X.tr g) (laneOf L g) := by
  intro k
  induction k with
  | zero =>
    intro _ σ hσ hc
    rw [Frame.stateAt_zero, thread_init_eq] at hσ
    obtain rfl := Option.some.inj (Option.some.inj hσ)
    exact hc.elim
  | succ k ih =>
    intro hk σ' hσ' hc
    have hlt : k < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    rw [Frame.stateAt_succ he] at hσ'
    rcases hk0 : Frame.stateAt (thread Q L) X g k with _ | _ | σ
    · rw [hk0] at hσ'; cases hσ'
    · rw [hk0] at hσ'; cases hσ'
    · rw [hk0] at hσ'
      have hn : (thread Q L g).next σ e = some (some σ') := hσ'
      obtain ⟨x, n⟩ := σ
      rcases x with s | ⟨_ | r, d⟩
      · exfalso
        rw [next_start] at hn
        obtain ⟨s', -, rfl⟩ := mm_some hn
        revert hc
        simp only [Code.enter]
        split
        · rename_i j _
          rcases j with (_ | _) | _
          · exact id
          · exact id
          · exact id
        · exact id
      · rename_i i
        obtain ⟨d', hd'⟩ := next_same_role hn
        obtain ⟨x', n'⟩ := σ'
        simp only at hd'
        subst hd'
        cases i with
        | dp tm bw => exact hc.elim
        | worker w =>
          rw [next_worker] at hn
          obtain ⟨σw', hσw, he'⟩ := mm_some hn
          simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq, true_and] at he'
          obtain ⟨he1, -⟩ := he'
          subst he1
          cases σw' with
          | mma d' P' =>
            have hcs : isPvS d'.site = true := hc
            rcases w_next_mma' hσw with hst | ⟨dm, rfl, hmn⟩
            · rw [hst] at hcs; cases hcs
            · rcases mm_next_into_pv hmn hcs with ⟨mask, inst, hk'⟩ | hcp
              · obtain ⟨pc, kd⟩ := e
                simp only at hk'
                subst hk'
                exact elected_of_get he
              · exact ih hlt.le _ hk0 hcp
          | _ => exact hc.elim
      · exact ((good_all' hp hX hg k).2 _ hk0).elim

/-! ### The prologue's copies -/

theorem ptcSite_mem (b : Fin 3) (j : Fin 4) :
    Proof.ProA.ptcSite (4 * b.val + j.val) ∈ Proof.ProA.ptcSites := by
  fin_cases b <;> fin_cases j <;> decide

/-- The prologue's copy states. -/
def ProCp (Q : Params) (L : Launch) (g : Nat) : (thread Q L g).D → Prop
  | (.inr ⟨.inl (.dp _ _), .inl d⟩, _) => ∃ b j, d.site = .ptc b j
  | _ => False

/-- **A prologue thread at a copy site has an election that returned its lane**, and the copies'
predicate `v_p59` held (warps 0 and 1). -/
theorem pro_ptc_elected (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) {k : Nat} (hk : k ≤ (X.tr g).length) {σ : (thread Q L g).D}
    (hσ : Frame.stateAt (thread Q L) X g k = some (some σ)) (hc : ProCp Q L g σ) :
    Elected (X.tr g) (laneOf L g) ∧ g % L.block < 64 := by
  cases k with
  | zero =>
    rw [Frame.stateAt_zero, thread_init_eq] at hσ
    obtain rfl := Option.some.inj (Option.some.inj hσ)
    exact hc.elim
  | succ k =>
    have hlt : k < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    rw [Frame.stateAt_succ he] at hσ
    rcases hk0 : Frame.stateAt (thread Q L) X g k with _ | _ | σ0
    · rw [hk0] at hσ; cases hσ
    · rw [hk0] at hσ; cases hσ
    · rw [hk0] at hσ
      have hn : (thread Q L g).next σ0 e = some (some σ) := hσ
      have hJ := (good_all' hp hX hg k).2 _ hk0
      obtain ⟨x, n⟩ := σ0
      rcases x with s | ⟨_ | r, d⟩
      · exfalso
        obtain ⟨x', n'⟩ := σ
        rcases x' with _ | ⟨_ | r, d⟩
        · exact hc
        · rename_i i
          cases i with
          | worker w => exact hc
          | dp tm bw =>
            rcases d with d | _
            · obtain ⟨b, j, hs⟩ := hc
              rw [next_start] at hn
              obtain ⟨s', -, hs'⟩ := mm_some hn
              cases hx : Startup.enterOf s' with
              | none =>
                rw [enter_inl hx] at hs'
                simp at hs'
              | some r =>
                cases hsel : sel L g r s' with
                | none =>
                  rw [Code.enter_some (i := Sum.inr r) (by simp [Code.gatedExit, hx, hsel])] at hs'
                  simp at hs'
                | some ro =>
                  rw [Code.enter_some (i := Sum.inl ro) (by simp [Code.gatedExit, hx, hsel])] at hs'
                  cases ro with
                  | worker w => simp at hs'
                  | dp tm1 bw1 =>
                    have h1 := congrArg (thread Q L g).pc hs'
                    change 27 = d.site.pc at h1
                    rw [hs] at h1
                    clear hs; revert h1; revert b j; decide
            · exact hc
        · exact hc
      · rename_i i
        obtain ⟨d', hd'⟩ := next_same_role hn
        obtain ⟨x', n'⟩ := σ
        simp only at hd'
        subst hd'
        cases i with
        | worker w => exact hc.elim
        | dp tm bw =>
          rcases d with d | ⟨_ | _, τ⟩
          · rw [next_pro] at hn
            obtain ⟨d'', hd'', he''⟩ := mm_some hn
            have hx : ProA.exitOf d'' = none := by
              cases hxo : ProA.exitOf d'' with
              | none => rfl
              | some v =>
                exfalso
                cases hsel : ProA.selTail Q L g v d'' with
                | some dt' =>
                  rw [Code.enter_some (i := Sum.inl dt')
                    (by simp [Code.gatedExit, hxo, hsel])] at he''
                  simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq,
                    true_and] at he''
                  obtain ⟨rfl, -⟩ := he''
                  exact hc.elim
                | none =>
                  rw [Code.enter_some (i := Sum.inr ())
                    (by simp [Code.gatedExit, hxo, hsel])] at he''
                  simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq,
                    true_and] at he''
                  obtain ⟨rfl, -⟩ := he''
                  exact hc.elim
            rw [Code.enter_none (by simp [Code.gatedExit, hx])] at he''
            simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq, true_and] at he''
            obtain ⟨rfl, -⟩ := he''
            obtain ⟨b, j, hs⟩ := hc
            obtain ⟨s0, dt⟩ := d
            have hk' : ProA.kill ⟨s0, dt⟩ e = false := by
              cases hq : ProA.kill ⟨s0, dt⟩ e
              · rfl
              · simp [ProA.next, hq] at hd''
            have h' : ProA.next0 L g ⟨s0, dt⟩ e = some (some d'') := by
              simpa [ProA.next, hk'] using hd''
            have h1 : s0 ≠ .bar18 := by
              intro h; subst h
              simp [ProA.next0] at h'
              rw [← h'] at hs; cases hs
            have h2 : s0 ≠ .exit := by intro h; subst h; simp [ProA.next0] at h'
            have h3 : s0 ≠ .ld 2 := by
              intro h; subst h
              rw [ld2_succ h'] at hs; cases hs
            have hf := ProA.next0_flat h1 h2 h3 h'
            have hf' : Proof.ProA.next L g ⟨s0.old, dt⟩ e = some (some (ProA.D.old d'')) := hf
            have hmem : (ProA.D.old d'').site ∈ Proof.ProA.ptcSites := by
              show d''.site.old ∈ _
              rw [hs, ptc_old]; exact ptcSite_mem b j
            obtain ⟨⟨mask, inst, hk2⟩, hp59⟩ := Proof.ProA.next_into_ptc hf' hmem
            refine ⟨?_, ?_⟩
            · obtain ⟨pc, kd⟩ := e
              simp only at hk2
              subst hk2
              exact elected_of_get he
            · obtain ⟨t, ins, o, hat, hi, -, -⟩ :=
                Frame.fired_site (fun g hg => thread_sound hp hg) hX he hk0
              exact Proof.ProA.tid_of_p59 (hi.1.args.tid) hp59
          · exfalso
            rw [next_tail] at hn
            obtain ⟨τ', -, he''⟩ := mm_some hn
            simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq, true_and] at he''
            obtain ⟨rfl, -⟩ := he''
            exact hc.elim
          · exact hJ.elim
      · exact hJ.elim

end
end PTX.Kernels.InklingRelDecode.Proof2
