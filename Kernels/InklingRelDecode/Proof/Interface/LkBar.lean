-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.LkMachine
public import Kernels.InklingRelDecode.Proof.Interface.LkCount
public import Kernels.InklingRelDecode.Proof.Interface.BarStatic
public import Lemmas.Flow.OpPcsFast

@[expose] public section

/-!
# Warp lockstep: the barrier events

A state is a barrier state when its instruction is `bar.sync` or `barrier.sync` (`barSt`): the
event fired from it is a barrier event, with the id and thread count its instruction has, and
every barrier event is fired from a barrier state (`isBar_state`). The barrier states are
synchronizing. So, from the lockstep of the synchronizing states, two lanes of a warp that have
made the same number of barrier events are at one barrier site (`bar_key`), and their events are
the same barrier with the same count (`bar_idcnt`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Lk (syOp syPcs syPc syAt kernel_syPcs)

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The state's instruction is a named barrier. -/
def barSt (s : TSt) : Bool :=
  match kernel.code[TSt.pc s]? with
  | some ins => barOp ins.op
  | none => false

/-- **A barrier state fires a barrier event; a state that is no barrier fires none.** -/
theorem isBar_state (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (hb : L.block ≠ 128) {g k : Nat}
    {e : Event} {s : TSt} (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some s)) :
    Execution.isBar e = barSt s := by
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site hS hX he hσ
  have hc' : kernel.code[TSt.pc s]? = some ins := hc
  have hf' : Fires (TSt.pc s) (eventTmpl asms L g t ins.op) e o := hf
  have hall := List.all_eq_true.mp kernel_barForm ins (List.mem_of_getElem? hc')
  simp only [barSt, hc']
  cases hq : barOp ins.op
  · cases hbar : Execution.isBar e
    · rfl
    · exfalso
      obtain ⟨pc, kd⟩ := e
      cases kd <;> simp only [Execution.isBar, Bool.false_eq_true] at hbar
      rename_i id c m
      have := fires_bar_op hf' (show (⟨pc, .bar id c m⟩ : Event).kind = .bar id c m from rfl)
      rw [hq] at this
      cases this
  · cases hins : ins.op with
    | barSync b al =>
      rw [hins] at hf' hall
      cases b with
      | imm v =>
        simp only [barForm, decide_eq_true_eq] at hall
        obtain ⟨n, rfl⟩ : ∃ n : Nat, v = n := ⟨v.toNat, (Int.toNat_of_nonneg hall.1).symm⟩
        have := EvD.fires_barSync_imm (by omega) hf'
        rw [this]
        rfl
      | _ => simp [barForm] at hall
    | barSyncN b c al =>
      rw [hins] at hf' hall
      cases b with
      | imm v =>
        cases c with
        | imm w =>
          by_cases h0 : v = 0
          · by_cases h1 : w = 128
            · subst h0 h1
              have := EvD.fires_barSyncN_128 hb hf'
              rw [this]
              rfl
            · simp [barForm, h0, h1] at hall
          · simp [barForm, h0] at hall
        | _ => simp [barForm] at hall
      | _ => simp [barForm] at hall
    | barArrive b c al =>
      rw [hins] at hall
      simp [barForm] at hall
    | _ => rw [hins] at hq; simp [barOp] at hq

/-- The instruction at a position satisfies `f`. -/
def opPc (f : Op → Bool) (pc : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ins => f ins.op
  | none => false

theorem syPc_of_op {f : Op → Bool} (hf : ∀ op, f op = true → syOp op = true) {pc : Nat}
    (h : opPc f pc = true) : syPc pc = true := by
  unfold opPc at h
  cases hc : kernel.code[pc]? with
  | none => rw [hc] at h; simp at h
  | some ins =>
    rw [hc] at h
    exact List.contains_iff_mem.mpr (OpPcsFast.mem kernel_syPcs hc (hf _ h))

/-- The positions of a class of synchronizing instructions are no second step of a two-step
instruction (checked per class by `decide`). -/
structure OpSub (f : Op → Bool) : Prop where
  ds : ∀ s : DStart.Site, opPc f s.pc = true → s.sub = 0 ∧ s ≠ DStart.Site.toProA
  pro : ∀ n < 182, opPc f (ProA.Site.ofNat n).pc = true → (ProA.Site.ofNat n).sub = 0
  ld : ∀ s : Loader.Site, opPc f s.pc = true → (match s with | .ld1 => 1 | _ => 0) = 0

/-- **A state of a class of synchronizing instructions is synchronizing.** -/
theorem opPc_sy {f : Op → Bool} (hf : ∀ op, f op = true → syOp op = true) (ha : OpSub f)
    {s : TSt} (hp : opPc f (TSt.pc s) = true) : tSy s := by
  have hsy := syPc_of_op hf hp
  cases s with
  | d s =>
    cases s with
    | dstart d =>
      obtain ⟨h1, h2⟩ := ha.ds d.site hp
      simp only [tSy, PTX.Kernels.InklingRelDecode.Proof.Lk.dSy, Bool.and_eq_true,
        decide_eq_true_eq, PTX.Kernels.InklingRelDecode.Proof.Lk.dsSy, syAt]
      exact ⟨⟨hsy, by omega⟩, h2⟩
    | pro d =>
      have := ha.pro d.site.ctorIdx (PTX.Kernels.InklingRelDecode.Proof.Lk.ctorIdx_lt _)
        (by rw [PTX.Kernels.InklingRelDecode.Proof.Lk.ofNat_ctorIdx]; exact hp)
      rw [PTX.Kernels.InklingRelDecode.Proof.Lk.ofNat_ctorIdx] at this
      simp only [tSy, PTX.Kernels.InklingRelDecode.Proof.Lk.dSy,
        PTX.Kernels.InklingRelDecode.Proof.Lk.proSy, syAt, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hsy, this⟩
    | sm d =>
      simp only [tSy, PTX.Kernels.InklingRelDecode.Proof.Lk.dSy,
        PTX.Kernels.InklingRelDecode.Proof.Lk.smSy, syAt, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hsy, trivial⟩
    | epi d =>
      simp only [tSy, PTX.Kernels.InklingRelDecode.Proof.Lk.dSy,
        PTX.Kernels.InklingRelDecode.Proof.Lk.epSy, syAt, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hsy, trivial⟩
  | w s =>
    simp only [tSy, PTX.Kernels.InklingRelDecode.Proof.Lk.wSy, syAt, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq]
    left
    refine ⟨hsy, ?_⟩
    cases s with
    | loader d P =>
      have := ha.ld d.site hp
      simp only [WComp.sub, Loader.sub]
      cases hs : d.site <;> simp_all
    | _ => rfl

/-- **Two synchronizing states of one key are both in a class of positions or both out.** -/
theorem opKey_class (f : Op → Bool) :
    ∀ {g h : Nat} {s s' : TSt}, SameWarp L g h → (kernelSkel Q L).sy s → (kernelSkel Q L).sy s' →
      (kernelSkel Q L).key g s = (kernelSkel Q L).key h s' →
      opPc f (TSt.pc s) = opPc f (TSt.pc s') := by
  intro g h s s' _ hs hs' hk
  have h1 := (kernelSkel Q L).pc_key (g := g) hs
  have h2 := (kernelSkel Q L).pc_key (g := h) hs'
  rw [← h1, ← h2, hk]

theorem barSub : OpSub barOp :=
  ⟨fun s => by cases s <;> decide +kernel, by decide +kernel,
    fun s => by cases s <;> decide +kernel⟩

/-- **A barrier state is synchronizing.** -/
theorem barSt_sy {s : TSt} (h : barSt s = true) : tSy s :=
  opPc_sy (f := barOp) (fun op h => by cases op <;> simp_all [barOp, syOp]) barSub h

/-- The barrier id and thread count of a barrier instruction. -/
def barIdCnt (ins : Instr) : Nat × Option Nat :=
  match ins.op with
  | .barSync (.imm v) _ => (v.toNat, none)
  | .barSyncN (.imm 0) (.imm 128) _ => (0, some 128)
  | _ => (0, none)

/-- **A barrier event has the id and thread count of its instruction.** -/
theorem bar_event_idcnt (hX : Consistent L kernel asms mem0 X) (hb : L.block ≠ 128)
    {i : EvId} {pc id : Nat} {cnt : Option Nat} {m : BarMode}
    (he : X.get i = some ⟨pc, .bar id cnt m⟩) :
    ∃ ins, kernel.code[pc]? = some ins ∧ (id, cnt) = barIdCnt ins := by
  rcases Flow.get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, -, hc, hf⟩
  · cases hf
  · simp only at hc hf
    refine ⟨ins, hc, ?_⟩
    have hop := fires_bar_op hf (show (⟨pc, .bar id cnt m⟩ : Event).kind = .bar id cnt m from rfl)
    have hall := List.all_eq_true.mp kernel_barForm ins (List.mem_of_getElem? hc)
    cases hins : ins.op with
    | barSync b al =>
      rw [hins] at hf hall
      cases b with
      | imm v =>
        simp only [barForm, decide_eq_true_eq] at hall
        obtain ⟨n, rfl⟩ : ∃ n : Nat, v = n := ⟨v.toNat, (Int.toNat_of_nonneg hall.1).symm⟩
        have := EvD.fires_barSync_imm (by omega) hf
        simp only [Event.mk.injEq, Kind.bar.injEq, true_and] at this
        obtain ⟨rfl, rfl, rfl⟩ := this
        simp [barIdCnt, hins]
      | _ => simp [barForm] at hall
    | barSyncN b c al =>
      rw [hins] at hf hall
      cases b with
      | imm v =>
        cases c with
        | imm w =>
          by_cases h0 : v = 0
          · by_cases h1 : w = 128
            · subst h0 h1
              have := EvD.fires_barSyncN_128 hb hf
              simp only [Event.mk.injEq, Kind.bar.injEq, true_and] at this
              obtain ⟨rfl, rfl, rfl⟩ := this
              simp [barIdCnt, hins]
            · simp [barForm, h0, h1] at hall
          · simp [barForm, h0] at hall
        | _ => simp [barForm] at hall
      | _ => simp [barForm] at hall
    | barArrive b c al =>
      rw [hins] at hall
      simp [barForm] at hall
    | _ => rw [hins] at hop; simp [barOp] at hop

theorem barKey_class :
    ∀ {g h : Nat} {s s' : TSt}, SameWarp L g h → (kernelSkel Q L).sy s → (kernelSkel Q L).sy s' →
      (kernelSkel Q L).key g s = (kernelSkel Q L).key h s' → barSt s = barSt s' :=
  opKey_class barOp

/-- **Two lanes of a warp that have made the same number of barrier events make their next
barrier event at one position, with one barrier id and one thread count**, given the lockstep of
the synchronizing states. -/
theorem bar_agree (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    (hL : ∀ n, Lock (kernelSkel Q L) X n) {g h i j pc pc' id id' : Nat} {count count' : Option Nat}
    {m m' : BarMode} (hw : SameWarp L g h) (hi : X.get (g, i) = some ⟨pc, .bar id count m⟩)
    (hj : X.get (h, j) = some ⟨pc', .bar id' count' m'⟩)
    (hcnt : ((X.tr g).take i).countP Execution.isBar = ((X.tr h).take j).countP Execution.isBar) :
    pc = pc' ∧ id = id' ∧ count = count' := by
  have hb : L.block ≠ 128 := by have := hpre.block; omega
  have hg : g < L.threads := hw.1.1
  have hh : h < L.threads := hw.1.2.1
  obtain ⟨s, hs⟩ := Frame.event_state hS hX ht hi (fun pc f h => by cases h)
  obtain ⟨s', hs'⟩ := Frame.event_state hS hX ht hj (fun pc f h => by cases h)
  have hs1 : St Q L X g i = some (some s) := hs
  have hs2 : St Q L X h j = some (some s') := hs'
  have hev : ClassEv Execution.isBar barSt Q L X := fun hg he hσ => isBar_state hX hS hb he hσ
  have hbs : barSt s = true := by
    rw [← isBar_state hX hS hb hi hs1]; rfl
  have hbs' : barSt s' = true := by
    rw [← isBar_state hX hS hb hj hs2]; rfl
  have hik : i ≤ (X.tr g).length := by
    have := (List.getElem?_eq_some_iff.mp hi).1
    simp only at this
    omega
  have hjk : j ≤ (X.tr h).length := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simp only at this
    omega
  have hkey := class_key (kernelSkel Q L) ht hL hev (fun hs => barSt_sy hs) barKey_class hw
    hik hjk hs1 hs2 hbs hbs' hcnt
  have h1 := (kernelSkel Q L).pc_key (g := g) (barSt_sy hbs)
  have h2 := (kernelSkel Q L).pc_key (g := h) (barSt_sy hbs')
  have hpc : TSt.pc s = TSt.pc s' := by rw [← h1, ← h2, hkey]
  have e1 := Frame.event_pc hS hX hi hs
  have e2 := Frame.event_pc hS hX hj hs'
  have hpc' : pc = pc' := by
    simp only at e1 e2
    rw [e1, e2]
    exact hpc
  refine ⟨hpc', ?_⟩
  subst hpc'
  obtain ⟨ins, hc1, hic1⟩ := bar_event_idcnt hX hb hi
  obtain ⟨ins', hc2, hic2⟩ := bar_event_idcnt hX hb hj
  rw [hc1] at hc2
  obtain rfl := Option.some.inj hc2
  have := hic1.trans hic2.symm
  simp only [Prod.mk.injEq] at this
  exact this

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
