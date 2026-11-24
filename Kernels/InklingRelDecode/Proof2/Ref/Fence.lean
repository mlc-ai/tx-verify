-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Ref.Stage1
public import Kernels.InklingRelDecode.Proof2.Ref.Codes
public import Kernels.InklingRelDecode.Proof2.Ref.Bar0
public import Kernels.InklingRelDecode.Proof2.Lib.CopyCta
public import Lemmas.Flow.OpPcsFast
public import Lemmas.Flow.NotTensor
public import Lemmas.Order.OrderWaits
public import Lemmas.Kernel.Safety.Handoff

@[expose] public section

/-! # Every tensor copy's issue comes after a proxy fence of its CTA, before the base word is known

From the first stage of the following (`Ref/Stage1.lean`) alone:

* `entry`: a thread is followed with `Ref1` up to its first state that owes nothing (`S1`), and at
  that state `Ref1` holds;
* `bar1_exit`: a thread that exits has made a barrier-1 event (the epilogue and the workers' exit
  path come after one);
* `thread0_fence`: when a thread of a CTA has passed its first barrier-1 event, the CTA's thread 0
  made a proxy fence before its own first barrier-1 event (the prologue's fence at pc 179, before
  its last barrier at pc 573);
* `issue_fence`: every tensor-copy issue is after a proxy fence of a thread of its CTA in base
  causality: the issuer's own fence for the default partition's copies (pc 179 comes before every
  copy instruction), thread 0's fence through barrier 1's first instance for the loader's
  (`Handoff.of_bar_upTo`).

This is the first tree's `ScFence`/`BaseWCopy`/`BaseWPhase` argument on the Proof2 machines. -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The barrier-1 count of a thread before position `k`. -/
abbrev c1 (X : Execution) (g k : Nat) : Nat := ((X.tr g).take k).countP (Execution.isBarId 1)

theorem cls_bar1 : cls (.bar 1) = Execution.isBarId 1 := by
  funext e
  obtain ⟨pc, k⟩ := e
  cases k <;> rfl

/-- An event of a class before position `k`. -/
theorem exists_of_count {P : Event → Bool} {k : Nat} (h : 1 ≤ ((X.tr g).take k).countP P) :
    ∃ j < k, ∃ e, X.get (g, j) = some e ∧ P e = true := by
  obtain ⟨e, hm, hp⟩ := List.countP_pos_iff.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one h)
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
  have hjk : j < k := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simp only [List.length_take] at this
    omega
  refine ⟨j, hjk, e, ?_, by simpa using hp⟩
  change (X.tr g)[j]? = some e
  rw [← hj, List.getElem?_take, ite_eq_left_iff.mpr (fun h => absurd hjk h)]

/-- No undefined behaviour before an event that is no undefined behaviour. -/
theorem ub0 (hX : Consistent L kernel Assumptions.all m X) {k j : Nat} {e : Event}
    (he : X.get (g, k) = some e) (hu : ∀ f, e.kind ≠ .ub f) (hj : j ≤ k) :
    ((X.tr g).take j).countP (cls .ub) = 0 := by
  apply List.countP_eq_zero.mpr
  intro x hx hc
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
  have hil : i < j := by
    have := (List.getElem?_eq_some_iff.mp hi).1
    simp only [List.length_take] at this
    omega
  have hget : X.get (g, i) = some x := by
    change (X.tr g)[i]? = some x
    rw [← hi, List.getElem?_take, ite_eq_left_iff.mpr (fun h => absurd hil h)]
  obtain ⟨pc, kd⟩ := x
  cases kd <;> simp [cls] at hc
  rename_i f
  rcases Nat.lt_or_ge i k with hlt | hge
  · have := ub_last hX hget he
    omega
  · have : i = k := by omega
    subst this
    rw [he] at hget
    cases hget
    exact hu f rfl

/-- The launched threads are the lanes the following covers. -/
theorem dpLane (hp : Pre Q L m) (hg : g < L.threads) : DpLane L g := by
  refine ⟨hg, ?_⟩
  rw [hp.block]
  have := Nat.mod_lt g (show 0 < 256 by decide)
  omega

/-- **Followed up to its first state of `S1`**: either every position up to `k` is before
`S1`, or there is a first position `i < k` at a state of `S1`, before which the thread was
followed. -/
theorem before_or_entry (k : Nat) :
    Frame.Before (thread Q L) (fun g => S1 Q L g) X g k ∨
      ∃ i < k, Frame.Before (thread Q L) (fun g => S1 Q L g) X g i ∧
        ∃ d, Frame.stateAt (thread Q L) X g i = some (some d) ∧ S1 Q L g d := by
  by_cases h : Frame.Before (thread Q L) (fun g => S1 Q L g) X g k
  · exact .inl h
  · right
    simp only [Frame.Before, not_forall, not_not] at h
    have hex : ∃ i, i < k ∧ ∃ d, Frame.stateAt (thread Q L) X g i = some (some d) ∧
        S1 Q L g d := by
      obtain ⟨i, hi, d, hd, hs⟩ := h
      exact ⟨i, hi, d, hd, hs⟩
    classical
    let i := Nat.find hex
    have hi := Nat.find_spec hex
    refine ⟨i, hi.1, ?_, hi.2⟩
    intro j hj d hd hs
    exact Nat.find_min hex hj ⟨by have := hi.1; omega, d, hd, hs⟩


/-! ### Code facts -/

/-- `ret` and `exit`. -/
def exitOp : Op → Bool
  | .ret | .exit => true
  | _ => false

theorem kernel_exit_pcs : OpPcsFast kernel.code exitOp [2855] = true := by decide +kernel

/-- The tensor copies of the code. -/
def copyPcs : List Nat :=
  [211, 217, 226, 231, 253, 259, 268, 273, 295, 301, 310, 315, 2389, 2391, 2394, 2396, 2404,
    2406, 2410, 2412]

theorem kernel_copy_pcs : OpPcsFast kernel.code tensorOp copyPcs = true := by decide +kernel

/-- A `barrier.sync 1`. -/
def bar1Op : Op → Bool
  | .barSync (.imm 1) _ => true
  | _ => false

def bar1Pcs : List Nat :=
  [573, 575, 2334, 2335, 2338, 2346, 2419, 2424, 2554, 2557, 2558, 2846, 2849]

theorem kernel_bar1_pcs : OpPcsFast kernel.code bar1Op bar1Pcs = true := by decide +kernel

/-- **An event on barrier 1 is at a `barrier.sync 1` of the code.** -/
theorem bar1_pc {t : TState} {ins : Instr} {pc : Nat} {e : Event} {o : Option TState}
    (hc : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o) {c : Option Nat} {md : BarMode}
    (hk : e.kind = .bar 1 c md) (hb : L.block ≠ 128) : pc ∈ bar1Pcs := by
  apply OpPcsFast.mem kernel_bar1_pcs hc
  have hall := List.all_eq_true.mp kernel_barForm ins (List.mem_of_getElem? hc)
  have hop := fires_bar_op hf hk
  cases hins : ins.op with
  | barSync b al =>
    rw [hins] at hf hall
    cases b with
    | imm v =>
      simp only [barForm, decide_eq_true_eq] at hall
      obtain ⟨n, rfl⟩ : ∃ n : Nat, v = n := ⟨v.toNat, (Int.toNat_of_nonneg hall.1).symm⟩
      have := Proof.EvD.fires_barSync_imm (by omega) hf
      rw [this] at hk
      simp only [Kind.bar.injEq] at hk
      obtain ⟨rfl, -⟩ := hk
      rfl
    | _ => simp [barForm] at hall
  | barSyncN b c' al =>
    rw [hins] at hf hall
    cases b with
    | imm v =>
      cases c' with
      | imm w =>
        by_cases h0 : v = 0
        · by_cases h1 : w = 128
          · subst h0 h1
            have := Proof.EvD.fires_barSyncN_128 hb hf
            rw [this] at hk
            simp at hk
          · simp [barForm, h0, h1] at hall
        · simp [barForm, h0] at hall
      | _ => simp [barForm] at hall
    | _ => simp [barForm] at hall
  | barArrive b c' al =>
    rw [hins] at hall
    simp [barForm] at hall
  | _ =>
    rw [hins] at hop
    simp [barOp] at hop

/-! ### Followed positions -/

/-- **A position before `S1` with an event that is no undefined behaviour is a followed state
with `Ref1`.** -/
theorem state1 (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {j : Nat}
    {e : Event} (he : X.get (g, j) = some e) (hu : ∀ f, e.kind ≠ .ub f)
    (hB : Frame.Before (thread Q L) (fun g => S1 Q L g) X g j) :
    ∃ d, Frame.stateAt (thread Q L) X g j = some (some d) ∧ Ref1 Q L g d := by
  have hg := Frame.lt_of_get hX he
  exact Frame.good_state (fun g hg => thread_sound hp hg) hX he
    (fun pc f h => hu f (by rw [h])) (good1 hp hX (dpLane hp hg) j hB)

/-- **The first state of `S1` holds `Ref1`.** -/
theorem entry1 (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads)
    {i : Nat} (hB : Frame.Before (thread Q L) (fun g => S1 Q L g) X g i) {d : (thread Q L g).D}
    (hd : Frame.stateAt (thread Q L) X g i = some (some d)) : Ref1 Q L g d :=
  (good1 hp hX (dpLane hp hg) i hB).2 d hd

/-- The pc of the state an event is fired from. -/
theorem fired_pc (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {j : Nat}
    {e : Event} {d : (thread Q L g).D} (he : X.get (g, j) = some e)
    (hd : Frame.stateAt (thread Q L) X g j = some (some d)) :
    ∃ t ins o, kernel.code[(thread Q L g).pc d]? = some ins ∧
      Fires ((thread Q L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o := by
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site (fun g hg => thread_sound hp hg) hX he hd
  exact ⟨t, ins, o, hc, hf⟩

theorem countP_mono_take {P : Event → Bool} {i j : Nat} (h : i ≤ j) :
    ((X.tr g).take i).countP P ≤ ((X.tr g).take j).countP P :=
  (List.take_sublist_take_left h).countP_le

/-! ### An exiting thread made a barrier-1 event -/

/-- **A thread that exits has made a barrier-1 event before its exit.** -/
theorem bar1_exit (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {j pc : Nat}
    (he : X.get (g, j) = some ⟨pc, .exit⟩) : 1 ≤ c1 X g j := by
  unfold c1
  have hg := Frame.lt_of_get hX he
  have hu : ∀ f, (⟨pc, .exit⟩ : Event).kind ≠ .ub f := by simp
  rcases before_or_entry (Q := Q) (X := X) (g := g) j with hB | ⟨i, hij, hB, d, hd, hS⟩
  · obtain ⟨d, hd, hR⟩ := state1 hp hX he hu hB
    obtain ⟨t, ins, o, hc, hf⟩ := fired_pc hp hX he hd
    have hpc : (thread Q L g).pc d = 2855 := by
      have h := fires_exit_op hf rfl
      exact List.mem_singleton.mp (OpPcsFast.mem kernel_exit_pcs hc (by
        rcases h with h | h <;> simp [exitOp, h]))
    obtain ⟨x, n⟩ := d
    have hcn : ∀ c, n c = ((X.tr g).take j).countP (cls c) := fun c => fcount hd c
    rcases x with s | ⟨_ | r, dd⟩
    · exfalso
      have := Startup.site_mem s.site
      change s.site.pc = 2855 at hpc
      rw [hpc] at this
      simp [startupSites] at this
    · rename_i i'
      cases i' with
      | dp tm bw =>
        rcases dd with dd | ⟨_ | _, τ⟩
        · exfalso
          have := ProA.site_mem dd.site
          change dd.site.pc = 2855 at hpc
          rw [hpc] at this
          simp [proASites] at this
        all_goals
          have h0 : n .ub = 0 := by rw [hcn .ub]; exact ub0 hX he hu le_rfl
          rcases hR.2 with h1 | h1
          · rw [hcn, cls_bar1] at h1; exact h1
          · omega
      | worker tm =>
        obtain ⟨-, -, hE, -⟩ := hR
        have h0 : n .ub = 0 := by rw [hcn .ub]; exact ub0 hX he hu le_rfl
        rcases hE with hE | h1 | h1
        · exfalso
          cases dd with
          | worker w =>
            obtain ⟨site, P⟩ := w
            simp only [WEarly] at hE
            rcases hE with rfl | rfl
            · exact absurd hpc (show (Proof.Worker.Site.loop).pc ≠ 2855 by decide)
            · exact absurd hpc (show (Proof.Worker.Site.bar2).pc ≠ 2855 by decide)
          | _ => exact hE.elim
        · rw [hcn, cls_bar1] at h1; exact h1
        · omega
    · exact hR.elim
  · have hR := entry1 hp hX hg hB hd
    obtain ⟨x, n⟩ := d
    have hcn : ∀ c, n c = ((X.tr g).take i).countP (cls c) := fun c => fcount hd c
    have h0 : n .ub = 0 := by rw [hcn .ub]; exact ub0 hX he hu hij.le
    have hmono := countP_mono_take (X := X) (g := g) (P := Execution.isBarId 1) hij.le
    rcases x with s | ⟨_ | r, dd⟩
    · exact hS.elim
    · rename_i i'
      cases i' with
      | dp tm bw =>
        rcases dd with dd | ⟨_ | _, τ⟩
        · exact hS.elim
        all_goals
          rcases hR.2 with h1 | h1
          · rw [hcn, cls_bar1] at h1; omega
          · omega
      | worker tm =>
        obtain ⟨-, -, hE, -⟩ := hR
        rcases hE with hE | h1 | h1
        · exfalso
          cases dd with
          | worker w =>
            obtain ⟨site, P⟩ := w
            simp only [S1] at hS
            simp only [WEarly] at hE
            rcases hE with rfl | rfl <;> simp at hS
          | _ => exact hE.elim
        · rw [hcn, cls_bar1] at h1; omega
        · omega
    · exact hR.elim

theorem bar1_exit_all (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hex : ∃ j pc, X.get (g, j) = some ⟨pc, .exit⟩) :
    1 ≤ (X.tr g).countP (Execution.isBarId 1) := by
  obtain ⟨j, pc, he⟩ := hex
  have h := bar1_exit hp hX he
  simp only [c1] at h
  have := (List.take_sublist j (X.tr g)).countP_le (p := Execution.isBarId 1)
  omega

/-! ### Thread 0's fence and the copies' fences -/

theorem cls_fence {ev : Event} (h : cls .fence ev = true) :
    ev.kind = .fenceProxy (.async (some (.shared .cta))) none := by
  obtain ⟨pc, k⟩ := ev
  simp only [cls] at h
  split at h
  · rfl
  · cases h

/-- The `n`-th event of a class before position `k`, with its position. -/
theorem nth_of_count {P : Event → Bool} {k q : Nat} (h : q + 1 ≤ ((X.tr g).take k).countP P) :
    ∃ j < k, ∃ e, X.get (g, j) = some e ∧ P e = true ∧ ((X.tr g).take j).countP P = q := by
  obtain ⟨j, e, hj, hp, hc⟩ := MbarRing.Slot.exists_nth_countP P h
  have hjk : j < k := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simp only [List.length_take] at this
    omega
  rw [List.take_take, Nat.min_eq_left hjk.le] at hc
  refine ⟨j, hjk, e, ?_, hp, hc⟩
  change (X.tr g)[j]? = some e
  rw [← hj, List.getElem?_take, ite_eq_left_iff.mpr (fun h => absurd hjk h)]

theorem proA_bar1 : ∀ p ∈ proASites, p ∈ bar1Pcs → p = 573 := by decide

/-- **The CTA's thread 0 made a proxy fence before its first barrier-1 event**, once a thread of
the CTA has made a barrier-1 event that it passed. -/
theorem thread0_fence (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {h j : Nat}
    (hh : h < L.threads) (hc : 1 ≤ c1 X h j) (hj : j < (X.tr h).length) :
    ∃ jf pcf, X.get (h / L.block * L.block, jf) =
        some ⟨pcf, .fenceProxy (.async (some (.shared .cta))) none⟩ ∧
      c1 X (h / L.block * L.block) (jf + 1) = 0 := by
  have hbk : L.block = 256 := hp.block
  have hblk : 0 < L.block := by omega
  have hg0t : h / L.block * L.block < L.threads :=
    lt_of_le_of_lt (Nat.div_mul_le_self h L.block) hh
  have hcta : h / L.block * L.block / L.block = h / L.block := Nat.mul_div_cancel _ hblk
  have hw0 : h / L.block * L.block % L.block = 0 := Nat.mul_mod_left _ _
  -- the first barrier-1 event of `h`
  obtain ⟨j1, hj1, ev, hget1, hb1, hc1⟩ := nth_of_count (X := X) (g := h) (q := 0) hc
  obtain ⟨pc1, k1⟩ := ev
  cases k1 with
  | bar id c md =>
    simp only [Execution.isBarId, beq_iff_eq] at hb1
    subst hb1
    obtain ⟨rfl, h1 | ⟨h1, -⟩⟩ := bar_event_static hX (by omega) hget1
    swap; · cases h1
    obtain ⟨rfl, -⟩ := h1
    have hf : X.IsBarrier (h, j1) 1 none pc1 := hget1
    obtain ⟨i0, pc0, md0, hget0, hc0⟩ := (bar1_sources hp hX).member_arrival_any hX
      (bar1_shape hp) hf (by simp only; omega) (g := h / L.block * L.block) (by rw [hcta])
      (by simp only [Finset.mem_range, CtaBarrier.warps, hbk]; omega) (by
        intro hex
        have hall := bar1_exit_all hp hX hex
        rw [← List.take_length (l := X.tr (h / L.block * L.block))] at hall
        obtain ⟨i, -, ev', hget', hb', hc'⟩ := nth_of_count (q := 0) hall
        obtain ⟨pci, ki⟩ := ev'
        cases ki with
        | bar idi ci mi =>
          simp only [Execution.isBarId, beq_iff_eq] at hb'
          subst hb'
          have hci := ((bar1_sources hp hX) _ _ _ ⟨mi, hget'⟩ hg0t).2
          subst hci
          exact ⟨i, pci, mi, hget', by simp only; rw [hc', hc1]⟩
        | _ => simp [Execution.isBarId] at hb')
    simp only at hc0
    rw [hc1] at hc0
    have hu0 : ∀ f, (⟨pc0, .bar 1 none md0⟩ : Event).kind ≠ .ub f := by simp
    have hc0' : ((X.tr (h / L.block * L.block)).take i0).countP (cls (.bar 1)) = 0 := by
      rw [cls_bar1]; exact hc0
    rcases before_or_entry (Q := Q) (X := X) (g := h / L.block * L.block) i0 with
      hB | ⟨i, hii, hB, d, hd, hS⟩
    · obtain ⟨d, hd, hR⟩ := state1 hp hX hget0 hu0 hB
      obtain ⟨x, n⟩ := d
      have hcn : ∀ c, n c = ((X.tr (h / L.block * L.block)).take i0).countP (cls c) :=
        fun c => fcount hd c
      have h0 : n .ub = 0 := by rw [hcn .ub]; exact ub0 hX hget0 hu0 le_rfl
      rcases x with s | ⟨_ | r, dd⟩
      · exfalso
        have := (start_cls hR (start_ev hp hX hget0 hd)).1
        simp [cls] at this
      · rename_i i'
        cases i' with
        | dp tm bw =>
          rcases dd with dd | ⟨_ | _, τ⟩
          · obtain ⟨t, ins, o, hcd, hfd⟩ := fired_pc hp hX hget0 hd
            have hpc := bar1_pc hcd hfd (show (⟨pc0, .bar 1 none md0⟩ : Event).kind = _ from rfl)
              (by omega)
            have h573 : dd.site.pc = 573 := proA_bar1 _ (ProA.site_mem dd.site) hpc
            rcases hR.2.2 (by rw [h573]; decide) with h1 | h1
            · rw [hcn] at h1
              obtain ⟨jf, hjf, ev, hgetf, hcf⟩ := exists_of_count h1
              refine ⟨jf, ev.pc, ?_, ?_⟩
              · rw [hgetf, ← cls_fence hcf]
              · have := countP_mono_take (X := X) (g := h / L.block * L.block)
                  (P := Execution.isBarId 1) (show jf + 1 ≤ i0 by omega)
                simp only [c1]
                omega
            · omega
          all_goals
            exfalso
            rcases hR.2 with h1 | h1
            · rw [hcn, hc0'] at h1; omega
            · omega
        | worker tm =>
          exfalso
          have := hR.2.2.2
          rw [hw0] at this
          omega
      · exact hR.elim
    · exfalso
      have hR := entry1 hp hX hg0t hB hd
      obtain ⟨x, n⟩ := d
      have hcn : ∀ c, n c = ((X.tr (h / L.block * L.block)).take i).countP (cls c) :=
        fun c => fcount hd c
      have h0 : n .ub = 0 := by rw [hcn .ub]; exact ub0 hX hget0 hu0 hii.le
      have hmono := countP_mono_take (X := X) (g := h / L.block * L.block) (P := cls (.bar 1))
        hii.le
      rcases x with s | ⟨_ | r, dd⟩
      · exact hS
      · rename_i i'
        cases i' with
        | dp tm bw =>
          rcases dd with dd | ⟨_ | _, τ⟩
          · exact hS
          all_goals
            rcases hR.2 with h1 | h1
            · rw [hcn] at h1; omega
            · omega
        | worker tm =>
          have := hR.2.2.2
          rw [hw0] at this
          omega
      · exact hR
  | _ => simp [Execution.isBarId] at hb1

/-- Thread 0's fence is before every event of a thread of its CTA after the thread's first
barrier-1 event (barrier 1's first instance, `Handoff.of_bar_upTo`). -/
theorem thread0_before (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {h j : Nat}
    (hh : h < L.threads) (hc : 1 ≤ c1 X h j) (hj : j < (X.tr h).length) :
    ∃ jf pcf, X.get (h / L.block * L.block, jf) =
        some ⟨pcf, .fenceProxy (.async (some (.shared .cta))) none⟩ ∧
      baseCausality L X (h / L.block * L.block, jf) (h, j) := by
  have hbk : L.block = 256 := hp.block
  have hblk : 0 < L.block := by omega
  have hg0t : h / L.block * L.block < L.threads :=
    lt_of_le_of_lt (Nat.div_mul_le_self h L.block) hh
  have hcta : h / L.block * L.block / L.block = h / L.block := Nat.mul_div_cancel _ hblk
  obtain ⟨jf, pcf, hget, hcf⟩ := thread0_fence hp hX hh hc hj
  refine ⟨jf, pcf, hget, ?_⟩
  have H := Frame.Handoff.of_bar_upTo hX (bar1_sources hp hX) (bar1_shape hp)
    (syncs := fun _ => True)
    (fun h' j' pc' cnt md _ he' => (bar_event_static hX (by omega) he').1) 1
    (fun g' hg' _ hex => bar1_exit_all hp hX hex)
  refine H _ _ _ _ ⟨⟨hg0t, hh, by rw [hcta]⟩, ?_, trivial⟩ hj ?_
  · have := Nat.mod_lt (h / L.block * L.block) hblk
    simp only [Finset.mem_range, CtaBarrier.warps, hbk]
    omega
  · simp only [c1] at hcf hc
    simp only [hcf]
    omega

/-- **Every tensor-copy issue comes after a proxy fence of a thread of its CTA**, in base
causality. -/
theorem issue_fence (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {h j pc a : Nat}
    {sp : TensorCopy.Spec} (he : X.get (h, j) = some ⟨pc, .tensorIssue a sp⟩) :
    ∃ f jf pcf, f / L.block = h / L.block ∧ f < L.threads ∧
      X.get (f, jf) = some ⟨pcf, .fenceProxy (.async (some (.shared .cta))) none⟩ ∧
      baseCausality L X (f, jf) (h, j) := by
  have hh := Frame.lt_of_get hX he
  have hbk : L.block = 256 := hp.block
  have hblk : 0 < L.block := by omega
  have hjl : j < (X.tr h).length := (List.getElem?_eq_some_iff.mp he).1
  have hu : ∀ f, (⟨pc, .tensorIssue a sp⟩ : Event).kind ≠ .ub f := by simp
  have hg0t : h / L.block * L.block < L.threads :=
    lt_of_le_of_lt (Nat.div_mul_le_self h L.block) hh
  have hcta : h / L.block * L.block / L.block = h / L.block := Nat.mul_div_cancel _ hblk
  -- the issuer's own fence before position `i ≤ j`
  have own : ∀ i ≤ j, 1 ≤ ((X.tr h).take i).countP (cls .fence) →
      ∃ f jf pcf, f / L.block = h / L.block ∧ f < L.threads ∧
        X.get (f, jf) = some ⟨pcf, .fenceProxy (.async (some (.shared .cta))) none⟩ ∧
        baseCausality L X (f, jf) (h, j) := by
    intro i hi h1
    obtain ⟨jf, hjf, ev, hgetf, hcf⟩ := exists_of_count h1
    refine ⟨h, jf, ev.pc, rfl, hh, by rw [hgetf, ← cls_fence hcf], ?_⟩
    have hk := cls_fence hcf
    obtain ⟨pcv, kv⟩ := ev
    simp only at hk
    subst hk
    exact .single (.inl (po_of_source_not_access (X := X) rfl (by simp only; omega) hjl (by
      rw [hgetf]; rfl)))
  -- thread 0's fence
  have zero : ∀ i ≤ j, 1 ≤ c1 X h i →
      ∃ f jf pcf, f / L.block = h / L.block ∧ f < L.threads ∧
        X.get (f, jf) = some ⟨pcf, .fenceProxy (.async (some (.shared .cta))) none⟩ ∧
        baseCausality L X (f, jf) (h, j) := by
    intro i hi h1
    have h1' : 1 ≤ c1 X h j := le_trans h1 (countP_mono_take hi)
    obtain ⟨jf, pcf, hget, hbc⟩ := thread0_before hp hX hh h1' hjl
    exact ⟨_, jf, pcf, hcta, hg0t, hget, hbc⟩
  rcases before_or_entry (Q := Q) (X := X) (g := h) j with hB | ⟨i, hij, hB, d, hd, hS⟩
  · obtain ⟨d, hd, hR⟩ := state1 hp hX he hu hB
    obtain ⟨x, n⟩ := d
    have hcn : ∀ c, n c = ((X.tr h).take j).countP (cls c) := fun c => fcount hd c
    have h0 : n .ub = 0 := by rw [hcn .ub]; exact ub0 hX he hu le_rfl
    obtain ⟨t, ins, o, hcd, hfd⟩ := fired_pc hp hX he hd
    have hcopy : (thread Q L h).pc (x, n) ∈ copyPcs := by
      apply OpPcsFast.mem kernel_copy_pcs hcd
      cases hq : tensorOp ins.op
      · exact (fires_notTensor (eventTmpl_notTensor hq) hfd a sp rfl).elim
      · rfl
    rcases x with s | ⟨_ | r, dd⟩
    · exfalso
      have := Startup.site_mem s.site
      change s.site.pc ∈ copyPcs at hcopy
      revert hcopy this
      generalize s.site.pc = q
      intro h1 h2
      simp [copyPcs, startupSites] at h1 h2
      omega
    · rename_i i'
      cases i' with
      | dp tm bw =>
        rcases dd with dd | ⟨_ | _, τ⟩
        · have hgt : 179 < dd.site.pc := by
            change dd.site.pc ∈ copyPcs at hcopy
            revert hcopy
            generalize dd.site.pc = q
            intro h1
            simp [copyPcs] at h1
            omega
          rcases hR.2.2 hgt with h1 | h1
          · exact own j le_rfl (by rw [hcn] at h1; exact h1)
          · omega
        all_goals
          rcases hR.1 with h1 | h1
          · exact own j le_rfl (by rw [hcn] at h1; exact h1)
          · omega
      | worker tm =>
        obtain ⟨-, -, hE, -⟩ := hR
        rcases hE with hE | h1 | h1
        · exfalso
          cases dd with
          | worker w =>
            obtain ⟨site, P⟩ := w
            simp only [WEarly] at hE
            rcases hE with rfl | rfl
            · exact absurd hcopy (show (Proof.Worker.Site.loop).pc ∉ copyPcs by decide)
            · exact absurd hcopy (show (Proof.Worker.Site.bar2).pc ∉ copyPcs by decide)
          | _ => exact hE.elim
        · exact zero j le_rfl (by rw [hcn, cls_bar1] at h1; exact h1)
        · omega
    · exact hR.elim
  · have hR := entry1 hp hX hh hB hd
    obtain ⟨x, n⟩ := d
    have hcn : ∀ c, n c = ((X.tr h).take i).countP (cls c) := fun c => fcount hd c
    have h0 : n .ub = 0 := by rw [hcn .ub]; exact ub0 hX he hu hij.le
    rcases x with s | ⟨_ | r, dd⟩
    · exact hS.elim
    · rename_i i'
      cases i' with
      | dp tm bw =>
        rcases dd with dd | ⟨_ | _, τ⟩
        · exact hS.elim
        all_goals
          rcases hR.1 with h1 | h1
          · exact own i hij.le (by rw [hcn] at h1; exact h1)
          · omega
      | worker tm =>
        obtain ⟨-, -, hE, -⟩ := hR
        rcases hE with hE | h1 | h1
        · exfalso
          cases dd with
          | worker w =>
            obtain ⟨site, P⟩ := w
            simp only [S1] at hS
            simp only [WEarly] at hE
            rcases hE with rfl | rfl <;> simp at hS
          | _ => exact hE.elim
        · exact zero i hij.le (by rw [hcn, cls_bar1] at h1; exact h1)
        · omega
    · exact hR.elim

end
end PTX.Kernels.InklingRelDecode.Proof2
