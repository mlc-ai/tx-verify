-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.Foot
public import Kernels.InklingRelDecode.Proof2.Lib.BarLaneKeys

@[expose] public section

/-! # Barrier 0 on the role table: its events, their counts, the last `bar.sync 0`

Read off the code: the kernel's `bar.sync 0` without a count is at pcs 12 and 14 (the startup),
2850 (the epilogue's last barrier) and 2853 (the worker exit path's); its `bar.sync 0, 128` at
21 positions of the prologue and the softmax region (`kernel_b0n_pcs`, `kernel_b0c_pcs`).

* `c0_inv`: along a thread, the barrier-0 events before a startup state are 0, 1 or 2 by its
  site, and at least 2 before every role state (an induction like `tm_inv`; a role state's
  successor is a role state of the same role, whose count does not decrease).
* `b0_class`: every barrier-0 event is `bar.sync 0` without a count, or `bar.sync 0, 128` of a
  default-partition lane with at least two earlier barrier-0 events.
* `post_inv`: a state at the epilogue's deallocation or return or at the exit path's return has an
  earlier `bar.sync 0` without a count and with at least two barrier-0 events before it (its
  thread's last `bar.sync 0`); `post_after`: every position after such a `bar.sync 0` is at such
  a state. These are the thread facts of the barrier-1 exit argument (`Safety/Bar1Exit.lean`). -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-! ### The barrier instructions -/

/-- **A barrier event's instruction**: `bar.sync id` without a count, or `bar.sync 0, 128`. -/
theorem bar_form {t : TState} {ins : Instr} {pc : Nat} {e : Event} {o : Option TState}
    (hc : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o) {id : Nat} {c : Option Nat}
    {md : BarMode} (hk : e.kind = .bar id c md) (hb : L.block ≠ 128) :
    (∃ al, ins.op = .barSync (.imm id) al ∧ c = none) ∨
      (∃ al, ins.op = .barSyncN (.imm 0) (.imm 128) al ∧ id = 0 ∧ c = some 128) := by
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
      obtain ⟨rfl, rfl, -⟩ := hk
      exact .inl ⟨al, rfl, rfl⟩
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
            simp only [Kind.bar.injEq] at hk
            obtain ⟨rfl, rfl, -⟩ := hk
            exact .inr ⟨al, rfl, rfl, rfl⟩
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

/-- A `bar.sync 0` without a count. -/
def b0nOp : Op → Bool
  | .barSync (.imm 0) _ => true
  | _ => false

def b0nPcs : List Nat := [12, 14, 2850, 2853]

theorem kernel_b0n_pcs : OpPcsFast kernel.code b0nOp b0nPcs = true := by decide +kernel

/-- A `bar.sync 0, 128`. -/
def b0cOp : Op → Bool
  | .barSyncN (.imm 0) _ _ => true
  | _ => false

def b0cPcs : List Nat :=
  [180, 192, 201, 212, 222, 227, 236, 243, 254, 264, 269, 278, 285, 296, 306, 311, 999, 1012,
    2241, 2251, 2326]

theorem kernel_b0c_pcs : OpPcsFast kernel.code b0cOp b0cPcs = true := by decide +kernel

/-- **A `bar.sync 0` event without a count is at one of four positions.** -/
theorem b0n_pc {t : TState} {ins : Instr} {pc : Nat} {e : Event} {o : Option TState}
    (hc : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o) {md : BarMode}
    (hk : e.kind = .bar 0 none md) (hb : L.block ≠ 128) : pc ∈ b0nPcs := by
  refine OpPcsFast.mem kernel_b0n_pcs hc ?_
  rcases bar_form hc hf hk hb with ⟨al, h, -⟩ | ⟨al, -, -, h⟩
  · rw [h]; rfl
  · cases h

/-- **A `bar.sync 0, 128` event is at one of 21 positions.** -/
theorem b0c_pc {t : TState} {ins : Instr} {pc : Nat} {e : Event} {o : Option TState}
    (hc : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o) {c : Nat} {md : BarMode}
    (hk : e.kind = .bar 0 (some c) md) (hb : L.block ≠ 128) : pc ∈ b0cPcs := by
  refine OpPcsFast.mem kernel_b0c_pcs hc ?_
  rcases bar_form hc hf hk hb with ⟨al, -, h⟩ | ⟨al, h, -, -⟩
  · cases h
  · rw [h]; rfl

local macro "site_none" : tactic =>
  `(tactic| (intro s h; revert h; cases s <;> (try (rename_i j; revert j)) <;> decide +kernel))

theorem startup_b0n : ∀ s : Startup.Site, s.pc ∈ b0nPcs → s = .bar0 ∨ s = .bar1 := by
  intro s h; revert h
  cases s with
  | bar0 => intro _; exact .inl rfl
  | bar1 => intro _; exact .inr rfl
  | enter r => cases r <;> decide
  | _ => decide

theorem proA_b0n (s : ProA.Site) (h : s.pc ∈ b0nPcs) : False := by
  cases s with
  | ld k | el k | init k | arr k | psh k | ldq k | st9 k =>
    revert h; revert k; decide
  | pb b j | lb b j | pel b j | ptc b j | stq b j =>
    revert h; revert j; revert b; decide
  | _ => revert h; decide

theorem sm_b0n : ∀ s : Proof.Sm.Site, s.pc ∈ b0nPcs → False := by site_none
theorem epi_b0n : ∀ s : Proof.Epi.Site, s.pc ∈ b0nPcs → s = .bar3 := by
  intro s h; revert h; cases s <;> (try (rename_i j; revert j)) <;> decide +kernel
theorem worker_b0n : ∀ s : Proof.Worker.Site, s.pc ∈ b0nPcs →
    s = .bar0 ∨ s = .bar1 ∨ s = .toExit := by
  intro s h; revert h; cases s <;> decide +kernel
theorem idle_b0n : ∀ s : Proof.Worker.Idle.Site, s.pc ∈ b0nPcs → False := by site_none
theorem loader_b0n : ∀ s : Proof.Loader.Site, s.pc ∈ b0nPcs → False := by site_none
theorem mma_b0n : ∀ s : Proof.Mma.Site, s.pc ∈ b0nPcs → False := by site_none
theorem exitsite_b0n : ∀ s : Proof.WComp.ExitSite, s.pc ∈ b0nPcs → s = .bar := by
  intro s h; revert h; cases s <;> decide +kernel

theorem startup_b0c : ∀ s : Startup.Site, s.pc ∈ b0cPcs → False := by
  intro s h; revert h
  cases s with
  | enter r => cases r <;> decide
  | _ => decide
theorem epi_b0c : ∀ s : Proof.Epi.Site, s.pc ∈ b0cPcs → False := by site_none
theorem worker_b0c : ∀ s : Proof.Worker.Site, s.pc ∈ b0cPcs → False := by site_none
theorem idle_b0c : ∀ s : Proof.Worker.Idle.Site, s.pc ∈ b0cPcs → False := by site_none
theorem loader_b0c : ∀ s : Proof.Loader.Site, s.pc ∈ b0cPcs → False := by site_none
theorem mma_b0c : ∀ s : Proof.Mma.Site, s.pc ∈ b0cPcs → False := by site_none
theorem exitsite_b0c : ∀ s : Proof.WComp.ExitSite, s.pc ∈ b0cPcs → False := by site_none


/-! ### The barrier-0 count along a thread -/

/-- The barrier-0 events before the event of a startup state. -/
def startC0 (s : Startup.D) : Nat :=
  match s.site with
  | .alloc | .allocWr | .bar0 => 0
  | .ld0 | .bar1 => 1
  | .relinq | .shfl | .enter _ => 2

/-- **The barrier-0 count of a state**: the startup's by site, at least 2 at a role state. -/
def C0 (Q : Params) (L : Launch) (g : Nat) : (thread Q L g).D → Nat → Prop
  | (.inl s, _), c => c = startC0 s
  | (.inr _, _), c => 2 ≤ c

theorem countP_snoc (P : Event → Bool) (l : List Event) (e : Event) :
    (l ++ [e]).countP P = l.countP P + if P e then 1 else 0 := by
  simp only [List.countP_append, List.countP_singleton]

/-- A role state's successor is a role state. -/
theorem next_inr {x : Σ i, (Code.withStubs (frag Q L g) Startup.Entry.pc i).D} {n : Cls → Nat}
    {e : Event} {σ' : (thread Q L g).D} (h : (thread Q L g).next (.inr x, n) e = some (some σ')) :
    ∃ y, σ'.1 = .inr y := by
  obtain ⟨i, d⟩ := x
  simp only [thread, Code.roleThread, Code.counted, Code.glue] at h
  rcases hr : (Code.withStubs (frag Q L g) Startup.Entry.pc i).next d e with _ | _ | d'
  · rw [hr] at h; simp at h
  · rw [hr] at h; simp at h
  · rw [hr] at h
    simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨_, by rw [← h]⟩

/-- **A continuing step keeps the barrier-0 count.** -/
theorem c0_step (hp : Pre Q L m) (hg : g < L.threads) {σ σ' : (thread Q L g).D} {e : Event}
    {t u : TState} {ins : Instr} (hJ : Ref Q L g σ) (hat : (thread Q L g).AtD σ t)
    (hi : (thread Q L g).inv σ) (hc : kernel.code[(thread Q L g).pc σ]? = some ins)
    (hf : Fires ((thread Q L g).pc σ) (eventTmpl Assumptions.all L g t ins.op) e (some u))
    {c : Nat} (hC : C0 Q L g σ c) (hn : (thread Q L g).next σ e = some (some σ')) :
    C0 Q L g σ' (c + if Execution.isBarId 0 e then 1 else 0) := by
  have hev := frag_ev hp hg hJ hat hi hc hf
  obtain ⟨x, n⟩ := σ
  rcases x with s | y
  · have hC' : c = startC0 s := hC
    rw [next_start] at hn
    obtain ⟨s', hs', rfl⟩ := mm_some hn
    obtain ⟨site, tm, x, w⟩ := s
    cases site with
    | enter r => exact hJ.elim
    | shfl =>
      have hev' : Startup.Ev L g ⟨.shfl, tm, x, w⟩ e := hev
      simp only [Startup.Ev] at hev'
      obtain ⟨recv, ok, rfl⟩ := hev'
      simp only [Startup.succ] at hs'
      split at hs'
      · simp only [Option.some.injEq] at hs'
        subst hs'
        simp only [Code.enter, Code.gatedExit, Startup.enterOf, Option.map_some]
        show 2 ≤ _
        simp [Execution.isBarId, hC', startC0]
      · simp at hs'
    | _ =>
      have hev' := hev
      simp only [FragEv, Startup.Ev] at hev'
      simp only [Startup.succ] at hs'
      repeat' split at hs'
      all_goals first
        | (simp only [Option.some.injEq, reduceCtorEq] at hs'; done)
        | (simp only [Option.some.injEq] at hs'
           subst hs'
           rw [enter_inl (by simp [Startup.enterOf])]
           first
             | (subst hev'; simp [C0, startC0, Execution.isBarId, hC'])
             | (obtain ⟨_, _, rfl, -⟩ := hev'; simp [C0, startC0, Execution.isBarId, hC']))
  · obtain ⟨y', hy'⟩ := next_inr hn
    obtain ⟨x', n'⟩ := σ'
    simp only at hy'
    subst hy'
    show 2 ≤ _
    have : 2 ≤ c := hC
    omega

/-- **The barrier-0 count along a thread.** -/
theorem c0_inv (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) :
    ∀ k, k < (X.tr g).length → ∀ σ, Frame.stateAt (thread Q L) X g k = some (some σ) →
      C0 Q L g σ (((X.tr g).take k).countP (Execution.isBarId 0)) := by
  intro k
  induction k with
  | zero =>
    intro _ σ hσ
    rw [Frame.stateAt_zero, thread_init_eq] at hσ
    obtain rfl := Option.some.inj (Option.some.inj hσ)
    show _ = startC0 _
    unfold Startup.init
    split <;> rfl
  | succ k ih =>
    intro hk σ' hσ'
    have hlt : k < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    rw [Frame.stateAt_succ he] at hσ'
    have hF := good_all' hp hX hg k
    rcases hk0 : Frame.stateAt (thread Q L) X g k with _ | _ | σ
    · rw [hk0] at hσ'; cases hσ'
    · exact absurd hk0 hF.1
    · rw [hk0] at hσ'
      have hn : (thread Q L g).next σ e = some (some σ') := hσ'
      obtain ⟨t, ins, o, hat, hi, hc, hf⟩ :=
        Frame.fired_site (fun g hg => thread_sound hp hg) hX (k := k) he hk0
      cases o with
      | none => exact absurd (fires_none_ends hf) (not_ends_of_lt hX hg he hk)
      | some u =>
        rw [List.take_add_one, he, Option.toList_some, countP_snoc]
        exact c0_step hp hg (hF.2 σ hk0) hat hi hc hf (ih hlt σ hk0) hn

/-! ### The classification of barrier-0 events -/

/-- **Every barrier-0 event is `bar.sync 0` without a count, or `bar.sync 0, 128` of a lane of
warps 0 to 3 with at least two earlier barrier-0 events.** -/
theorem b0_class (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {g k pc : Nat} {c : Option Nat} {md : BarMode} (he : X.get (g, k) = some ⟨pc, .bar 0 c md⟩) :
    c = none ∨ (c = some 128 ∧ g % L.block < 128 ∧
      2 ≤ ((X.tr g).take k).countP (Execution.isBarId 0)) := by
  have hb : L.block = 256 := hp.block
  rcases (bar_event_static hX (by omega) he).2 with ⟨h, -⟩ | ⟨-, h⟩
  · exact .inl h
  · subst h
    refine .inr ⟨rfl, ?_⟩
    have hg := Frame.lt_of_get hX he
    obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
    have hlen : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
    have hC := c0_inv hp hX hg k hlen σ hσ
    have hpc := b0c_pc hc hf rfl (by omega)
    obtain ⟨x, n⟩ := σ
    rcases x with st | ⟨_ | r, d⟩
    · exact (startup_b0c st.site hpc).elim
    · rename_i i
      have hC' : 2 ≤ ((X.tr g).take k).countP (Execution.isBarId 0) := hC
      cases i with
      | dp tm bw =>
        rcases d with d | ⟨_ | _, τ⟩
        · exact ⟨hi.1.args.tid, hC'⟩
        · cases τ with
          | sm d => exact ⟨(hi : Proof.Sm.Inv L g d).tid, hC'⟩
          | epi d => exact (epi_b0c d.site hpc).elim
        · exact hJ.elim
      | worker w =>
        cases d with
        | worker w => exact (worker_b0c w.site hpc).elim
        | idle d => exact (idle_b0c d.site hpc).elim
        | loader d P => exact (loader_b0c d.site hpc).elim
        | mma d P => exact (mma_b0c d.site hpc).elim
        | exit x => exact (exitsite_b0c x.site hpc).elim
    · exact hJ.elim

/-- The loop group of named barrier 0: warps 0 to 3. -/
def loopGroup : Finset Nat := Finset.range 4

theorem loopGroup_sub (hp : Pre Q L m) :
    loopGroup ⊆ Finset.range (CtaBarrier.warps L.block) := by
  intro w hw
  have hb : L.block = 256 := hp.block
  simp only [loopGroup, Finset.mem_range, CtaBarrier.warps, hb] at hw ⊢
  omega

theorem loopGroup_card : loopGroup.card = 4 := by
  simp [loopGroup]

theorem loopGroup_ne (hp : Pre Q L m) : 4 ≠ CtaBarrier.warps L.block := by
  have hb : L.block = 256 := hp.block
  simp [CtaBarrier.warps, hb]

theorem loopGroup_target : CtaBarrier.target L.block (some 128) = .ok 4 := by
  simp [CtaBarrier.target]

/-- **Barrier 0's arrivals follow the phased classification**: no count, or the count 128 from
the loop group with a source ordinal at least 2. -/
theorem bar0_phSources (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) :
    NamedBar.PhSources L X loopGroup (some 128) 2 0 := by
  intro e pc cnt ⟨md, he⟩ hg
  obtain ⟨g, k⟩ := e
  rcases b0_class hp hX he with h | ⟨h1, h2, h3⟩
  · exact .inl h
  · refine .inr ⟨h1, ?_, h3⟩
    simp only [loopGroup, Finset.mem_range]
    omega

/-! ### The thread's last `bar.sync 0` -/

/-- The states after a thread's last `bar.sync 0`: the epilogue's deallocation and return, the
exit path's return. -/
def IsPost (Q : Params) (L : Launch) (g : Nat) : (thread Q L g).D → Prop
  | (.inr ⟨.inl (.dp _ _), .inr ⟨.inl _, .epi d⟩⟩, _) => d.site = .dealloc ∨ d.site = .exit
  | (.inr ⟨.inl (.worker _), .exit x⟩, _) => x.site = .ret
  | _ => False

/-- The states of a thread's last `bar.sync 0`: the epilogue's and the exit path's. -/
def IsLast (Q : Params) (L : Launch) (g : Nat) : (thread Q L g).D → Prop
  | (.inr ⟨.inl (.dp _ _), .inr ⟨.inl _, .epi d⟩⟩, _) => d.site = .bar3
  | (.inr ⟨.inl (.worker _), .exit x⟩, _) => x.site = .bar
  | _ => False

theorem epi_pred {d d' : Proof.Epi.D} {e : Event} (h : Proof.Epi.next d e = some (some d'))
    (hp : d'.site = .dealloc ∨ d'.site = .exit) : d.site = .bar3 ∨ d.site = .dealloc := by
  unfold Proof.Epi.next at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at h; done)
    | (simp only [Option.some.injEq] at h; subst h
       simp_all [Proof.Epi.D.stores, Proof.Epi.stNext]
       done)
    | (simp only [Option.some.injEq] at h; subst h
       simp_all [Proof.Epi.D.stores, Proof.Epi.stNext]
       split_ifs at hp <;> simp_all)

theorem wcomp_pred {σ : Proof.WComp.WSt} {e : Event} {P : Proof.Loader.Pro}
    (h : Proof.WComp.next L g σ e = some (some (.exit ⟨.ret, P⟩))) :
    ∃ P', σ = .exit ⟨.bar, P'⟩ := by
  cases σ with
  | worker w =>
    obtain ⟨site, P0⟩ := w
    cases site
    case ldRole =>
      simp only [Proof.WComp.next, Proof.WComp.dispatch] at h
      repeat' split at h
      all_goals first
        | (cases h)
        | (simp only [Proof.WComp.roleStart] at h
           repeat' split at h
           all_goals simp at h)
    all_goals
      simp only [Proof.WComp.next] at h
      rcases hr : Proof.Worker.next L g _ e with _ | _ | w' <;> rw [hr] at h <;> simp at h
  | idle d =>
    simp only [Proof.WComp.next] at h
    split at h
    · simp at h
    · rcases hr : Proof.Worker.Idle.next d e with _ | _ | d' <;> rw [hr] at h <;> simp at h
  | loader d P0 =>
    simp only [Proof.WComp.next] at h
    split at h
    · simp at h
    · rcases hr : Proof.Loader.next L g d e with _ | _ | d' <;> rw [hr] at h <;> simp at h
  | mma d P0 =>
    simp only [Proof.WComp.next] at h
    split at h
    · simp at h
    · rcases hr : Proof.Mma.next L g d e with _ | _ | d' <;> rw [hr] at h <;> simp at h
  | exit x =>
    obtain ⟨site, P0⟩ := x
    cases site
    · exact ⟨P0, rfl⟩
    · simp [Proof.WComp.next] at h

theorem entry_notPost (j : Role ⊕ Startup.Entry) (n : Cls → Nat) :
    ¬ IsPost Q L g (.inr ⟨j, (Code.withStubs (frag Q L g) Startup.Entry.pc j).init⟩, n) := by
  rcases j with (_ | _) | _ <;> exact id

/-- **A state after the last `bar.sync 0` follows one, or is the last `bar.sync 0`'s state.** -/
theorem post_pred {σ σ' : (thread Q L g).D} {e : Event} (hJ : Ref Q L g σ)
    (hn : (thread Q L g).next σ e = some (some σ')) (hp : IsPost Q L g σ') :
    IsPost Q L g σ ∨ IsLast Q L g σ := by
  obtain ⟨x, n⟩ := σ
  rcases x with s | ⟨_ | r, d⟩
  · rw [next_start] at hn
    obtain ⟨s', -, rfl⟩ := mm_some hn
    exfalso
    revert hp
    simp only [Code.enter]
    split
    · exact entry_notPost _ _
    · exact id
  · rename_i i
    cases i with
    | dp tm bw =>
      rcases d with d | ⟨_ | _, τ⟩
      · rw [next_pro] at hn
        obtain ⟨d', -, rfl⟩ := mm_some hn
        exfalso
        revert hp
        simp only [Code.enter]
        split
        · rename_i j _
          rcases j with _ | _ <;> exact id
        · exact id
      · rw [next_tail] at hn
        obtain ⟨τ', hτ, rfl⟩ := mm_some hn
        cases τ with
        | sm d =>
          exfalso
          simp only [Tail.next] at hτ
          split at hτ
          · simp only [Tail.exitNext] at hτ
            split at hτ
            · simp only [Option.some.injEq] at hτ
              subst hτ
              simp [IsPost, Proof.Epi.D.entry] at hp
            · cases hτ
          · obtain ⟨d', -, rfl⟩ := mm_some hτ
            exact hp
        | epi d =>
          simp only [Tail.next] at hτ
          obtain ⟨d', hd', rfl⟩ := mm_some hτ
          rcases epi_pred hd' hp with h | h
          · exact .inr h
          · exact .inl (.inl h)
      · exact hJ.elim
    | worker w =>
      rw [next_worker] at hn
      obtain ⟨σw', hσw, rfl⟩ := mm_some hn
      cases σw' with
      | exit x =>
        obtain ⟨site, P⟩ := x
        have hs : site = .ret := hp
        subst hs
        obtain ⟨P', rfl⟩ := wcomp_pred hσw
        exact .inr rfl
      | _ => exact hp.elim
  · exact hJ.elim

/-- **The event of a last `bar.sync 0`'s state** is `bar.sync 0` without a count. -/
theorem last_event (hp : Pre Q L m) (hg : g < L.threads) {σ : (thread Q L g).D} {e : Event}
    {t u : TState} {ins : Instr} (hJ : Ref Q L g σ) (hat : (thread Q L g).AtD σ t)
    (hi : (thread Q L g).inv σ) (hc : kernel.code[(thread Q L g).pc σ]? = some ins)
    (hf : Fires ((thread Q L g).pc σ) (eventTmpl Assumptions.all L g t ins.op) e (some u))
    (hl : IsLast Q L g σ) : ∃ pc, e = ⟨pc, .bar 0 none .sync⟩ := by
  obtain ⟨x, n⟩ := σ
  rcases x with s | ⟨_ | r, d⟩
  · exact hl.elim
  · rename_i i
    cases i with
    | dp tm bw =>
      rcases d with d | ⟨_ | _, τ⟩
      · exact hl.elim
      · cases τ with
        | sm d => exact hl.elim
        | epi d =>
          have hs : d.site = .bar3 := hl
          have hev := frag_ev hp hg hJ hat hi hc hf
          simp only [FragEv, Proof.Epi.Shape, hs] at hev
          exact ⟨_, hev⟩
      · exact hl.elim
    | worker w =>
      cases d with
      | exit x =>
        obtain ⟨site, P⟩ := x
        have hs : site = .bar := hl
        subst hs
        have hc' : kernel.code[2853]? = some ins := hc
        rw [Flow.code_bar_37] at hc'
        obtain rfl := Option.some.inj hc'
        exact ⟨_, Proof.EvD.fires_barSync_imm (by omega) hf⟩
      | _ => exact hl.elim
  · exact hl.elim

/-- **After the last `bar.sync 0` the thread stays after it.** -/
theorem post_next {σ σ' : (thread Q L g).D} {e : Event} (hp : IsPost Q L g σ ∨ IsLast Q L g σ)
    (hn : (thread Q L g).next σ e = some (some σ')) : IsPost Q L g σ' := by
  obtain ⟨x, n⟩ := σ
  rcases x with s | ⟨_ | r, d⟩
  · exact (hp.elim id id).elim
  · rename_i i
    cases i with
    | dp tm bw =>
      rcases d with d | ⟨_ | _, τ⟩
      · exact (hp.elim id id).elim
      · cases τ with
        | sm d => exact (hp.elim id id).elim
        | epi d =>
          rw [next_tail] at hn
          obtain ⟨τ', hτ, rfl⟩ := mm_some hn
          simp only [Tail.next] at hτ
          obtain ⟨d', hd', rfl⟩ := mm_some hτ
          have hs : d.site = .dealloc ∨ d.site = .exit ∨ d.site = .bar3 := by
            rcases hp with h | h
            · rcases h with h | h
              · exact .inl h
              · exact .inr (.inl h)
            · exact .inr (.inr h)
          show d'.site = .dealloc ∨ d'.site = .exit
          rcases hs with h | h | h
          · simp only [Proof.Epi.next, h, Option.some.injEq] at hd'
            subst hd'; exact .inr rfl
          · simp [Proof.Epi.next, h] at hd'
          · simp only [Proof.Epi.next, h, Option.some.injEq] at hd'
            subst hd'
            split <;> simp
      · exact (hp.elim id id).elim
    | worker w =>
      rw [next_worker] at hn
      obtain ⟨σw', hσw, rfl⟩ := mm_some hn
      cases d with
      | exit x =>
        obtain ⟨site, P⟩ := x
        cases site
        · simp only [Proof.WComp.next, Option.some.injEq] at hσw
          subst hσw; rfl
        · simp [Proof.WComp.next] at hσw
      | _ => exact (hp.elim id id).elim
  · exact (hp.elim id id).elim

/-- The positions of the states after the last `bar.sync 0`. -/
theorem post_pc {σ : (thread Q L g).D} (h : IsPost Q L g σ) :
    (thread Q L g).pc σ = 2851 ∨ (thread Q L g).pc σ = 2855 := by
  obtain ⟨x, n⟩ := σ
  rcases x with s | ⟨_ | r, d⟩
  · exact h.elim
  · rename_i i
    cases i with
    | dp tm bw =>
      rcases d with d | ⟨_ | _, τ⟩
      · exact h.elim
      · cases τ with
        | sm d => exact h.elim
        | epi d =>
          rcases (h : d.site = .dealloc ∨ d.site = .exit) with h | h
          · left; show d.site.pc = 2851; rw [h]; rfl
          · right; show d.site.pc = 2855; rw [h]; rfl
      · exact h.elim
    | worker w =>
      cases d with
      | exit x =>
        obtain ⟨site, P⟩ := x
        have hs : site = .ret := h
        subst hs
        right; rfl
      | _ => exact h.elim
  · exact h.elim

/-- **A state after the last `bar.sync 0` has it before**: an earlier `bar.sync 0` without a
count, with at least two barrier-0 events before it. -/
theorem post_inv (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) :
    ∀ k, k < (X.tr g).length → ∀ σ, Frame.stateAt (thread Q L) X g k = some (some σ) →
      IsPost Q L g σ → ∃ jW < k, ∃ pcW, X.get (g, jW) = some ⟨pcW, .bar 0 none .sync⟩ ∧
        2 ≤ ((X.tr g).take jW).countP (Execution.isBarId 0) := by
  intro k
  induction k with
  | zero =>
    intro _ σ hσ hpo
    rw [Frame.stateAt_zero, thread_init_eq] at hσ
    obtain rfl := Option.some.inj (Option.some.inj hσ)
    exact hpo.elim
  | succ k ih =>
    intro hk σ' hσ' hpo
    have hlt : k < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    rw [Frame.stateAt_succ he] at hσ'
    have hF := good_all' hp hX hg k
    rcases hk0 : Frame.stateAt (thread Q L) X g k with _ | _ | σ
    · rw [hk0] at hσ'; cases hσ'
    · exact absurd hk0 hF.1
    · rw [hk0] at hσ'
      have hn : (thread Q L g).next σ e = some (some σ') := hσ'
      have hJ := hF.2 σ hk0
      rcases post_pred hJ hn hpo with h | h
      · obtain ⟨jW, hjW, rest⟩ := ih hlt σ hk0 h
        exact ⟨jW, by omega, rest⟩
      · obtain ⟨t, ins, o, hat, hi, hc, hf⟩ :=
          Frame.fired_site (fun g hg => thread_sound hp hg) hX (k := k) he hk0
        cases o with
        | none => exact absurd (fires_none_ends hf) (not_ends_of_lt hX hg he hk)
        | some u =>
          obtain ⟨pc, rfl⟩ := last_event hp hg hJ hat hi hc hf h
          have hC := c0_inv hp hX hg k hlt σ hk0
          obtain ⟨x, n⟩ := σ
          rcases x with s | y
          · exact h.elim
          · exact ⟨k, by omega, pc, he, hC⟩

/-- **A `bar.sync 0` without a count after two barrier-0 events is a last `bar.sync 0`.** -/
theorem last_of_b0n (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {g jZ pc : Nat} {md : BarMode} (he : X.get (g, jZ) = some ⟨pc, .bar 0 none md⟩)
    (h2 : 2 ≤ ((X.tr g).take jZ).countP (Execution.isBarId 0)) :
    ∃ σ, Frame.stateAt (thread Q L) X g jZ = some (some σ) ∧ IsLast Q L g σ := by
  have hg := Frame.lt_of_get hX he
  have hb : L.block = 256 := hp.block
  obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
  have hlen : jZ < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hC := c0_inv hp hX hg jZ hlen σ hσ
  have hpc := b0n_pc hc hf rfl (by omega)
  refine ⟨σ, hσ, ?_⟩
  obtain ⟨x, n⟩ := σ
  rcases x with st | ⟨_ | r, d⟩
  · have hC' : _ = startC0 st := hC
    rcases startup_b0n st.site hpc with hs | hs
    · have h0 : startC0 st = 0 := by unfold startC0; rw [hs]
      omega
    · have h1 : startC0 st = 1 := by unfold startC0; rw [hs]
      omega
  · rename_i i
    cases i with
    | dp tm bw =>
      rcases d with d | ⟨_ | _, τ⟩
      · exact (proA_b0n d.site hpc).elim
      · cases τ with
        | sm d => exact (sm_b0n d.site hpc).elim
        | epi d => exact epi_b0n d.site hpc
      · exact hJ.elim
    | worker w =>
      cases d with
      | worker w =>
        have hW := hJ.2.2.1.1
        rcases worker_b0n w.site hpc with hs | hs | hs <;> rw [hs] at hW <;> simp at hW
      | idle d => exact (idle_b0n d.site hpc).elim
      | loader d P => exact (loader_b0n d.site hpc).elim
      | mma d P => exact (mma_b0n d.site hpc).elim
      | exit x => exact exitsite_b0n x.site hpc
  · exact hJ.elim

/-- **Every position after a last `bar.sync 0` is at a state after it.** -/
theorem post_after (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {g jZ pc : Nat} {md : BarMode} (he : X.get (g, jZ) = some ⟨pc, .bar 0 none md⟩)
    (h2 : 2 ≤ ((X.tr g).take jZ).countP (Execution.isBarId 0)) :
    ∀ d, jZ + 1 + d < (X.tr g).length → ∀ σ,
      Frame.stateAt (thread Q L) X g (jZ + 1 + d) = some (some σ) → IsPost Q L g σ := by
  obtain ⟨σZ, hσZ, hlast⟩ := last_of_b0n hp hX he h2
  intro d
  induction d with
  | zero =>
    intro _ σ hσ
    have he' : (X.tr g)[jZ]? = some ⟨pc, .bar 0 none md⟩ := he
    rw [Nat.add_zero, Frame.stateAt_succ he', hσZ] at hσ
    exact post_next (.inr hlast) hσ
  | succ d ih =>
    intro hk σ hσ
    have hlt : jZ + 1 + d < (X.tr g).length := by omega
    obtain ⟨e, he'⟩ : ∃ e, (X.tr g)[jZ + 1 + d]? = some e :=
      ⟨_, List.getElem?_eq_getElem hlt⟩
    rw [show jZ + 1 + (d + 1) = jZ + 1 + d + 1 by omega, Frame.stateAt_succ he'] at hσ
    rcases hk0 : Frame.stateAt (thread Q L) X g (jZ + 1 + d) with _ | _ | σ0
    · rw [hk0] at hσ; cases hσ
    · rw [hk0] at hσ; cases hσ
    · rw [hk0] at hσ
      exact post_next (.inl (ih hlt σ0 hk0)) hσ

end
end PTX.Kernels.InklingRelDecode.Proof2
