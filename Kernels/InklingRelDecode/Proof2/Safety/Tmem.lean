-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.Table
public import Kernels.InklingRelDecode.Proof2.Lib.ResPcs
public import Kernels.InklingRelDecode.Proof2.Lib.TmemAlloc

@[expose] public section

/-! # The Tensor Memory allocation on the role table

`tmem1Facts`: the thread layer's part of the single-CTA allocation protocol
(`Proof2/Lib/TmemAlloc.lean`, `Tmem1Facts L X 0`), from the role table (`Safety/Table.lean`):

* every resource event is fired from the startup's allocation or relinquishment or from the
  epilogue's deallocation (`res_state`: the instruction is at a position of `resPcs`, and the
  states at those positions are these three, `Lib/ResPcs.lean`), of a thread of warp 0 (the
  startup's invariant; the epilogue's `%p3`, which is `tid < 32`);
* a thread's resource operations before a state's event are `resN` of the state (`tm_inv`: 0 at
  the allocation, 1 up to the relinquishment, 2 after it, 3 at the epilogue's return of warp 0,
  none for the other warps), so the `n`-th has the shape `n`;
* the deallocation frees column 0: the epilogue's base word is the startup's recorded word 0,
  which the softmax states carry in their entry numbers (`TmS`);
* a lane of warp 0 exits only at the epilogue's return (the worker exit path's return is a worker
  state, `TmS`), after its three operations.

`tm_inv` is an induction on the positions of a thread's trace: it reads only the states the role
table follows (`good_all'`) and the shapes of the events (`frag_ev`); no other thread is used.
With `Tmem1.no_resource_unsafe` and `Tmem1.no_release_unsafe` this discharges the classes
`Tmem.Pair.ResourceUnsafe` and `Tmem.Pair.ReleaseUnsafe` (`no_resource_unsafe`,
`no_release_unsafe`). -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame Tmem.Pair

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-! ### The count and the carried words -/

/-- The resource operations a thread has made before the event of a startup state. -/
def startN (L : Launch) (g : Nat) (s : Startup.D) : Nat :=
  match s.site with
  | .alloc => 0
  | .allocWr | .bar0 | .ld0 | .bar1 | .relinq => if g % L.block < 32 then 1 else 0
  | .shfl | .enter _ => if g % L.block < 32 then 2 else 0

/-- **The resource operations a thread has made before the event of a state**: the startup's by
site, 3 at the epilogue's return of warp 0, else 2 for warp 0 and none for the other warps. -/
def resN (Q : Params) (L : Launch) (g : Nat) : (thread Q L g).D → Nat
  | (.inl s, _) => startN L g s
  | (.inr ⟨.inl (.dp _ _), .inr ⟨.inl _, .epi d⟩⟩, _) =>
    if g % L.block < 32 then (if d.site = .exit then 3 else 2) else 0
  | _ => if g % L.block < 32 then 2 else 0

/-- **The words a state carries**: the softmax states' recorded base word 0, the epilogue's base
word 0 and its `%p3` (`tid < 32`), and a worker's warp (4 and above). -/
def TmS (Q : Params) (L : Launch) (g : Nat) : (thread Q L g).D → Prop
  | (.inr ⟨.inl (.dp _ _), .inr ⟨.inl _, .sm d⟩⟩, _) => d.e.tm = 0
  | (.inr ⟨.inl (.dp _ _), .inr ⟨.inl _, .epi d⟩⟩, _) =>
    d.pr.tm = 0 ∧ d.pr.p3 = decide (g % L.block < 32)
  | (.inr ⟨.inl (.worker _), _⟩, _) => 4 ≤ g % L.block / 32
  | _ => True

theorem tmemOps_snoc (l : List Event) (e : Event) :
    tmemOps (l ++ [e]) = tmemOps l + if isTmemOp e then 1 else 0 := by
  simp only [tmemOps, List.countP_append, List.countP_singleton]

theorem isTmemOp_kind {e : Event} (h : isTmemOp e = true) :
    ∃ grp dst act, e.kind = .tc (.resource grp dst act) := by
  obtain ⟨pc, k⟩ := e
  cases k <;> simp [isTmemOp] at h
  rename_i op
  cases op <;> simp at h
  exact ⟨_, _, _, rfl⟩

/-- An event of an instruction at no special position is no resource operation. -/
theorem tmem_false {pc : Nat} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o) (hpc : pc ∉ resPcs) :
    isTmemOp e = false := by
  cases h : isTmemOp e with
  | false => rfl
  | true =>
    obtain ⟨grp, dst, act, hk⟩ := isTmemOp_kind h
    exact absurd (res_pc' hc hf hk) hpc

/-- The epilogue's step keeps its base word and its `%p3`. -/
theorem epi_next_pr {d d' : Proof.Epi.D} {e : Event} (h : Proof.Epi.next d e = some (some d')) :
    d'.pr.tm = d.pr.tm ∧ d'.pr.p3 = d.pr.p3 := by
  unfold Proof.Epi.next at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at h; done)
    | (simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩)
    | (simp only [Option.some.injEq] at h; subst h; simp only [Proof.Epi.stNext]; split <;>
        exact ⟨rfl, rfl⟩)

/-- The epilogue's count for warp 0: the step adds the deallocation. -/
theorem epi_next_cnt {d d' : Proof.Epi.D} {e : Event} (hp : d.pr.p3 = true)
    (h : Proof.Epi.next d e = some (some d')) :
    (if d'.site = .exit then 3 else 2) =
      (if d.site = .exit then 3 else 2) + (if d.site = .dealloc then 1 else 0) := by
  unfold Proof.Epi.next at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at h; done)
    | (simp only [Option.some.injEq] at h; subst h
       simp_all [Proof.Epi.D.stores, Proof.Epi.stNext]
       done)
    | (simp only [Option.some.injEq] at h; subst h
       simp_all [Proof.Epi.D.stores, Proof.Epi.stNext]
       split_ifs <;> simp_all)

/-- The epilogue of another warp never reaches its return through a deallocation. -/
theorem epi_next_exit {d d' : Proof.Epi.D} {e : Event} (hd : d.site ≠ .dealloc)
    (h : Proof.Epi.next d e = some (some d')) :
    (if d'.site = .exit then 3 else 2) = (if d.site = .exit then 3 else 2) ∨
      (d.site = .bar3 ∧ d.pr.p3 = false) := by
  unfold Proof.Epi.next at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at h; done)
    | (simp only [Option.some.injEq] at h; subst h
       simp_all [Proof.Epi.D.stores, Proof.Epi.stNext]
       done)
    | (simp only [Option.some.injEq] at h; subst h
       simp_all [Proof.Epi.D.stores, Proof.Epi.stNext]
       split_ifs <;> simp_all)


/-! ### The step -/

theorem mm_some {α β : Type} {x : Option (Option α)} {f : α → β} {y : β}
    (h : x.map (Option.map f) = some (some y)) : ∃ a, x = some (some a) ∧ f a = y := by
  rcases x with _ | _ | a
  · simp at h
  · simp at h
  · exact ⟨a, rfl, by simpa using h⟩

/-- A site of the startup at a resource position is the allocation or the relinquishment. -/
theorem start_res {s : Startup.Site} (h : s.pc ∈ resPcs) :
    s = .alloc ∨ s = .allocWr ∨ s = .relinq := by
  have := startup_special s (List.mem_append_left _ h)
  simpa using this

/-- A role's first state counts as the startup's last. -/
theorem entry_res (j : Role ⊕ Startup.Entry) (n : Cls → Nat) :
    resN Q L g (.inr ⟨j, (Code.withStubs (frag Q L g) Startup.Entry.pc j).init⟩, n) =
      if g % L.block < 32 then 2 else 0 := by
  rcases j with (_ | _) | _ <;> rfl

/-- A role's first state carries a worker's warp when it is a worker's. -/
theorem entry_tms (j : Role ⊕ Startup.Entry) (n : Cls → Nat)
    (h : ∀ w, j = .inl (.worker w) → 4 ≤ g % L.block / 32) :
    TmS Q L g (.inr ⟨j, (Code.withStubs (frag Q L g) Startup.Entry.pc j).init⟩, n) := by
  rcases j with (_ | w) | _
  · trivial
  · exact h w rfl
  · trivial

/-- **A continuing step adds the event's resource operation to the count and keeps the carried
words.** -/
theorem tm_step (hp : Pre Q L m) (hg : g < L.threads) {σ σ' : (thread Q L g).D} {e : Event}
    {t u : TState} {ins : Instr} (hJ : Ref Q L g σ) (hat : (thread Q L g).AtD σ t)
    (hi : (thread Q L g).inv σ) (hc : kernel.code[(thread Q L g).pc σ]? = some ins)
    (hf : Fires ((thread Q L g).pc σ) (eventTmpl Assumptions.all L g t ins.op) e (some u))
    (hS : TmS Q L g σ) (hn : (thread Q L g).next σ e = some (some σ')) :
    resN Q L g σ' = resN Q L g σ + (if isTmemOp e then 1 else 0) ∧ TmS Q L g σ' := by
  have hev := frag_ev hp hg hJ hat hi hc hf
  obtain ⟨x, n⟩ := σ
  rcases x with s | ⟨_ | r, d⟩
  · -- the startup
    rw [next_start] at hn
    obtain ⟨s', hs', rfl⟩ := mm_some hn
    have hI : Startup.Inv L g s := hi.1
    obtain ⟨site, tm, x, w⟩ := s
    cases site with
    | alloc =>
      have hw0 : g % L.block < 32 := hI (.inl rfl)
      have he : e = _ := hev
      subst he
      have hs2 : s'.site = .allocWr ∨ s'.site = .bar0 := by
        simp only [Startup.succ, Option.some.injEq] at hs'
        split at hs' <;> (subst hs'; simp)
      have hx : Startup.enterOf s' = none := by
        rcases hs2 with h | h <;> simp [Startup.enterOf, h]
      rw [enter_inl hx]
      refine ⟨?_, trivial⟩
      rcases hs2 with h | h <;> simp [resN, startN, h, hw0, isTmemOp]
    | relinq =>
      have hw0 : g % L.block < 32 := hI (.inr (.inr rfl))
      have he : e = _ := hev
      subst he
      simp only [Startup.succ, Option.some.injEq] at hs'
      subst hs'
      rw [enter_inl (by simp [Startup.enterOf])]
      exact ⟨by simp [resN, startN, hw0, isTmemOp], trivial⟩
    | allocWr =>
      obtain ⟨col, -, he⟩ := (hev : ∃ col, _ ∧ _)
      subst he
      simp only [Startup.succ, Option.some.injEq] at hs'
      subst hs'
      rw [enter_inl (by simp [Startup.enterOf])]
      exact ⟨by simp [resN, startN, isTmemOp], trivial⟩
    | bar0 =>
      have he : e = _ := hev
      subst he
      simp only [Startup.succ, Option.some.injEq] at hs'
      subst hs'
      rw [enter_inl (by simp [Startup.enterOf])]
      exact ⟨by simp [resN, startN, isTmemOp], trivial⟩
    | ld0 =>
      obtain ⟨ac, bs, he, -⟩ := (hev : ∃ ac bs, _ ∧ _)
      subst he
      have hs2 : s'.site = .bar1 := by
        simp only [Startup.succ] at hs'
        repeat' split at hs'
        all_goals first
          | (simp only [Option.some.injEq, reduceCtorEq] at hs'; done)
          | (simp only [Option.some.injEq] at hs'; subst hs'; rfl)
      rw [enter_inl (by simp [Startup.enterOf, hs2])]
      exact ⟨by simp [resN, startN, hs2, isTmemOp], trivial⟩
    | bar1 =>
      have he : e = _ := hev
      subst he
      simp only [Startup.succ, Option.some.injEq] at hs'
      by_cases hw0 : g % L.block < 32
      · simp only [hw0, ↓reduceIte] at hs'
        subst hs'
        rw [enter_inl (by simp [Startup.enterOf])]
        exact ⟨by simp [resN, startN, isTmemOp, hw0], trivial⟩
      · simp only [hw0, ↓reduceIte] at hs'
        subst hs'
        rw [enter_inl (by simp [Startup.enterOf])]
        exact ⟨by simp [resN, startN, isTmemOp, hw0], trivial⟩
    | shfl =>
      have hev' : Startup.Ev L g ⟨.shfl, tm, x, w⟩ e := hev
      simp only [Startup.Ev] at hev'
      obtain ⟨recv, ok, he⟩ := hev'
      subst he
      simp only [Startup.succ] at hs'
      split at hs'
      · rename_i _ x'
        simp only [Option.some.injEq] at hs'
        subst hs'
        simp only [isTmemOp, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        simp only [Code.enter, Code.gatedExit, Startup.enterOf, Option.map_some]
        refine ⟨by rw [entry_res]; simp [resN, startN], entry_tms _ _ fun w' hj => ?_⟩
        cases hr : Startup.entryOf x' with
        | dp =>
          rw [hr] at hj
          simp only [sel] at hj
          split_ifs at hj
          simp at hj
        | worker =>
          rw [hr] at hj
          simp only [sel] at hj
          split_ifs at hj with hG
          · simp only [WGate, Bool.and_eq_true, decide_eq_true_eq] at hG
            exact hG.2
      · simp at hs'
    | enter r => exact hJ.elim
  · rename_i i
    cases i with
    | dp tm bw =>
      rcases d with d | ⟨_ | _, τ⟩
      · -- the prologue
        have hflag : isTmemOp e = false := tmem_false hc hf (fun h =>
          proA_special d.site (List.mem_append_left _ h))
        simp only [hflag, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        rw [next_pro] at hn
        obtain ⟨d', -, rfl⟩ := mm_some hn
        cases hxo : ProA.exitOf d' with
        | none =>
          rw [Code.enter_none (by simp [Code.gatedExit, hxo])]
          exact ⟨rfl, trivial⟩
        | some v =>
          cases hsel : ProA.selTail Q L g v d' with
          | some dt =>
            rw [Code.enter_some (i := Sum.inl dt) (by simp [Code.gatedExit, hxo, hsel])]
            refine ⟨rfl, ?_⟩
            have hG : TailGate Q L g d'.dt ∧ d'.dt = dt := by
              simp only [ProA.selTail] at hsel
              split at hsel
              · exact ⟨‹_›, Option.some.inj hsel⟩
              · cases hsel
            obtain ⟨hG, rfl⟩ := hG
            show (Proof.SmEntry.entOf Q L g d'.dt).tm = 0
            simp only [Proof.SmEntry.entOf, hG.1]
            rfl
          | none =>
            rw [Code.enter_some (i := Sum.inr ()) (by simp [Code.gatedExit, hxo, hsel])]
            exact ⟨rfl, trivial⟩
      · -- the softmax–epilogue fragment
        rw [next_tail] at hn
        obtain ⟨τ', hτ, rfl⟩ := mm_some hn
        cases τ with
        | sm d =>
          have hflag : isTmemOp e = false := tmem_false hc hf (fun h => by
            simpa using sm_special d.site (List.mem_append_left _ h))
          simp only [hflag, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
          have hS' : d.e.tm = 0 := hS
          simp only [Tail.next] at hτ
          split at hτ
          · simp only [Tail.exitNext] at hτ
            split at hτ
            · simp only [Option.some.injEq] at hτ
              subst hτ
              refine ⟨by simp [resN, Proof.Epi.D.entry], ?_⟩
              show (Proof.Br.prm (Proof.DComp.exitIn L g d)).tm = 0 ∧
                (Proof.Br.prm (Proof.DComp.exitIn L g d)).p3 = decide (g % L.block < 32)
              simp [Proof.Br.prm, Proof.DComp.exitIn, hS']
            · cases hτ
          · obtain ⟨d', hd', rfl⟩ := mm_some hτ
            refine ⟨rfl, ?_⟩
            show d'.e.tm = 0
            rw [sm_next_e hd']
            exact hS'
        | epi d =>
          obtain ⟨htm, hp3⟩ := (hS : d.pr.tm = 0 ∧ d.pr.p3 = decide (g % L.block < 32))
          simp only [Tail.next] at hτ
          obtain ⟨d', hd', rfl⟩ := mm_some hτ
          obtain ⟨htm', hp3'⟩ := epi_next_pr hd'
          refine ⟨?_, ⟨htm'.trans htm, hp3'.trans hp3⟩⟩
          have hinv : Proof.Epi.Inv d := hi.1
          have hflag : isTmemOp e = if d.site = .dealloc then true else false := by
            by_cases hs : d.site = .dealloc
            · simp only [hs, ↓reduceIte]
              have he := hev
              simp only [FragEv, Proof.Epi.Shape, hs] at he
              rw [he]; rfl
            · simp only [hs, ↓reduceIte]
              refine tmem_false hc hf (fun h => ?_)
              have := epi_special d.site (List.mem_append_left _ h)
              simp only [List.mem_cons, List.not_mem_nil, or_false] at this
              rcases this with h' | h'
              · exact hs h'
              · simp [Proof.Epi.next, h'] at hd'
          by_cases hw0 : g % L.block < 32
          · have hp : d.pr.p3 = true := by rw [hp3]; simpa using hw0
            have := epi_next_cnt hp hd'
            simp only [resN, hw0, ↓reduceIte, hflag]
            rw [this]
            split <;> simp
          · have hnd : d.site ≠ .dealloc := fun h => by
              have := hinv.dealloc h
              rw [hp3] at this
              simp [hw0] at this
            simp only [resN, hw0, ↓reduceIte, hflag, hnd]
            rfl
      · exact hJ.elim
    | worker w =>
      have hw4 : 4 ≤ g % L.block / 32 := hS
      have hflag : isTmemOp e = false := tmem_false hc hf (fun h => by
        obtain ⟨P, hP⟩ := worker_state_special d (List.mem_append_left _ h)
        subst hP
        exact absurd h (show Proof.WComp.ExitSite.pc .ret ∉ resPcs by decide))
      simp only [hflag, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      rw [next_worker] at hn
      obtain ⟨d', -, rfl⟩ := mm_some hn
      exact ⟨rfl, hw4⟩
  · exact hJ.elim


/-! ### The count along a thread -/

/-- An event before the last of its thread continues it. -/
theorem not_ends_of_lt (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads)
    {k : Nat} {e : Event} (he : (X.tr g)[k]? = some e) (hk : k + 1 < (X.tr g).length) :
    ¬ Ends e := by
  intro hE
  obtain ⟨r, hr⟩ := hX.thr g hg
  have := Flow.Run.end_last hr he hE
  omega

theorem thread_init_eq : (thread Q L g).init = (.inl (Startup.init L g), fun _ => 0) := by
  show (Code.enter (Startup.code Q L g) (Code.withStubs (frag Q L g) Startup.Entry.pc)
    (Code.gatedExit Startup.enterOf (sel L g)) (Startup.init L g), fun _ => 0) = _
  rw [enter_inl enterOf_init]

/-- **The count and the carried words along a thread**: at every position of the trace, the
thread's resource operations before it are `resN` of its state, which carries `TmS`. -/
theorem tm_inv (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) :
    ∀ k, k < (X.tr g).length → ∀ σ, Frame.stateAt (thread Q L) X g k = some (some σ) →
      tmemOps ((X.tr g).take k) = resN Q L g σ ∧ TmS Q L g σ := by
  intro k
  induction k with
  | zero =>
    intro _ σ hσ
    rw [Frame.stateAt_zero, thread_init_eq] at hσ
    obtain rfl := Option.some.inj (Option.some.inj hσ)
    refine ⟨?_, trivial⟩
    by_cases hw : g % L.block < 32 <;>
      simp [tmemOps, resN, startN, Startup.init, hw]
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
      obtain ⟨hc0, hS0⟩ := ih hlt σ hk0
      have hJ := hF.2 σ hk0
      obtain ⟨t, ins, o, hat, hi, hc, hf⟩ :=
        Frame.fired_site (fun g hg => thread_sound hp hg) hX (k := k) he hk0
      cases o with
      | none => exact absurd (fires_none_ends hf) (not_ends_of_lt hX hg he hk)
      | some u =>
        obtain ⟨h1, h2⟩ := tm_step hp hg hJ hat hi hc hf hS0 hn
        refine ⟨?_, h2⟩
        rw [List.take_add_one, he, Option.toList_some, tmemOps_snoc, hc0, h1]

/-! ### The resource events -/

/-- **A resource event is the startup's allocation or relinquishment or the epilogue's
deallocation, of a thread of warp 0, in group one.** -/
theorem res_class (hp : Pre Q L m) (hg : g < L.threads) {σ : (thread Q L g).D} {e : Event}
    {t u : TState} {ins : Instr} (hJ : Ref Q L g σ) (hat : (thread Q L g).AtD σ t)
    (hi : (thread Q L g).inv σ) (hc : kernel.code[(thread Q L g).pc σ]? = some ins)
    (hf : Fires ((thread Q L g).pc σ) (eventTmpl Assumptions.all L g t ins.op) e (some u))
    (hS : TmS Q L g σ) {grp : CtaGroup} {dst : Option Loc} {act : Tmem.Request}
    (hk : e.kind = .tc (.resource grp dst act)) :
    g % L.block < 32 ∧ grp = .one ∧
      ((∃ s n, σ = (.inl s, n) ∧ s.site = .alloc ∧ act = .alloc 512) ∨
       (∃ s n, σ = (.inl s, n) ∧ s.site = .relinq ∧ act = .relinquish) ∨
       (∃ tm bw dt d n, σ = (.inr ⟨.inl (.dp tm bw), .inr ⟨.inl dt, .epi d⟩⟩, n) ∧
          d.site = .dealloc ∧ act = .dealloc d.pr.tm 512)) := by
  have hev := frag_ev hp hg hJ hat hi hc hf
  have hpc := res_pc' hc hf hk
  obtain ⟨x, n⟩ := σ
  rcases x with s | ⟨_ | r, d⟩
  · have hI : Startup.Inv L g s := hi.1
    obtain ⟨site, tm, x, w⟩ := s
    rcases start_res hpc with h | h | h <;> simp only at h <;> subst h
    · have he : e = _ := hev
      subst he
      simp only [Kind.tc.injEq, TcKind.resource.injEq] at hk
      exact ⟨hI (.inl rfl), hk.1.symm, .inl ⟨_, n, rfl, rfl, hk.2.2.symm⟩⟩
    · obtain ⟨col, -, he⟩ := (hev : ∃ col, _ ∧ _)
      subst he
      cases hk
    · have he : e = _ := hev
      subst he
      simp only [Kind.tc.injEq, TcKind.resource.injEq] at hk
      exact ⟨hI (.inr (.inr rfl)), hk.1.symm, .inr (.inl ⟨_, n, rfl, rfl, hk.2.2.symm⟩)⟩
  · rename_i i
    cases i with
    | dp tm bw =>
      rcases d with d | ⟨_ | _, τ⟩
      · exact absurd (List.mem_append_left _ hpc) (proA_special d.site)
      · cases τ with
        | sm d => simpa using sm_special d.site (List.mem_append_left _ hpc)
        | epi d =>
          have hm := epi_special d.site (List.mem_append_left _ hpc)
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
          rcases hm with hs | hs
          · have he := hev
            simp only [FragEv, Proof.Epi.Shape, hs] at he
            subst he
            simp only [Kind.tc.injEq, TcKind.resource.injEq] at hk
            have hinv : Proof.Epi.Inv d := hi.1
            have hp3 := hinv.dealloc hs
            obtain ⟨-, hp3'⟩ := (hS : d.pr.tm = 0 ∧ d.pr.p3 = decide (g % L.block < 32))
            rw [hp3'] at hp3
            exact ⟨by simpa using hp3, hk.1.symm,
              .inr (.inr ⟨tm, bw, _, d, n, rfl, hs, hk.2.2.symm⟩)⟩
          · have he := hev
            simp only [FragEv, Proof.Epi.Shape, hs] at he
      · exact hJ.elim
    | worker w =>
      obtain ⟨P, hP⟩ := worker_state_special d (List.mem_append_left _ hpc)
      subst hP
      exact absurd hpc (show Proof.WComp.ExitSite.pc .ret ∉ resPcs by decide)
  · exact hJ.elim

/-- The followed state of an event, with the event fired from it. -/
theorem ev_state (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {e : Event} (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f) :
    ∃ σ t ins o, Frame.stateAt (thread Q L) X g k = some (some σ) ∧ Ref Q L g σ ∧
      (thread Q L g).AtD σ t ∧ (thread Q L g).inv σ ∧
      kernel.code[(thread Q L g).pc σ]? = some ins ∧
      Fires ((thread Q L g).pc σ) (eventTmpl Assumptions.all L g t ins.op) e o := by
  have hg := Frame.lt_of_get hX he
  have hC : ∀ g < L.threads, (thread Q L g).Sound := fun g hg => thread_sound hp hg
  have hF := good_all' hp hX hg k
  rcases Frame.fired hC hX he with ⟨σo, o, hσ, -⟩ | ⟨-, pc, f, rfl⟩
  · rcases σo with _ | σ
    · exact absurd hσ hF.1
    · obtain ⟨t, ins, o, hat, hi, hc, hf⟩ := Frame.fired_site hC hX he hσ
      exact ⟨σ, t, ins, o, hσ, hF.2 σ hσ, hat, hi, hc, hf⟩
  · exact absurd rfl (hub f)

/-- **`Tmem1Facts L X 0` from the role table.** -/
theorem tmem1Facts (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) :
    Proof.Tmem1.Tmem1Facts L X 0 where
  warp_lt := by have := hp.block; omega
  event := by
    intro g k pc grp dst act hg he
    obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
    have hlen : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
    obtain ⟨hcnt, hS⟩ := tm_inv hp hX hg k hlen σ hσ
    cases o with
    | none => exact absurd (fires_none_ends hf) (by simp [Ends])
    | some u =>
      obtain ⟨hw0, hgrp, hcl⟩ := res_class hp hg hJ hat hi hc hf hS rfl
      refine ⟨by omega, hgrp, ?_⟩
      rw [hcnt]
      rcases hcl with ⟨s, n, rfl, hs, rfl⟩ | ⟨s, n, rfl, hs, rfl⟩ |
        ⟨tm, bw, dt, d, n, rfl, hs, rfl⟩
      · simp [resN, startN, hs, TmemShape]
      · simp [resN, startN, hs, hw0, TmemShape]
      · simp [resN, hs, hw0, TmemShape]
  dealloc := by
    intro g k pc grp dst a n hg he
    obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
    have hlen : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
    obtain ⟨-, hS⟩ := tm_inv hp hX hg k hlen σ hσ
    cases o with
    | none => exact absurd (fires_none_ends hf) (by simp [Ends])
    | some u =>
      obtain ⟨-, -, hcl⟩ := res_class hp hg hJ hat hi hc hf hS rfl
      rcases hcl with ⟨s, n', rfl, hs, h⟩ | ⟨s, n', rfl, hs, h⟩ |
        ⟨tm, bw, dt, d, n', rfl, hs, h⟩
      · cases h
      · cases h
      · simp only [Tmem.Request.dealloc.injEq] at h
        rw [h.1]
        exact (hS : d.pr.tm = 0 ∧ _).1
  exit := by
    intro g k pc hg hw he
    obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
    have hlen : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
    obtain ⟨hcnt, hS⟩ := tm_inv hp hX hg k hlen σ hσ
    have hpc := ret_pc' hc hf rfl
    have hw0 : g % L.block < 32 := by omega
    rw [hcnt]
    obtain ⟨x, n⟩ := σ
    rcases x with s | ⟨_ | r, d⟩
    · have hm := startup_special s.site (List.mem_append_right _ hpc)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h <;> rw [show (thread Q L g).pc _ = s.site.pc from rfl, h] at hpc <;>
        simp [retPcs, Startup.Site.pc] at hpc
    · rename_i i
      cases i with
      | dp tm bw =>
        rcases d with d | ⟨_ | _, τ⟩
        · exact absurd (List.mem_append_right _ hpc) (proA_special d.site)
        · cases τ with
          | sm d => simpa using sm_special d.site (List.mem_append_right _ hpc)
          | epi d =>
            have hm := epi_special d.site (List.mem_append_right _ hpc)
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
            rcases hm with hs | hs
            · rw [show (thread Q L g).pc _ = d.site.pc from rfl, hs] at hpc
              simp [retPcs, Proof.Epi.Site.pc] at hpc
            · simp [resN, hs, hw0]
        · exact hJ.elim
      | worker w =>
        have : 4 ≤ g % L.block / 32 := hS
        omega
    · exact hJ.elim

/-- **ERR-TMEM-ALLOC for the allocator's requests** (`Tmem.Pair.ResourceUnsafe`): every request
of the execution is legal. -/
theorem no_resource_unsafe (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) :
    ¬ Tmem.Pair.ResourceUnsafe L X :=
  Proof.Tmem1.no_resource_unsafe hX (tmem1Facts hp hX)

/-- **No allocation is live at the end** (`Tmem.Pair.ReleaseUnsafe`). -/
theorem no_release_unsafe (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) :
    ¬ Tmem.Pair.ReleaseUnsafe L X :=
  Proof.Tmem1.no_release_unsafe hX (tmem1Facts hp hX)

end
end PTX.Kernels.InklingRelDecode.Proof2
