-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.Origin
public import Lemmas.Flow.NotShfl

@[expose] public section

/-! # The shuffles of a thread along its run

A thread's shuffles before each state of its machine are a function of the state (`shfls`): the
prologue's four broadcasts (`Prologue.Site.shfls`), then the loader's rank broadcast at each
item's head (`Loader.shfls`, the item count after the last item), or the MMA warp's Q-descriptor
broadcast and the fourteen constant broadcasts of each item (`Mma.shA`, `6 n + 2` per item, in
the count formulas of `MmaCountsGen.lean`); the other roles broadcast nothing. Every shuffle is
at a shuffle site (`kernel_shfl_pcs`), and a step from a shuffle site is a shuffle, so the count
of the thread's shuffles is the state's (`shflJ_run`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The positions of the shuffles. -/
abbrev shflPcs : List Nat := Flow.shfl.toList

/-- Every shuffle of the kernel is listed. -/
theorem kernel_shfl_pcs : OpPcsFast kernel.code Op.isShfl shflPcs = true := by
  decide +kernel

/-! ### The prologue -/

namespace Prologue

/-- The prologue's shuffle sites. -/
def Site.isShfl : Site → Bool
  | .shfl0 | .shfl1 | .shfl2 | .shfl3 => true
  | _ => false

/-- The prologue's shuffles before a site: warp 0's first two election groups come before the
rank broadcast. -/
def Site.shfls : Site → Nat
  | .shfl0 => 0 | .shfl1 => 1 | .shfl2 => 2
  | .elect12 | .init320 | .fence0 | .shfl3 => 3
  | .elect e => if e.val < 2 then 3 else 4
  | .init j => if (groupOf j).val < 2 then 3 else 4
  | .fence1 | .clArrive | .clWait => 4

theorem site_shfl_pc (s : Site) (h : s.isShfl = false) : s.pc ∉ shflPcs := by
  cases s <;> simp only [Site.isShfl, reduceCtorEq] at h <;> site_decide

theorem shfls_elect : ∀ k : Fin 14, (afterGroup k).shfls = (Site.elect k).shfls ∧
    (Site.init (groupStart k)).shfls = (Site.elect k).shfls := by decide

theorem shfls_init : ∀ j : Fin 36, (initNext j).shfls = (Site.init j).shfls := by decide

variable {L : Launch} {g : Nat} {p : D} {e : Event}

/-- A prologue step moves the count by the site's shuffle; the hand-off is after all four. -/
theorem shfls_next {x : D ⊕ RoleKind} (hn : next L g p e = some (some x)) :
    (match x with
      | .inl p' => p'.site.shfls
      | .inr _ => 4) = p.site.shfls + if p.site.isShfl then 1 else 0 := by
  obtain ⟨s⟩ := p
  cases s <;> simp only [next] at hn
  all_goals (repeat' split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hn)
  all_goals (try subst hn)
  all_goals (try split_ifs)
  all_goals first
    | (simp only [Nat.add_zero, (shfls_elect _).1, (shfls_elect _).2, shfls_init]; done)
    | simp_all [Site.shfls, Site.isShfl]

/-- At a prologue shuffle site the continuing event is a shuffle. -/
theorem next_shfl (hs : p.site.isShfl = true) {x} (hn : next L g p e = some (some x)) :
    Execution.isShfl e = true := by
  obtain ⟨s⟩ := p
  obtain ⟨pc, k⟩ := e
  cases s <;> simp only [Site.isShfl, reduceCtorEq] at hs <;> simp only [next] at hn <;>
    cases k <;> simp_all [Execution.isShfl]

end Prologue

/-! ### The loader -/

namespace Loader
open Work

/-- The loader's shuffles before a state: one per item head passed, the item count after the
last item. -/
def shfls (L : Launch) (g : Nat) (d : D) : Nat :=
  match d.site with
  | .setMaxReg => 0
  | .head => d.i
  | .drain _ | .drainQ | .elTail | .arriveTail | .exit => T L g
  | _ => d.i + 1

theorem site_shfl_pc (s : Site) (h : s ≠ .head) : s.pc ∉ shflPcs := by
  cases s <;> simp only [ne_eq, not_true_eq_false] at h <;> site_decide

variable {L : Launch} {g : Nat} {d d' : D} {e : Event}

theorem shfls_itemEnd (h : d.i < T L g) : shfls L g (afterUse.itemEndOf L g d) = d.i + 1 := by
  unfold afterUse.itemEndOf
  split_ifs with h1
  · simp [shfls]
  · simp [shfls]; omega

theorem shfls_afterUse (u : UseK) (h : d.i < T L g) : shfls L g (afterUse L g d u) = d.i + 1 := by
  cases u <;> simp only [afterUse]
  all_goals (try split_ifs)
  all_goals first | (simp [shfls]; done) | exact shfls_itemEnd h

theorem shfls_afterCopy (u : UseK) (j : Fin 2) (h : d.i < T L g) :
    shfls L g (afterCopy L g d u j) = d.i + 1 := by
  unfold afterCopy
  split_ifs
  · simp [shfls]
  · exact shfls_afterUse u h

/-- A loader step moves the count by the head's broadcast. -/
theorem shfls_next (hi : Inv L g d) (hn : next L g d e = some (some d')) :
    shfls L g d' = shfls L g d + if d.site = .head then 1 else 0 := by
  obtain ⟨s, i, t, ks, ph, qp⟩ := d
  have hT : s.inItem = true → i < T L g := hi.item
  cases s <;> simp only [next] at hn
  all_goals (repeat' split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hn)
  all_goals (try subst hn)
  all_goals (try split_ifs)
  all_goals first
    | (simp_all; done)
    | (rw [shfls_afterCopy _ _ (hT rfl)]; simp [shfls])
    | simp_all [shfls]

/-- At the head the continuing event is a shuffle. -/
theorem next_shfl (hs : d.site = .head) (hn : next L g d e = some (some d')) :
    Execution.isShfl e = true := by
  obtain ⟨s, i, t, ks, ph, qp⟩ := d
  obtain ⟨pc, k⟩ := e
  simp only at hs
  subst hs
  simp only [next] at hn
  cases k <;> simp_all [Execution.isShfl]

end Loader


/-! ### The MMA warp -/

namespace Mma

/-- The MMA warp's shuffle sites: the Q descriptor's broadcast and the constant broadcasts. -/
def Site.isShfl : Site → Bool
  | .shflQ | .shfl _ => true
  | _ => false

/-- The shuffles before a site, without the `6 t` of the trips done: the Q descriptor's, then
an item's three before the loop, a trip's six and the five after the loop, by their item
positions (`Site.ord`). -/
def shA (s : Site) : Nat :=
  (if s.phase = 0 then 0 else 1) + s.after 3 + s.after 4 + s.after 10 + s.inTrip 102 +
    s.inTrip 103 + s.inTrip 104 + s.inTrip 110 + s.inTrip 116 + s.inTrip 117 + s.after 206 +
    s.after 207 + s.after 208 + s.after 216 + s.after 217

/-- A shuffle site's event. -/
def shflEv (s : Site) (_ : Bool) : Bool := s.isShfl

theorem check_shfl : check shA 6 2 shflEv allValid = true := by decide +kernel

/-- The MMA warp's shuffles before a state. -/
def shfls (L : Launch) (d : D) : Nat := cnt L shA 6 2 d

theorem site_shfl_pc (s : Site) (h : s.isShfl = false) : s.pc ∉ shflPcs := by
  cases s <;> simp only [Site.isShfl, reduceCtorEq] at h <;> site_decide

variable {L : Launch} {g : Nat} {d d' : D} {e : Event}

theorem shfls_start (L : Launch) (b : Value) (pro : Nat → Value) :
    shfls L ⟨.setMaxReg, 0, 0, b, pro⟩ = 0 := by
  simp [shfls, cnt, shA, Site.after, Site.inTrip, Site.ord, Site.phase, Site.loop]

/-- An MMA step moves the count by the site's broadcast. -/
theorem shfls_next (hi : Inv L g d) (hp : d.site.phase = 0 → d.i = 0)
    (hn : next L g d e = some (some d')) :
    shfls L d' = shfls L d + if d.site.isShfl then 1 else 0 :=
  cnt_next check_shfl hi hp hn rfl

/-- At a shuffle site the continuing event is a shuffle. -/
theorem next_shfl (hs : d.site.isShfl = true) (hn : next L g d e = some (some d')) :
    Execution.isShfl e = true := by
  obtain ⟨s, i, t, base, pro⟩ := d
  obtain ⟨pc, k⟩ := e
  cases s <;> simp only [Site.isShfl, reduceCtorEq] at hs <;> simp only [next] at hn <;>
    cases k <;> simp_all [Execution.isShfl]

/-- After the items, on the leader CTA every item of the cluster is done. -/
def EndOk (L : Launch) (g : Nat) (d : D) : Prop :=
  d.site.phase = 2 → rank L g = 0 → totOf L ≤ work L g d.i

theorem phase_next : (∀ k, (kvNext k).phase = 1) ∧ (∀ k, (pNext k).phase = 1) ∧
    (∀ k, (shflNext k).phase = 1) ∧ (∀ k b, (p2Next k b).phase = 1) ∧
    (∀ b j, (mmaNext b j).phase = 1) ∧ (∀ b, (skipGrp b).phase = 1) := by decide

theorem afterCommit_end (c : Fin 12) (h : (afterCommit L g d c).site.phase = 2) :
    (afterCommit L g d c).i = d.i + 1 ∧ ¬ work L g (d.i + 1) < totOf L := by
  fin_cases c <;> simp only [afterCommit] at h ⊢ <;> (try split_ifs at h ⊢) <;>
    simp_all [Site.phase]

theorem endOk_next (h : EndOk L g d) (hn : next L g d e = some (some d')) : EndOk L g d' := by
  intro hp hr
  obtain ⟨s, i, t, base, pro⟩ := d
  cases s <;> simp only [next] at hn
  all_goals (repeat' split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hn)
  all_goals (try subst hn)
  all_goals (try (obtain ⟨h1, h2⟩ := afterCommit_end _ hp; rw [h1]; omega))
  all_goals (try simp only [start] at hp ⊢)
  all_goals (try split_ifs at hp ⊢)
  all_goals (try simp only [phase_next.1, phase_next.2.1, phase_next.2.2.1,
    phase_next.2.2.2.1, phase_next.2.2.2.2.1, phase_next.2.2.2.2.2] at hp)
  all_goals simp_all [Site.phase, EndOk]

end Mma


/-! ### The other roles -/

theorem Store.site_not_shfl (s : Store.Site) : s.pc ∉ shflPcs := by cases s <;> site_decide
theorem Idle.site_not_shfl (s : Idle.Site) : s.pc ∉ shflPcs := by cases s <;> site_decide
theorem Correction.site_not_shfl (s : Correction.Site) : s.pc ∉ shflPcs := by
  cases s <;> site_decide
theorem Softmax.site_not_shfl (s : Softmax.Site) : s.pc ∉ shflPcs := by cases s <;> site_decide

/-! ### The thread's count -/

/-- Whether a thread's state is at a shuffle. -/
def isShflSite : ThreadD → Bool
  | .inl p => p.site.isShfl
  | .inr (.loader d) => decide (d.site = .head)
  | .inr (.mma d) => d.site.isShfl
  | .inr _ => false

/-- The thread's shuffles before a state. -/
def shflCnt (L : Launch) (g : Nat) : ThreadD → Nat
  | .inl p => p.site.shfls
  | .inr (.loader d) => 4 + Loader.shfls L g d
  | .inr (.mma d) => 4 + Mma.shfls L d
  | .inr _ => 4

/-- The run invariant of the shuffle count: the roles' counts, the count of shuffles, and the
MMA warp's end. -/
def shflJ (L : Launch) (g : Nat) (d : ThreadD) (es : List Event) : Prop :=
  roleJ L g d es ∧ es.countP Execution.isShfl = shflCnt L g d ∧
    (match d with
      | .inr (.mma m) => Mma.EndOk L g m
      | _ => True)

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- A site that is not a shuffle site fires no shuffle. -/
theorem not_shfl_of {d : ThreadD} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hs : (code L g).pc d ∉ shflPcs) (hc : kernel.code[(code L g).pc d]? = some ins)
    (hf : Fires ((code L g).pc d) (eventTmpl asms L g t ins.op) e o) :
    Execution.isShfl e = false := by
  by_contra h
  exact hs (OpPcsFast.mem kernel_shfl_pcs hc (fires_shfl_op hf (by simpa using h)))

theorem shflJ_run (hpre : Pre P L mem0) (hg : g < L.threads) : RunInv L g (shflJ L g) where
  init := ⟨(roleJ_run hpre hg).init, rfl, trivial⟩
  step := by
    intro d d' pre e t u ins hJ hat hi hc hf hn
    obtain ⟨hR, hC, hE⟩ := hJ
    refine ⟨(roleJ_run hpre hg).step hR hat hi hc hf hn, ?_, ?_⟩
    · rw [List.countP_append, hC, List.countP_singleton]
      rcases d with p | r
      · change (Prologue.next L g p e).map (Option.bind · (handoff L g)) = some (some d') at hn
        cases hx : Prologue.next L g p e with
        | none => rw [hx] at hn; cases hn
        | some x =>
          rw [hx] at hn
          cases x with
          | none => cases hn
          | some x =>
            have hs := Prologue.shfls_next hx
            have hev : Execution.isShfl e = p.site.isShfl := by
              cases hp : p.site.isShfl
              · exact not_shfl_of (d := .inl p) (Prologue.site_shfl_pc _ hp) hc hf
              · exact Prologue.next_shfl hp hx
            rw [hev]
            cases x with
            | inl p' =>
              simp only [Option.map_some, Option.bind_some, handoff, Option.some.injEq] at hn
              subst hn
              exact hs.symm
            | inr k =>
              simp only [Option.map_some, Option.bind_some, handoff] at hn
              simp only at hs
              cases k <;> simp only [Role.start, Option.map_some,
                Option.some.injEq] at hn <;> subst hn <;>
                simp [shflCnt, Loader.shfls, Mma.shfls_start] <;> omega
      · obtain ⟨r', rfl, hk⟩ := code_next_inr hn
        cases r with
        | loader l =>
          cases r' <;> simp only [Role.kind, reduceCtorEq] at hk
          rename_i l'
          have hn' := next_role (fun _ _ h => Role.loader.inj h) hn
          have hev : Execution.isShfl e = decide (l.site = .head) := by
            by_cases hh : l.site = .head
            · simp only [hh, decide_true]; exact Loader.next_shfl hh hn'
            · simp only [hh, decide_false]
              exact not_shfl_of (d := .inr (.loader l)) (Loader.site_shfl_pc _ hh) hc hf
          rw [hev, shflCnt, shflCnt, Loader.shfls_next hi hn']
          by_cases hh : l.site = .head <;> simp [hh, Nat.add_assoc]
        | mma m =>
          cases r' <;> simp only [Role.kind, reduceCtorEq] at hk
          rename_i m'
          have hn' := next_role (fun _ _ h => Role.mma.inj h) hn
          have hev : Execution.isShfl e = m.site.isShfl := by
            cases hh : m.site.isShfl
            · exact not_shfl_of (d := .inr (.mma m)) (Mma.site_shfl_pc _ hh) hc hf
            · exact Mma.next_shfl hh hn'
          rw [hev, shflCnt, shflCnt, Mma.shfls_next hi.1 hR.pre hn']
          cases m.site.isShfl <;> simp [Nat.add_assoc]
        | idle s =>
          cases r' <;> simp only [Role.kind, reduceCtorEq] at hk
          rw [not_shfl_of (d := .inr (.idle s)) (Idle.site_not_shfl _) hc hf]; rfl
        | store s =>
          cases r' <;> simp only [Role.kind, reduceCtorEq] at hk
          rw [not_shfl_of (d := .inr (.store s)) (Store.site_not_shfl _) hc hf]; rfl
        | softmax s =>
          cases r' <;> simp only [Role.kind, reduceCtorEq] at hk
          rw [not_shfl_of (d := .inr (.softmax s)) (Softmax.site_not_shfl _) hc hf]; rfl
        | corr s =>
          cases r' <;> simp only [Role.kind, reduceCtorEq] at hk
          rw [not_shfl_of (d := .inr (.corr s)) (Correction.site_not_shfl _) hc hf]; rfl
    · rcases d with p | r
      · change (Prologue.next L g p e).map (Option.bind · (handoff L g)) = some (some d') at hn
        rcases d' with p' | r'
        · trivial
        cases r' <;> try trivial
        rename_i m'
        intro hp
        cases hx : Prologue.next L g p e with
        | none => rw [hx] at hn; cases hn
        | some x =>
          rw [hx] at hn
          rcases x with _ | _ | k
          · cases hn
          · simp [handoff] at hn
          · cases k <;> simp [handoff, Role.start] at hn
            subst hn
            simp [Mma.Site.phase] at hp
      · obtain ⟨r', rfl, hk⟩ := code_next_inr hn
        cases r with
        | mma m =>
          cases r' <;> simp only [Role.kind, reduceCtorEq] at hk
          exact Mma.endOk_next hE (next_role (fun _ _ h => Role.mma.inj h) hn)
        | _ => cases r' <;> trivial

end
end PTX.Kernels.FlashAttn4Fwd.Proof
