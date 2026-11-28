-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.QMov
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.QuerySkip
public import Lemmas.Flow.SegQSkip
public import Lemmas.Flow.OutRun
public import Lemmas.Flow.DataCompute

@[expose] public section

/-! # The strict query sites: the skipped loads

A state of the query region, with the facts of the loads before it. A load whose group is off
is skipped, and the move after it makes the zero half the next load's register. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged Control Arith32

set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {g : Nat} {w : Value}

/-- The state of the query site `s` with the control words `c` and the halves `v`. -/
abbrev dq (c : Control.D) (v : Data.Vals) (s : Site) : Data.D := ⟨{c with site := s}, v⟩

theorem mem_ctl {d : Data.D} {r : Nat} (h : r ∈ ctlLive d.c.site.pc) :
    (r, valueOf Q L g w d.c r) ∈ dFacts Q L g w d :=
  List.mem_append_right _ (mem_factsFrom (val := valueOf Q L g w d.c) h)

theorem mem_tag {d : Data.D} {τ : Data.Tag} (h : τ ∈ Data.tags d.c.site) :
    (τ.reg, τ.val Q L g d) ∈ dFacts Q L g w d :=
  List.mem_append_left _ (List.mem_map_of_mem (f := fun τ => (τ.reg, τ.val Q L g d)) h)

theorem keys_notin {d : Data.D} {r : Nat} (h1 : r ∉ ctlLive d.c.site.pc)
    (h2 : r ∉ (Data.tags d.c.site).map Data.Tag.reg) :
    r ∉ (dFacts Q L g w d).map Prod.fst := fun h => by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp hp
    exact h2 (List.mem_map_of_mem (f := Data.Tag.reg) hτ)
  · exact h1 (by simpa [facts, factsFrom_keys] using List.mem_map_of_mem (f := Prod.fst) hp)

/-- No step: the facts `G` are among the facts `F`. -/
theorem SegQ.sub {Q' : TState → Prop} {a : Nat} {F G : List (Nat × Value)}
    (h : ∀ q ∈ G, q ∈ F) : SegQ kernel Assumptions.all L g Q' a F a G :=
  SegQ.weaken fun _ hR => holds_of_forall fun p hp => holds_mem hR (h p hp)

/-- The load `j` of the first 63, and the load after it. -/
abbrev f64 (j : Fin 63) : Fin 64 := ⟨j.val, by omega⟩
abbrev f64s (j : Fin 63) : Fin 64 := ⟨j.val + 1, by omega⟩

theorem q_fresh : ∀ j : Fin 63, qDst (f64s j) ∉ ctlLive (queryPc (f64 j)) ∧
    qDst (f64s j) ∉ (Data.tags (.ldq (f64 j))).map Data.Tag.reg ∧
    qDst (f64s j) ≠ qDst (f64 j) := by decide +kernel

theorem q_tags : ∀ j : Fin 63, ∀ τ ∈ Data.tags (.ldq (f64s j)),
    τ ∈ Data.tags (.ldq (f64 j)) ∨ τ = .qh (f64 j) := by decide +kernel

theorem q_live : ∀ j : Fin 63, (ctlLive (queryPc (f64 j) + 2)).isSublist
    (ctlLive (queryPc (f64 j))) = true := by decide +kernel

theorem q_move_code : ∀ j : Fin 63, OItem.instrB kernel.code[queryPc (f64 j) + 1]?
    (.move ⟨.scalar, .int .u 16, [some (qDst (f64s j))], [.reg 199]⟩) = true := by decide +kernel

theorem q_move_tags : ∀ j : Fin 63, ∀ p ∈ proQt (queryPc (f64 j) + 1 + 1),
    p.1 ≠ qDst (f64s j) ∧ (proQt (queryPc (f64 j) + 1)).lookup p.1 = some p.2 := by decide +kernel

theorem q_skip_tags : ∀ j : Fin 63, tagsIn (proQt (queryPc (f64 j) + 1)) (proQt (queryPc (f64 j))) =
    true := by decide +kernel

theorem q_move_pc : ∀ j : Fin 63, 27 ≤ queryPc (f64 j) + 1 ∧ queryPc (f64 j) + 1 < 574 := by
  decide +kernel

/-- The facts of a skipped query load: the zero half of its register is held. -/
noncomputable abbrev SkipF (Q : Params) (L : Launch) (g : Nat) (w : Value) (c : Control.D) (v :
    Data.Vals) (j : Fin 64) : List (Nat × Value) :=
  (qDst j, Data.zeroV) :: dFacts Q L g w (dq c v (.ldq j))

theorem tag_val_site (c : Control.D) (v : Data.Vals) (s s' : Site) (τ : Data.Tag) :
    τ.val Q L g (dq c v s) = τ.val Q L g (dq c v s') := by cases τ <;> rfl

theorem mem_succ {c : Control.D} {v : Data.Vals} (j : Fin 63)
    (hoff : queryOn (g % L.block) (j.val / 16) c = false) :
    ∀ q ∈ dFacts Q L g w (dq c v (.ldq (f64s j))), q ∈ SkipF Q L g w c v (f64 j) := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp hq
    rcases q_tags j τ hτ with h | rfl
    · rw [tag_val_site (Q := Q) (L := L) (g := g) c v (.ldq (f64s j)) (.ldq (f64 j)) τ]
      exact List.mem_cons_of_mem _ (mem_tag (w := w) (d := dq c v (.ldq (f64 j))) h)
    · have e : Data.Tag.val Q L g (dq c v (.ldq (f64s j))) (.qh (f64 j)) = Data.zeroV := by
        simp only [Data.Tag.val, Data.qv]
        have h0 : queryOn (g % L.block) (j.val / 16) (dq c v (.ldq (f64s j))).c = false := hoff
        simp [h0]
        rfl
      rw [e]
      exact List.mem_cons_self
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    exact List.mem_cons_of_mem _ (mem_ctl (w := w) (d := dq c v (.ldq (f64 j)))
      ((List.isSublist_iff_sublist.mp (q_live j)).subset hr))


theorem pc_succ (j : Fin 63) : queryPc (f64s j) = queryPc (f64 j) + 2 := by
  simp only [queryPc, Site.pc]; omega

/-- **A skipped load and the move after it**: the next register holds the zero half. -/
theorem qs_step (c : Control.D) (v : Data.Vals) (j : Fin 63)
    (hoff : queryOn (g % L.block) (j.val / 16) c = false) :
    SegQ kernel Assumptions.all L g (QT proQt) (queryPc (f64 j)) (SkipF Q L g w c v (f64 j))
      (queryPc (f64s j)) (SkipF Q L g w c v (f64s j)) := by
  obtain ⟨hk1, hk2, hk3⟩ := q_fresh j
  obtain ⟨hlo, hhi⟩ := q_move_pc j
  have hz : (199, Data.zeroV) ∈ SkipF Q L g w c v (f64 j) :=
    List.mem_cons_of_mem _ (mem_tag (w := w) (d := dq c v (.ldq (f64 j))) (τ := .zero) (by
      simp [Data.tags, Data.oldTags, Data.qTags]))
  have hn : qDst (f64s j) ∉ (SkipF Q L g w c v (f64 j)).map
      Prod.fst := by
    simp only [List.map_cons, List.mem_cons, not_or]
    exact ⟨hk3, keys_notin (w := w) (d := dq c v (.ldq (f64 j))) hk1 hk2⟩
  rw [pc_succ]
  refine SegQ.comp (b := queryPc (f64 j) + 1) (G := SkipF Q L g w c v
    (f64 j)) (SegQ.skipG (pick := false) (neg := false) (p := queryPred (f64 j))
    (qLoadPair (L := L) (g := g) (f64 j)).2 (fun R hR => ?_) rfl (fun _ h => h)
    (q_skip_tags j)) ?_
  · have := holds_mem hR (List.mem_cons_of_mem _ (mem_ctl (w := w)
      (d := dq c v (.ldq (f64 j))) (query_live (f64 j))))
    rw [query_value] at this
    have h0 : queryOn (g % L.block) (j.val / 16) (dq c v (.ldq (f64 j))).c = false := hoff
    simpa [h0] using this
  · refine SegQ.comp (b := queryPc (f64 j) + 1 + 1) (G := (qDst (f64s j), Data.zeroV) ::
      SkipF Q L g w c v (f64 j)) (move_seg (v := Data.zeroV)
      (OItem.instrB_eq (q_move_code j)) rfl rfl hlo hhi
      (fun t hF => hex_mov16 hz rfl t hF) (fun R hR => holds_update_cons hR hn)
      (q_move_tags j)) (SegQ.sub fun q hq => ?_)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_succ j hoff q hq)


/-- **A run of skipped loads**, from the load `a` to the load `b`. -/
theorem qs_run (c : Control.D) (v : Data.Vals) (n : Nat) :
    ∀ (a : Nat) (b : Fin 64) (hb : b.val = a + n),
    (∀ k, a ≤ k → k < b.val → queryOn (g % L.block) (k / 16) c = false) →
    SegQ kernel Assumptions.all L g (QT proQt) (queryPc ⟨a, by omega⟩)
      (SkipF Q L g w c v ⟨a, by omega⟩) (queryPc b) (SkipF Q L g w c v b) := by
  induction n with
  | zero =>
    intro a b hb _
    obtain ⟨b, hb'⟩ := b
    simp only [Nat.add_zero] at hb
    subst hb
    exact SegQ.sub fun _ h => h
  | succ n ih =>
    intro a b hb hoff
    have h1 : a < 63 := by omega
    refine SegQ.comp (b := queryPc ⟨a + 1, by omega⟩) (G := SkipF Q L g w c v ⟨a + 1, by omega⟩)
      (qs_step (w := w) c v ⟨a, h1⟩ (hoff a le_rfl (by omega))) ?_
    exact ih (a + 1) b (by omega) fun k hk hk' => hoff k (by omega) hk'

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
