-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingTensorEvents
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MmaDataTrace

@[expose] public section

/-! # Each query transfer site issues once -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.QueryTmaSites

open PTX PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {X : Execution} {g : Nat}

private def transferRank : Wg1Mma.Site → Nat
  | .head | .elect | .loadTopk | .loadExtra => 0
  | .qLoad tile => tile.val
  | .qArrive => 8
  | .qWait | .qFence => 9
  | .qCopy chunk => 9 + chunk.val
  | .qCopyCommit => 25
  | _ => 26

private theorem transferRank_le (s : Wg1Mma.Site) : transferRank s ≤ 26 := by
  cases s
  case qLoad k => have := k.isLt; simp only [transferRank]; omega
  case qCopy k => have := k.isLt; simp only [transferRank]; omega
  all_goals simp only [transferRank]; decide

set_option maxHeartbeats 1200000 in
private theorem mma_rank_mono {d d' : Wg1Mma.D} {e : Event}
    (hn : Wg1Mma.next P L g d e = some (some d')) :
    transferRank d.site ≤ transferRank d'.site := by
  cases hd : d.site <;> simp only [Wg1Mma.next, hd, Wg1Mma.nextSite] at hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals
    try simp only [Wg1Mma.startSite, Wg1Mma.afterTopk]
    repeat' split_ifs
    all_goals simp_all [transferRank]
  rename_i k _
  have := k.isLt
  omega

private def stateRank : Option (Option Machine.ThreadD) → Nat
  | some (some (.mma d)) => transferRank d.site
  | some (some .done) | some none | none => 26
  | _ => 0

private theorem next_mono {d : Machine.ThreadD} {e : Event} :
    stateRank (some (some d)) ≤ stateRank (Machine.next P L g d e) := by
  cases d
  case mma q =>
    simp only [Machine.next]
    split
    · exact mma_rank_mono (by assumption)
    · split_ifs with h
      · simp [stateRank, h, transferRank]
      · exact transferRank_le _
    · split_ifs <;> exact transferRank_le _
  case done => exact Nat.le_refl 26
  all_goals exact Nat.zero_le _

private theorem frame_mono {i j : Nat} (hij : i ≤ j) (hj : j ≤ (X.tr g).length) :
    stateRank (Frame.stateAt (Machine.code P L) X g i) ≤
      stateRank (Frame.stateAt (Machine.code P L) X g j) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction n with
  | zero => simp
  | succ n ih =>
    have hlt : i + n < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[i + n]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    refine (ih hlt.le).trans ?_
    rw [Nat.add_succ, Frame.stateAt_succ he]
    cases h : Frame.stateAt (Machine.code P L) X g (i + n) with
    | none => exact Nat.le_refl 26
    | some v =>
      cases v with
      | none => exact Nat.le_refl 26
      | some d => exact next_mono (P := P) (L := L) (g := g)

/-- An MMA loop site cannot occur before the query-copy commit in the same trace. -/
theorem loop_after_copy_commit {i j : Nat} {d q : Wg1Mma.D} {e : Event}
    (he : X.get (g, j) = some e)
    (hi : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hj : Frame.stateAt (Machine.code P L) X g j = some (some (.mma q)))
    (hLoop : Wg1Mma.LoopSite d.site) (hCommit : q.site = .qCopyCommit) : j < i := by
  by_contra! hle
  have hRank := frame_mono (P := P) (L := L) hle (PTX.len_of_get he).le
  rw [hi, hj] at hRank
  change transferRank d.site ≤ transferRank q.site at hRank
  rw [hCommit] at hRank
  cases hd : d.site <;> simp_all [Wg1Mma.LoopSite, transferRank]

private theorem transfer_strict {i : Nat} {d : Wg1Mma.D} {e : Event}
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hs : (∃ tile, d.site = .qLoad tile) ∨
      (∃ chunk, d.site = .qCopy chunk) ∨ d.site = .qCopyCommit ∨ d.site = .qArrive) :
    transferRank d.site < stateRank (Frame.stateAt (Machine.code P L) X g (i + 1)) := by
  rw [Frame.stateAt_succ he, hd]
  change transferRank d.site < stateRank (Machine.next P L g (.mma d) e)
  rcases hs with ⟨tile, hs⟩ | ⟨tile, hs⟩ | hs | hs
  · have hk := tile.isLt
    simp only [Machine.next, Wg1Mma.next, hs, Wg1Mma.nextSite]
    split_ifs <;> simp [stateRank, transferRank]
  · have hk := tile.isLt
    simp only [Machine.next, Wg1Mma.next, hs, Wg1Mma.nextSite]
    split_ifs <;> simp [stateRank, transferRank]
    omega
  · simp [Machine.next, Wg1Mma.next, hs, stateRank, transferRank]
  · simp [Machine.next, Wg1Mma.next, hs, stateRank, transferRank]

private theorem site_unique {i j : Nat} {site : Wg1Mma.Site} {d d' : Wg1Mma.D} {e f : Event}
    (he : X.get (g, i) = some e) (hf : X.get (g, j) = some f)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hd' : Frame.stateAt (Machine.code P L) X g j = some (some (.mma d')))
    (hs : d.site = site) (hs' : d'.site = site)
    (hSite : (∃ tile, site = .qLoad tile) ∨
      (∃ chunk, site = .qCopy chunk) ∨ site = .qCopyCommit ∨ site = .qArrive) : i = j := by
  have hnot {a b : Nat} {q q' : Wg1Mma.D} {e f : Event}
      (ha : X.get (g, a) = some e) (hb : X.get (g, b) = some f)
      (hdl : Frame.stateAt (Machine.code P L) X g a = some (some (.mma q)))
      (hdr : Frame.stateAt (Machine.code P L) X g b = some (some (.mma q')))
      (hsl : q.site = site) (hsr : q'.site = site) : ¬ a < b := by
    intro hab
    have hl : b < (X.tr g).length := PTX.len_of_get hb
    have hm := frame_mono (P := P) (L := L) (X := X) (g := g) hab hl.le
    rw [hdr] at hm
    have hlt := (transfer_strict ha hdl (by rw [hsl]; exact hSite)).trans_le hm
    exact (Nat.lt_irrefl _) (by simpa only [stateRank, hsl, hsr] using hlt)
  exact Nat.le_antisymm (Nat.le_of_not_gt (hnot hf he hd' hd hs' hs))
    (Nat.le_of_not_gt (hnot he hf hd hd' hs hs'))

/-- A query TMA tile is issued at most once per lane. -/
theorem load_site_unique {i j : Nat} {tile : Fin 8} {d d' : Wg1Mma.D} {e f : Event}
    (he : X.get (g, i) = some e) (hf : X.get (g, j) = some f)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hd' : Frame.stateAt (Machine.code P L) X g j = some (some (.mma d')))
    (hs : d.site = .qLoad tile) (hs' : d'.site = .qLoad tile) : i = j :=
  site_unique he hf hd hd' hs hs' (.inl ⟨tile, rfl⟩)

/-- A query-copy chunk is issued at most once per lane. -/
theorem copy_site_unique {i j : Nat} {chunk : Fin 16} {d d' : Wg1Mma.D} {e f : Event}
    (he : X.get (g, i) = some e) (hf : X.get (g, j) = some f)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hd' : Frame.stateAt (Machine.code P L) X g j = some (some (.mma d')))
    (hs : d.site = .qCopy chunk) (hs' : d'.site = .qCopy chunk) : i = j :=
  site_unique he hf hd hd' hs hs' (.inr (.inl ⟨chunk, rfl⟩))

/-- The elected lane issues its query-copy commit at most once. -/
theorem commit_site_unique {i j : Nat} {d d' : Wg1Mma.D} {e f : Event}
    (he : X.get (g, i) = some e) (hf : X.get (g, j) = some f)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hd' : Frame.stateAt (Machine.code P L) X g j = some (some (.mma d')))
    (hs : d.site = .qCopyCommit) (hs' : d'.site = .qCopyCommit) : i = j :=
  site_unique he hf hd hd' hs hs' (.inr (.inr (.inl rfl)))

/-- The query's expect-tx arrival is issued at most once by the elected lane. -/
theorem arrive_site_unique {i j : Nat} {d d' : Wg1Mma.D} {e f : Event}
    (he : X.get (g, i) = some e) (hf : X.get (g, j) = some f)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hd' : Frame.stateAt (Machine.code P L) X g j = some (some (.mma d')))
    (hs : d.site = .qArrive) (hs' : d'.site = .qArrive) : i = j :=
  site_unique he hf hd hd' hs hs' (.inr (.inr (.inr rfl)))

/-- A firing at a followed query-load site has the exact query tensor specification. -/
theorem fired_load {mem0 : Mem0} {d : Wg1Mma.D} {e : Event} {o : Option TState}
    {tile : Fin 8} {a : Nat} {spec : TensorCopy.Spec} (hpre : Pre P L mem0) (hg : g < L.threads)
    (hs : d.site = .qLoad tile)
    (hf : (Machine.machine P L g).Fired (some (.mma d)) e o)
    (he : e.kind = .tensorIssue a spec) :
    a = P.param1Base + Wg1Mma.qMapOff ∧ spec = MmaDataTrace.queryTmaSpec P L g tile := by
  cases o with
  | none =>
    obtain ⟨_, _, hfire⟩ := hf
    rcases fires_none_ends hfire with ⟨f, hk⟩ | hk <;> rw [he] at hk <;> cases hk
  | some u =>
    obtain ⟨t, ⟨hat, _⟩, hfire⟩ := hf
    change (Wg1Mma.code P L g).AtD d t at hat
    change Fires t.pc (match kernel.code[d.site.pc]? with
      | some ins => eventTmpl Assumptions.all L g t ins.op
      | none => .ub .pcOutOfRange) e (some u) at hfire
    have hpc : t.pc = d.site.pc := hat.1
    rw [hpc, hs] at hfire
    have hq : d = ⟨.qLoad tile, d.i⟩ := by cases d; simp_all
    rw [hq] at hat
    cases hc : kernel.code[(Wg1Mma.Site.qLoad tile).pc]? with
    | none =>
      rw [hc] at hfire
      cases hfire.2
    | some ins =>
      rw [hc] at hfire
      exact Kind.tensorIssue.inj
        (he.symm.trans (MmaDataTrace.fires_qLoad hpre hg d.i tile hat hc hfire).1)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.QueryTmaSites
