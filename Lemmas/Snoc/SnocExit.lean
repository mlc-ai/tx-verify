-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Snoc.SnocSinkFrame
public import Lemmas.Flow.WaitTmpl
public import Lemmas.Snoc.SnocResourceWaiting

@[expose] public section

/-! # Appending an exit

An exit fills the need of a lane collective (`MaskExitK`, `MaskExited`) or of a warp-level matrix
instruction (`ExitedShort`) only for an instance that its thread did not reach. Every collective
of `X` exists only once its instance is complete (a returned blocking event is ready, DEP-ORDER),
so a running thread has already performed its event of each such instance: the appended exit
is not an exit before it, and it fills no need of an existing event. -/
namespace PTX
open AsyncCopy
noncomputable section

section
variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {g : Nat} {e : Event} {r : Nat → Option Ref}

/-- A thread whose run leaves a state has not exited. -/
theorem no_exit_of_run {t : TState} (hrun : Run K A L g {} (X.tr g) (some t)) :
    ∀ i pc, X.get (g, i) ≠ some ⟨pc, .exit⟩ := by
  intro i pc h
  exact Flow.Run.no_end hrun _ (List.mem_of_getElem? h) (.inr rfl)

/-- The `n`-th event of class `c` with mask `m` of a thread is followed by no more than the thread's
count of such events. -/
theorem lt_countP_of_maskK {Q V : Type} {c : Kind → Option (WarpPart Q V)} {v : EvId}
    {m n : Nat} (h : X.MaskK c v m n) :
    n < (X.tr v.1).countP (fun ev => (c ev.kind).any (·.mask == m)) := by
  obtain ⟨⟨ev, p, hg, hc, hm⟩, hcnt⟩ := h
  have hv := len_of_get hg
  have hd : (X.tr v.1).drop v.2 = ev :: (X.tr v.1).drop (v.2 + 1) := by
    rw [List.drop_eq_getElem_cons hv]
    congr 1
    exact Option.some.inj ((List.getElem?_eq_getElem hv).symm.trans hg)
  rw [← List.take_append_drop v.2 (X.tr v.1), List.countP_append, hcnt, hd, List.countP_cons]
  simp [hc, hm]

theorem lt_countP_of_matrixK {v : EvId} {n : Nat} (h : X.MatrixK v n) :
    n < (X.tr v.1).countP isMatrix := by
  obtain ⟨⟨ev, hg, hm⟩, hcnt⟩ := h
  have hv := len_of_get hg
  have hd : (X.tr v.1).drop v.2 = ev :: (X.tr v.1).drop (v.2 + 1) := by
    rw [List.drop_eq_getElem_cons hv]
    congr 1
    exact Option.some.inj ((List.getElem?_eq_getElem hv).symm.trans hg)
  rw [← List.take_append_drop v.2 (X.tr v.1), List.countP_append, hcnt, hd, List.countP_cons]
  simp [hm]

/-- The mask and number of an event of class `c` are its own. -/
theorem maskK_unique {Q V : Type} {c : Kind → Option (WarpPart Q V)} {v : EvId}
    {m m' n n' : Nat} (h : X.MaskK c v m n) (h' : X.MaskK c v m' n') : m = m' ∧ n = n' := by
  obtain ⟨⟨ev, p, hg, hc, hm⟩, hcnt⟩ := h
  obtain ⟨⟨ev', p', hg', hc', hm'⟩, hcnt'⟩ := h'
  rw [hg] at hg'
  cases hg'
  rw [hc] at hc'
  cases hc'
  have hmm : m = m' := hm.symm.trans hm'
  subst hmm
  exact ⟨rfl, hcnt.symm.trans hcnt'⟩

/-- A lane collective that is ready names, for each lane of its mask in a running thread, the
lane's event of its instance. -/
theorem maskK_lane_of_ready {Q V : Type} (c : Kind → Option (WarpPart Q V))
    (hgx : ∀ i pc, X.get (g, i) ≠ some ⟨pc, .exit⟩) {f : EvId} {ev : Event} {p : WarpPart Q V}
    (hf : X.get f = some ev) (hc : c ev.kind = some p)
    (hneeds : ∀ n ∈ maskNeeds L c X f, n ∈ Needs L X f) (hready : Ready L X f)
    {m n : Nat} {q : Q} (hat : X.MaskAt c f m n q) {lane : Nat} (hl : lane < 32)
    (hb : m.testBit lane = true) (hg : f.1 - laneOf L f.1 + lane = g) :
    ∃ j, X.MaskK c (g, j) m n := by
  have hpm : p.mask = m := by
    obtain ⟨⟨ev', p', hg', hc', hm'⟩, -⟩ := hat.1
    rw [hf] at hg'
    cases hg'
    rw [hc] at hc'
    cases hc'
    exact hm'
  have hmem := maskNeeds_mem L c X f hf hc hl (by rw [hpm]; exact hb)
  obtain ⟨x, -, j, rfl, hw⟩ := hready _ (hneeds _ hmem)
  obtain ⟨-, m', n', q', hat', hrest⟩ := hw
  obtain ⟨rfl, rfl⟩ := maskK_unique hat.1 hat'.1
  have hgl : warpLane L f.1 lane = g := hg
  rw [hgl] at hrest
  rcases hrest with he | ⟨-, ⟨pc, hge⟩, -⟩
  · exact ⟨j, he.1⟩
  · exact (hgx j pc hge).elim

/-- An exit appended to a running thread is no exit before an instance that a ready collective of
`X` belongs to. -/
theorem snoc_exit_maskExited {Q V : Type} (c : Kind → Option (WarpPart Q V))
    (hgx : ∀ i pc, X.get (g, i) ≠ some ⟨pc, .exit⟩) {f : EvId} {ev : Event} {p : WarpPart Q V}
    (hf : X.get f = some ev) (hc : c ev.kind = some p)
    (hneeds : ∀ n ∈ maskNeeds L c X f, n ∈ Needs L X f) (hready : Ready L X f)
    {m n : Nat} {q : Q} (hat : X.MaskAt c f m n q) {lane : Nat} (hl : lane < 32)
    (hb : m.testBit lane = true)
    (h : MaskExited c (X.snoc g e r) (f.1 - laneOf L f.1 + lane) m n) :
    MaskExited c X (f.1 - laneOf L f.1 + lane) m n := by
  obtain ⟨k, pc, hk, hcnt⟩ := h
  rw [snoc_get] at hk
  split_ifs at hk with hkn
  · have hlg : f.1 - laneOf L f.1 + lane = g := congrArg Prod.fst hkn
    have hkl : k = (X.tr g).length := congrArg Prod.snd hkn
    obtain ⟨j, hj⟩ := maskK_lane_of_ready (L := L) c hgx hf hc hneeds hready hat hl hb hlg
    have hlt := lt_countP_of_maskK hj
    rw [hlg, snoc_tr, ite_eq_left rfl, hkl, List.take_left'] at hcnt
    · exact absurd hcnt (by simp only at hlt; omega)
    · rfl
  · exact ⟨k, pc, hk, by rwa [snoc_take (len_of_get hk).le] at hcnt⟩

/-- A lane collective instance of a ready collective of `X` is one of `X` after an exit appended to
a running thread. -/
theorem maskInstance_snoc_exit {Q V : Type} (c : Kind → Option (WarpPart Q V))
    (hce : c .exit = none) (he : e.kind = .exit)
    (hgx : ∀ i pc, X.get (g, i) ≠ some ⟨pc, .exit⟩) {f : EvId} {ev : Event} {p : WarpPart Q V}
    (hf : X.get f = some ev) (hc : c ev.kind = some p)
    (hneeds : ∀ n ∈ maskNeeds L c X f, n ∈ Needs L X f) (hready : Ready L X f)
    {m n : Nat} {q : Q} (hat : X.MaskAt c f m n q) {part : Nat → Option V}
    (hi : MaskInstance L c (X.snoc g e r) f.1 m n q part) : MaskInstance L c X f.1 m n q part := by
  intro lane hl
  obtain ⟨h1, h2⟩ := hi lane hl
  refine ⟨fun hb => ?_, h2⟩
  rcases h1 hb with ⟨j, pc, k, v, hj, hck, hk, hp⟩ | ⟨hx, hp⟩
  · have hjx : X.get (f.1 - laneOf L f.1 + lane, j) = some ⟨pc, k⟩ := by
      rw [snoc_get] at hj
      split_ifs at hj
      · have hk' : e.kind = k := congrArg Event.kind (Option.some.inj hj)
        rw [he] at hk'
        subst hk'
        rw [hce] at hck
        cases hck
      · exact hj
    exact .inl ⟨j, pc, k, v, hjx, hck, Execution.maskK_of_le le_snoc hjx hk, hp⟩
  · exact .inr ⟨snoc_exit_maskExited (L := L) c hgx hf hc hneeds hready hat hl hb hx, hp⟩

/-- A returned lane collective of class `c` is ready, and its needs are those of its class. -/
private theorem ready_of_class {Q V : Type} (c : Kind → Option (WarpPart Q V))
    (hX : Consistent L K A mem0 X) {f : EvId} {pc : Nat} {k : Kind} (hf : X.get f = some ⟨pc, k⟩)
    (hres : k.resume = .blocking true) (hk : KindNeeds L X k f = maskNeeds L c X f) :
    (∀ n ∈ maskNeeds L c X f, n ∈ Needs L X f) ∧ Ready L X f := by
  refine ⟨fun n hn => by simp only [Needs, hf]; rw [hk]; exact hn, hX.dependency.ready f ?_⟩
  unfold Returned
  rw [hf]
  cases k <;> simp_all [Kind.resume]

/-- **An exit appended to a running thread keeps the ballot values** (DEP-WARP-VOTE). -/
theorem snoc_exit_voteOk (hX : Consistent L K A mem0 X) (he : e.kind = .exit)
    (hgx : ∀ i pc, X.get (g, i) ≠ some ⟨pc, .exit⟩) : VoteOk L (X.snoc g e r) := by
  intro g0 i n pc mask a ballot hget hk part hp lane hl
  have hget' : X.get (g0, i) = some ⟨pc, .vote mask a ballot⟩ :=
    snoc_get_not_kind hget (by rw [he]; intro h; cases h)
  have hk' := Execution.maskK_of_le le_snoc hget' hk
  obtain ⟨hn, hr⟩ := ready_of_class (L := L) voteClass hX hget' rfl rfl
  exact hX.vote g0 i n pc mask a ballot hget' hk' part
    (maskInstance_snoc_exit (L := L) voteClass rfl he hgx hget' rfl hn hr
      ⟨hk', _, _, hget', rfl, rfl⟩ hp) lane hl

/-- **An exit appended to a running thread keeps the values of mode votes, reductions, matches
and `activemask`** (DEP-WARP-VOTE, DEP-WARP-REDUX, DEP-WARP-MATCH, DEP-WARP-ACTIVEMASK). -/
theorem snoc_exit_warpValueOk (hX : Consistent L K A mem0 X) (he : e.kind = .exit)
    (hgx : ∀ i pc, X.get (g, i) ≠ some ⟨pc, .exit⟩) : WarpValueOk L (X.snoc g e r) := by
  obtain ⟨hv, hr, hm, ha⟩ := hX.warpValue
  have old : ∀ {v pc k}, (X.snoc g e r).get v = some ⟨pc, k⟩ → k ≠ .exit →
      X.get v = some ⟨pc, k⟩ := fun h hk => snoc_get_not_kind h (by rw [he]; exact hk.symm)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g0 i pc mode mask a r' n hget hk part hp
    have hget' := old hget (by intro h; cases h)
    have hk' := Execution.maskK_of_le le_snoc hget' hk
    obtain ⟨hn, hrd⟩ := ready_of_class (L := L) voteClass hX hget' rfl rfl
    exact hv g0 i pc mode mask a r' n hget' hk' part
      (maskInstance_snoc_exit (L := L) voteClass rfl he hgx hget' rfl hn hrd
        ⟨hk', _, _, hget', rfl, rfl⟩ hp)
  · intro g0 i pc op signed mask a r' n hget hk part hp
    have hget' := old hget (by intro h; cases h)
    have hk' := Execution.maskK_of_le le_snoc hget' hk
    obtain ⟨hn, hrd⟩ := ready_of_class (L := L) reduxClass hX hget' rfl rfl
    exact hr g0 i pc op signed mask a r' n hget' hk' part
      (maskInstance_snoc_exit (L := L) reduxClass rfl he hgx hget' rfl hn hrd
        ⟨hk', _, _, hget', rfl, rfl⟩ hp)
  · intro g0 i pc all wide mask a r' p' n hget hk part hp
    have hget' := old hget (by intro h; cases h)
    have hk' := Execution.maskK_of_le le_snoc hget' hk
    obtain ⟨hn, hrd⟩ := ready_of_class (L := L) matchClass hX hget' rfl rfl
    exact hm g0 i pc all wide mask a r' p' n hget' hk' part
      (maskInstance_snoc_exit (L := L) matchClass rfl he hgx hget' rfl hn hrd
        ⟨hk', _, _, hget', rfl, rfl⟩ hp)
  · intro g0 i pc r' hget
    exact ha g0 i pc r' (old hget (by intro h; cases h))

end
end
end PTX
