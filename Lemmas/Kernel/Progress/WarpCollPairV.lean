-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.WarpCollPair
public import Lemmas.Kernel.FrameU

@[expose] public section
namespace PTX.Sched

open PTX PTX.Flow

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
  {X : Execution} {κ : Type}

variable {key : Nat → κ} {AtColl : ∀ g, (M.code g).D → Prop}
  {S : ∀ g, (M.code g).D → CollShape}

/-- **The warp collectives' facts from the facts of two lanes of a warp**, for a kernel whose
elections' masks are registers: the static part is checked for a collective event by its own kind
(`hSev`), and by the instruction's template only for a lane waiting at a collective (`hSend`). -/
theorem warpCollRel_of_pairsV
    (hkey : ∀ {g h : Nat}, g < L.threads → h < L.threads → key g = key h → SameWarp L g h)
    (hSF : ∀ {g k : Nat} {d : (M.code g).D}, g < L.threads → CollPos M X AtColl g k d →
      (S g d).Full)
    (hSev : ∀ {g k : Nat} {e : Event} {d : (M.code g).D}, g < L.threads →
      Frame.stateAt M.code X g k = some (some d) → X.get (g, k) = some e →
      isWarpColl e = true → kindShape e.kind = some (S g d))
    (hSend : ∀ {g : Nat} {d : (M.code g).D}, g < L.threads →
      Frame.stateAt M.code X g (X.tr g).length = some (some d) → AtColl g d →
      ∀ t ins, (M.code g).AtD d t → (M.code g).inv d → K.code[(M.code g).pc d]? = some ins →
        ins.op.isLocal = false ∧ ((∃ f, eventTmpl A L g t ins.op = .ub f) ∨
          tmplShape (eventTmpl A L g t ins.op) = some (S g d)))
    (hp : ∀ {g h : Nat}, SameWarp L g h → WarpPair mem0 M X AtColl S g h) :
    WarpCollRel mem0 M X key AtColl := by
  -- the common value at a position
  have hF : ∀ {g k : Nat} {d : (M.code g).D}, g < L.threads → CollPos M X AtColl g k d →
      collAt M X key AtColl S (key g) (((X.tr g).take k).countP isWarpColl) =
        ((M.code g).pc d, S g d) := by
    intro g k d hg hd
    have hex : ∃ g' k', ∃ d' : (M.code g').D, g' < L.threads ∧ key g' = key g ∧
        CollPos M X AtColl g' k' d' ∧ ((X.tr g').take k').countP isWarpColl =
          ((X.tr g).take k).countP isWarpColl := ⟨g, k, d, hg, rfl, hd, rfl⟩
    unfold collAt
    simp only [hex, dite_true]
    obtain ⟨h1, h2, h3, h4⟩ := Classical.choose_spec (Classical.choose_spec hex).choose_spec
    obtain ⟨e1, e2⟩ := (hp (hkey h1 hg h2)).pc h3 hd h4
    simp only [e1, e2]
  refine ⟨⟨collAt M X key AtColl S, fun c n => ?_, fun {g k e d} hg hσ he hc => ?_,
    fun {g d t m} hg hσ hd hAt hinv hout => ?_⟩, fun {g h d d'} hg hs => (hp hs).released, ?_,
    fun {h} hh => (hp ⟨⟨hh.1, hh.1, rfl⟩, rfl⟩ : WarpPair mem0 M X AtColl S h h).dead hh,
    fun {g h d} _ _ hs => (hp hs).lag⟩
  · unfold collAt
    split
    · rename_i h
      obtain ⟨h1, h2, h3, h4⟩ := Classical.choose_spec (Classical.choose_spec h).choose_spec
      exact hSF h1 h3
    · trivial
  · have hpos : CollPos M X AtColl g k d := ⟨hσ, .inl ⟨e, he, hc⟩⟩
    rw [hF hg hpos]
    exact hSev hg hσ he hc
  · have hpos : CollPos M X AtColl g (X.tr g).length d := ⟨hσ, .inr ⟨rfl, hd⟩⟩
    obtain ⟨hpc, -, -, hfault, -⟩ := id hAt
    rw [show ((X.tr g).countP isWarpColl) = ((X.tr g).take (X.tr g).length).countP isWarpColl by
      rw [List.take_length], hF hg hpos]
    unfold out at hout
    rw [hfault] at hout
    simp only [hpc] at hout ⊢
    cases hins : K.code[(M.code g).pc d]? with
    | none => rw [hins] at hout; cases hout; exact .inl ⟨_, rfl⟩
    | some ins =>
      rw [hins] at hout
      obtain ⟨hloc, hsh⟩ := hSend hg hσ hd t ins hAt hinv hins
      simp only [hloc, Bool.false_eq_true, ite_false] at hout
      split at hout
      · cases hout; exact .inl ⟨_, rfl⟩
      · cases hout
      · simp only [Out.ev.injEq] at hout
        subst hout
        rcases hsh with h | h
        · exact .inl h
        · exact .inr ⟨trivial, h⟩
  · classical
    let Ex : κ → Nat → Prop := fun c n => ∃ g k pc, ∃ d : (M.code g).D, g < L.threads ∧ key g = c ∧
      Frame.stateAt M.code X g k = some (some d) ∧ X.get (g, k) = some ⟨pc, .exit⟩ ∧
      ((X.tr g).take k).countP isWarpColl = n
    refine ⟨fun c => if h : ∃ n, Ex c n then Nat.find h else
      ((Finset.range L.threads).sup fun g => (X.tr g).countP isWarpColl) + 1, ?_, ?_⟩
    · intro g d hg hσ hd
      by_cases h : ∃ n, Ex (key g) n
      · simp only [h, dite_true]
        obtain ⟨h', k, pc, d', hh, hk, hσ', he, hn⟩ := Nat.find_spec h
        rw [← hn]
        exact (hp (hkey hg hh hk.symm)).exit hσ hd hσ' he
      · simp only [h, dite_false]
        have := Finset.le_sup (f := fun g => (X.tr g).countP isWarpColl) (Finset.mem_range.mpr hg)
        omega
    · intro g k pc d hg hσ he
      have h : ∃ n, Ex (key g) n := ⟨_, g, k, pc, d, hg, rfl, hσ, he, rfl⟩
      simp only [h, dite_true]
      exact Nat.find_min' h ⟨g, k, pc, d, hg, rfl, hσ, he, rfl⟩

end
end PTX.Sched
