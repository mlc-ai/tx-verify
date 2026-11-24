-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution
public import Lemmas.Tcgen05.TcCommit
public import Lemmas.Tcgen05.TcFence
public import Lemmas.Tmem.TmemStore

@[expose] public section

section
namespace PTX.TcMma
noncomputable section

/-- An MMA write must complete before any release of a lifetime covering it, unless a
fresh allocation separates them. -/
theorem before_release {L : Launch} {X : Execution}
    (h : Tmem.Pair.AccessSafe L X) {e : EvId} {cell : Cell}
    (he : Tmem.Pair.Access L X e cell) {cta : Nat} {r : Tmem.Pair.Requests}
    (hr : r ∈ X.tmemHistory cta)
    (hc : Tmem.Pair.Covers L X r cell.cta e cell.column) {d : EvId}
    (hd : Tmem.Pair.ReleaseOf L X r d)
    (hn : ¬ Tmem.Pair.FreshAfter L X d e cell.cta cell.column) :
    TcMma.CompletedBefore L X e d :=
  ((h e cell he).2 cta r hr hc d hd).resolve_right hn

end
end PTX.TcMma
end

section
namespace PTX.TcMma
noncomputable section

/-- A full FP32 word carries exactly the ideal result selected by the profile. -/
theorem WordContains.f32 {x : ℝ} {word : Value}
    (h : WordContains (.float .f32 x) word) : word = .float .f32 x := by
  rcases h with h | h
  · exact h.2
  · cases h.1

/-- A full word of a load register is the value its read source wrote. -/
theorem LoadReadOk.f32 {L : Launch} {A : List Assumption} {X : Execution}
    (h : LoadReadOk L A X) {load source : EvId} {address j : Nat} {vals : List Value}
    {sh : TcShape} {cell : Cell} {x : ℝ} (hl : X.TLd load address vals sh)
    (hc : LoadCell L X load j cell) (hs : ReadSource L X .ld source load cell)
    (hw : Wrote L A X source cell (.float .f32 x)) :
    vals[j]? = some (.float .f32 x) := by
  obtain ⟨word, hv, hwc⟩ := h load address vals sh j source cell (.float .f32 x) hl hc hs hw
  rw [WordContains.f32 hwc] at hv
  exact hv

/-- The physical owner is determined by the load, not the MMA issuing thread. -/
theorem LoadCell.owner {L : Launch} {X : Execution} {load : EvId} {j : Nat} {cell : Cell}
    (h : LoadCell L X load j cell) : cell.cta = load.1 / L.block := by
  obtain ⟨a, vs, _, _, _, he⟩ := h
  cases he
  rfl

end
end PTX.TcMma
end
