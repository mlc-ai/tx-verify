-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SegDead
public import Lemmas.Register.RegisterFrame

@[expose] public section

namespace PTX.Flow

open PTX.Proof

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- A segment specified only on paths that continue to its endpoint. -/
def SegU (K : Kernel) (A : List Assumption) (L : Launch) (g s : Nat)
    (F : List (Nat × Value)) (b : Nat) (G : List (Nat × Value)) : Prop :=
  ∀ t, At t s F → (∃ u, Relation.ReflTransGen (Tau K A L g) t u ∧ At u b G) ∨
    Machine.Dead (K := K) (A := A) (L := L) (g := g) t

variable {a b c n : Nat} {F G H : List (Nat × Value)}

theorem SegU.of_seg (h : Seg K A L g n a F b G) : SegU K A L g a F b G := by
  intro t ht
  obtain ⟨u, hr, hu⟩ := h t ht
  exact .inl ⟨u, run_rtg hr, hu⟩

theorem SegU.comp (h : SegU K A L g a F b G) (h' : SegU K A L g b G c H) :
    SegU K A L g a F c H := by
  intro t ht
  rcases h t ht with ⟨u, hr, hu⟩ | hd
  · rcases h' u hu with ⟨s, hr', hs⟩ | hd
    · exact .inl ⟨s, hr.trans hr', hs⟩
    · exact .inr (dead_of_rtg hr hd)
  · exact .inr hd

namespace Havoc

/-- The landing PC and clobbered registers of a successful assumption segment. -/
structure Hook where
  stop : Nat
  writes : List Nat

/-- A sparse table accounts for any assumption selecting a segment at a scalar boundary. -/
def Hooks (A : List Assumption) (L : Launch) (g : Nat) (tab : Nat → Option Hook) : Prop :=
  ∀ t a u, t.sub = 0 → t.acc = [] → a ∈ A → a.segmentRule L g t = some (.ok u) →
    ∃ h, tab t.pc = some h ∧ u.pc = h.stop ∧ u.sub = 0 ∧ u.acc = [] ∧ u.fault = t.fault ∧
      ∀ r, r ∉ h.writes → u.regs r = t.regs r

def straight : Op → Bool
  | .bra .. | .brx .. => false
  | _ => true

private theorem lands {op : Op} {t u : TState} (hs : straight op = true)
    (h : LocalFrame op t u) : u.pc = t.pc + 1 := by
  rcases h.pc with h | h
  · unfold nextPc at h
    split at h
    · cases hs
    · exact h
  · unfold BrxTarget at h
    split at h
    · cases hs
    · exact h.elim

/-- Check a decoded stretch in one pass, including hook endpoints and write footprints. -/
def check (tab : Nat → Option Hook) (keep : List Nat) (a b : Nat) (ops : List Instr) : Bool :=
  (ops.zipIdx a).all fun (ins, pc) =>
    ins.guard.isNone && ins.op.isLocal && straight ins.op &&
      (writesRegs ins.op).all (fun r => !keep.contains r) &&
      match tab pc with
      | none => true
      | some h => pc < h.stop && h.stop ≤ b && h.writes.all (fun r => !keep.contains r)

private theorem localFrameOfRule (hA : RulesFrame A) {t u : TState} {op : Op}
    (h : execLocalRule A L g t op = .ok u) : LocalFrame op t u := by
  unfold execLocalRule at h
  split at h
  · rename_i v hv
    obtain ⟨a, ha, hr⟩ := List.exists_of_findSome?_eq_some hv
    exact hA a ha L g t op u (h ▸ hr)
  · exact execLocal_frame h

/-- A successful hook may skip several instructions, but must land inside the checked stretch.
The carry flag is unconstrained at a scalar boundary, as in `At`. -/
theorem cross {tab : Nat → Option Hook} {keep : List Nat} (hA : RulesFrame A)
    (hh : Hooks A L g tab) (hlen : b ≤ K.code.length)
    (hc : check tab keep a b ((K.code.drop a).take (b-a)) = true)
    {t : TState} (ha : a ≤ t.pc) (hb : t.pc ≤ b) (ht : At t t.pc []) :
    (∃ u, Relation.ReflTransGen (Tau K A L g) t u ∧ At u b [] ∧
      ∀ r ∈ keep, u.regs r = t.regs r) ∨ Machine.Dead (K := K) (A := A) (L := L) (g := g) t := by
  by_cases he : t.pc = b
  · exact .inl ⟨t, .refl, he ▸ ht, fun _ _ => rfl⟩
  have hlt : t.pc < b := by omega
  let ins := K.code[t.pc]'(by omega)
  have hcode : K.code[t.pc]? = some ins := List.getElem?_eq_getElem (by omega)
  have hm : (ins, t.pc) ∈ (((K.code.drop a).take (b-a)).zipIdx a) := by
    apply List.mk_mem_zipIdx_iff_le_and_getElem?_sub.mpr
    refine ⟨ha, ?_⟩
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le ha]
    exact hcode
  obtain ⟨⟨⟨⟨hguard, hl⟩, hs⟩, hw⟩, hhook⟩ := by
    simpa only [Bool.and_eq_true] using List.all_eq_true.mp hc _ hm
  have hg := Option.isNone_iff_eq_none.mp hguard
  have hcode' : K.code[t.pc]? = some ⟨none, ins.op⟩ := by
    rw [hcode, ← hg]
  cases hex : execLocalA A L g t ins.op with
  | error f => exact .inr (dead_of_error hcode' hl ht.2.2.2.1 hex)
  | ok u =>
    have tau := tau_of_ok hcode' hl ht.2.2.2.1 hex
    have step : t.pc < u.pc ∧ u.pc ≤ b ∧ At u u.pc [] ∧ ∀ r ∈ keep, u.regs r = t.regs r := by
      unfold execLocalA at hex
      split at hex
      · rename_i v hv
        obtain ⟨asmp, ham, hr⟩ := List.exists_of_findSome?_eq_some hv
        obtain ⟨h, htab, hpc, hsub, hacc, hf, hreg⟩ :=
          hh t asmp u ht.2.1 ht.2.2.1 ham (hex ▸ hr)
        simp only [htab, Bool.and_eq_true, decide_eq_true_eq] at hhook
        exact ⟨hpc ▸ hhook.1.1, hpc ▸ hhook.1.2, ⟨rfl, hsub, hacc, hf.trans ht.2.2.2.1, trivial⟩,
          fun r hr => hreg r (fun hw => by
            have hn := List.all_eq_true.mp hhook.2 r hw
            simp only [List.contains_iff_mem.mpr hr, Bool.not_true, Bool.false_eq_true] at hn)⟩
      · have frame := localFrameOfRule hA hex
        have hpc := lands hs frame
        refine ⟨by omega, by omega, ⟨rfl, frame.sub.trans ht.2.1, frame.acc.trans ht.2.2.1,
          frame.fault.trans ht.2.2.2.1, trivial⟩, fun r hr => frame.regs r ?_⟩
        intro hm
        have h := List.all_eq_true.mp hw r hm
        simp only [List.contains_iff_mem.mpr hr, Bool.not_true, Bool.false_eq_true] at h
    obtain ⟨hp, hub, hu, hr⟩ := step
    rcases cross hA hh hlen hc (ha.trans hp.le) hub hu with ⟨s, hl', hs', hr'⟩ | hd
    · exact .inl ⟨s, .head tau hl', hs', fun r h => (hr' r h).trans (hr r h)⟩
    · exact .inr (Machine.dead_of_tau tau hd)
termination_by b - t.pc
decreasing_by omega

end Havoc

/-- Carry selected input facts over the checked stretch. -/
theorem SegU.of_havoc {tab : Nat → Option Havoc.Hook} (hA : RulesFrame A)
    (hh : Havoc.Hooks A L g tab) (hab : a ≤ b) (hlen : b ≤ K.code.length)
    (hc : Havoc.check tab (G.map Prod.fst) a b ((K.code.drop a).take (b-a)) = true)
    (hG : ∀ p ∈ G, p ∈ F) : SegU K A L g a F b G := by
  intro t ht
  rcases Havoc.cross hA hh hlen hc ht.1.ge (ht.1 ▸ hab)
      ⟨rfl, ht.2.1, ht.2.2.1, ht.2.2.2.1, trivial⟩ with ⟨u, hl, hu, hr⟩ | hd
  · refine .inl ⟨u, hl, At.mono hu ?_⟩
    have keep (p) (hp : p ∈ G) : u.regs p.1 = some p.2 := by
      rw [hr _ (List.mem_map_of_mem hp)]
      exact holds_mem ht.2.2.2.2 (hG p hp)
    clear hr hc hG
    induction G with
    | nil => trivial
    | cons p ps ih =>
      exact ⟨keep p List.mem_cons_self, ih (fun x hx => keep x (List.mem_cons_of_mem _ hx))⟩
  · exact .inr hd
end PTX.Flow
