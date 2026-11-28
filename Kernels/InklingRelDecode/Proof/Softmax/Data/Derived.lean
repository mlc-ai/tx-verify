-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.Cross
public import Kernels.InklingRelDecode.Gen.SoftmaxEntry
public import Lemmas.Flow.PhaseTableJump
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section

/-! # The constants the softmax's setup code derives from the launch

Before the loop the thread computes, from its thread index and the words past the first token, the
words the mask reads: the lane's half of the head (`p1`, `p2`, registers 1 and 2), the lane's
column offset (register 1956) and the 32 pairs of column positions (registers 1961 to 1992). Four
generated runs (`Gen/SoftmaxEntry`) compute them, one after the other: each run's start facts are
the previous runs' facts (`G0` to `G4`, a fact list with the newest first). `derV` is the value of
each register in the last list. The entry (`bar0`) and the last preload (`pre 63`) stop in a loop
site after the runs; the table `tk` lists, for each position of that path, the registers whose
facts hold there. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control

set_option maxRecDepth 100000
noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

/-- The facts before the first run: the thread index, the query length, the words past and the
scale parameter (registers 462, 481, 482 and 525). -/
def G0 (e : Entry) (L : Launch) (g : Nat) : List (Nat × Value) :=
  [(462, b32 (g % L.block)), (481, b32 e.qlen), (482, e.prior), (525, scaleVal L)]

def G1 (e : Entry) (L : Launch) (g : Nat) : List (Nat × Value) :=
  Gen.en_facts1 (lookupD (G0 e L g)) ++ G0 e L g

def G2 (e : Entry) (L : Launch) (g : Nat) : List (Nat × Value) :=
  Gen.dv_facts1 (lookupD (G1 e L g)) ++ G1 e L g

def G3 (e : Entry) (L : Launch) (g : Nat) : List (Nat × Value) :=
  Gen.e8_facts1 (lookupD (G2 e L g)) ++ G2 e L g

def G4 (e : Entry) (L : Launch) (g : Nat) : List (Nat × Value) :=
  Gen.ng_facts1 (lookupD (G3 e L g)) ++ G3 e L g

def G5 (e : Entry) (L : Launch) (g : Nat) : List (Nat × Value) :=
  Gen.ie_facts1 (lookupD (G4 e L g)) ++ G4 e L g

def G6 (e : Entry) (L : Launch) (g : Nat) : List (Nat × Value) :=
  Gen.io_facts3 (lookupD (G5 e L g)) ++ G5 e L g

/-- **The derived constants**: the value of each register after the six runs. -/
def derV (e : Entry) (L : Launch) (g : Nat) : Nat → Value := lookupD (G6 e L g)

/-- The registers of the facts before the loop's first preload: the lane's half of the head
(1, 2), the token offset (496), the column offsets (798, 1956), the scale word (498) and the
reciprocal of the scale (805). -/
def keysB : List Nat := [1, 2, 496, 798, 1956, 498, 805]

/-- The registers of the loop: the halves, the column offset, the negated scale word (499) and
the 33 pairs of positions, the first the reciprocal of the scale twice. -/
def keysC : List Nat := [1, 2, 1956, 499] ++ (List.range 33).map (1960 + ·)

/-- The facts of a site: none before the preloads and at the end, `keysB` in the preloads. -/
def derF (e : Entry) (L : Launch) (g : Nat) : Site → List (Nat × Value)
  | .setMaxReg | .bar0 | .epilogue => []
  | .pre _ => factsFrom keysB (derV e L g)
  | _ => factsFrom keysC (derV e L g)

/-! ### The lists' lookups -/

theorem lookup_app_left : ∀ {F G : List (Nat × Value)} {r : Nat} {v : Value},
    F.lookup r = some v → (F ++ G).lookup r = some v
  | [], _, _, _, h => by simp [List.lookup] at h
  | (q, w) :: F, G, r, v, h => by
    by_cases hq : r = q
    · simpa [List.lookup, hq] using h
    · have hb : (r == q) = false := by simpa using hq
      simp only [List.cons_append, List.lookup, hb] at h ⊢
      exact lookup_app_left (F := F) (G := G) h

theorem lookup_app_right : ∀ {F G : List (Nat × Value)} {r : Nat}, r ∉ F.map Prod.fst →
    (F ++ G).lookup r = G.lookup r
  | [], _, _, _ => rfl
  | (q, w) :: F, G, r, h => by
    have hq : r ≠ q := fun e => h (by simp [e])
    have hb : (r == q) = false := by simpa using hq
    simp only [List.cons_append, List.lookup, hb]
    exact lookup_app_right (F := F) (G := G) (fun e => h (by simp [e]))

/-- A fact list on top of another: its registers read through it. -/
theorem holds_head {R : Nat → Option Value} {F G : List (Nat × Value)} {K live : List Nat}
    (hK : F.map Prod.fst = K) (h : Holds R F) (hl : live.all (fun r => K.contains r) = true) :
    Holds R (factsFrom live (lookupD (F ++ G))) := by
  refine holds_of_pointwise fun r hr => ?_
  have hk : r ∈ F.map Prod.fst := by simpa [hK] using List.all_eq_true.mp hl r hr
  obtain ⟨v, hv⟩ := lookup_some hk
  rw [show lookupD (F ++ G) r = v by simp [lookupD, lookup_app_left hv]]
  exact lookup_holds h hv

/-- A fact list under another: the registers the top does not list read through to it. -/
theorem holds_tail {R : Nat → Option Value} {F G : List (Nat × Value)} {K live : List Nat}
    (hK : F.map Prod.fst = K) (h : Holds R (factsFrom live (lookupD (F ++ G))))
    (hl : live.all (fun r => !K.contains r) = true) :
    Holds R (factsFrom live (lookupD G)) := by
  refine holds_of_pointwise fun r hr => ?_
  have hk : r ∉ F.map Prod.fst := by simpa [hK] using List.all_eq_true.mp hl r hr
  have := holds_mem h (mem_factsFrom (val := lookupD (F ++ G)) hr)
  simpa [lookupD, lookup_app_right hk] using this

/-- The converse: facts read from the lower list read the same through the top that lists none
of them. -/
theorem holds_up {R : Nat → Option Value} {F G : List (Nat × Value)} {K live : List Nat}
    (hK : F.map Prod.fst = K) (h : Holds R (factsFrom live (lookupD G)))
    (hl : live.all (fun r => !K.contains r) = true) :
    Holds R (factsFrom live (lookupD (F ++ G))) := by
  refine holds_of_pointwise fun r hr => ?_
  have hk : r ∉ F.map Prod.fst := by simpa [hK] using List.all_eq_true.mp hl r hr
  have := holds_mem h (mem_factsFrom (val := lookupD G) hr)
  simpa [lookupD, lookup_app_right hk] using this

/-! ### A run as a jump of the table -/

/-- **A generated run is a jump**: from a state with the run's start facts and facts `H` that its
code does not write, local steps reach a state at the run's end with its facts and `H`. -/
theorem jump_gen {n s b : Nat} {F G H : List (Nat × Value)} {C : Prop} {ins : List Instr}
    (seg : SegD kernel Assumptions.all L g n s F b G C) (hcode : (kernel.code.drop s).take n = ins)
    (hlen : ins.length = n) (hB : frameB ins (H.map Prod.fst) = true)
    (hS : ∀ i < n, Assumption.SegFreePc Assumptions.all (s + i)) (hne : s ≠ b) {t : TState}
    (ht : At t s (F ++ H)) :
    (∃ w, Relation.ReflTransGen (Tau kernel Assumptions.all L g) t w ∧ t ≠ w ∧
      At w b (G ++ H)) ∨ Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) t := by
  have h := SegD.frame Lib.rulesFrame seg hcode hlen hB hS t ht
  by_cases hC : C
  · obtain ⟨w, hr, hw⟩ := h.1 hC
    refine .inl ⟨w, run_rtg hr, fun e => hne ?_, hw⟩
    rw [← ht.1, e, hw.1]
  · exact .inr (h.2 hC)

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
