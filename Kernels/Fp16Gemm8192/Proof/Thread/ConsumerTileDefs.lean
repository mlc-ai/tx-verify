-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ClcSites
public import Lemmas.Flow.RoundTrip
public import Lemmas.Flow.Polls

@[expose] public section

/-! # The tile of a consumer's task, as the trace shows it

A consumer's tasks are numbered by its successful response polls (`epoch`). Its first task is its
CTA's own tile; task `E > 0` is the tile of the CTA named by the response it read right after its
poll numbered `E - 1` (`TileAt`, `ReadClaim`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Flow

noncomputable section

namespace Consumer

/-- The CTA named by the response a consumer read right after its successful response poll
numbered `E` (`Loader.none32` when it names none). -/
def ReadClaim (L : Launch) (g : Nat) (es : List Event) (E x : Nat) : Prop :=
  ∃ j pc p acq sc pcr, ∃ a : Acc, ∃ bs rr,
    es[j]? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ ∧
    okPolls (clcResp L g) (es.take j) = E ∧ es[j + 1]? = some ⟨pcr, .rd a bs⟩ ∧
    Flow.responseOf bs = some rr ∧ x = (rr.firstCta.map fun c => c.1.toNat).getD Loader.none32

/-- The tile `(m, n)` of a consumer's task `E`: its CTA's own for the first task, the claimed CTA's
for a later one. -/
def TileAt (L : Launch) (g : Nat) (es : List Event) (E m n : Nat) : Prop :=
  (E = 0 ∧ m = Loader.claimM (g / L.block) ∧ n = Loader.claimN (g / L.block)) ∨
    ∃ x, 0 < E ∧ ReadClaim L g es (E - 1) x ∧ x ≠ Loader.none32 ∧ m = Loader.claimM x ∧
      n = Loader.claimN x

theorem ReadClaim.snoc {L : Launch} {g : Nat} {es : List Event} {E x : Nat}
    (h : ReadClaim L g es E x) (e : Event) :
    ReadClaim L g (es ++ [e]) E x := by
  obtain ⟨j, pc, p, acq, sc, pcr, a, bs, rr, hj, hc, hj1, hr, hx⟩ := h
  have hl : j + 1 < es.length := (List.getElem?_eq_some_iff.mp hj1).1
  refine ⟨j, pc, p, acq, sc, pcr, a, bs, rr, ?_, ?_, ?_, hr, hx⟩
  · rw [List.getElem?_append_left (by omega)]; exact hj
  · rw [List.take_append_of_le_length (by omega)]; exact hc
  · rw [List.getElem?_append_left hl]; exact hj1

theorem TileAt.snoc {L : Launch} {g : Nat} {es : List Event} {E m n : Nat}
    (h : TileAt L g es E m n) (e : Event) :
    TileAt L g (es ++ [e]) E m n := by
  rcases h with h | ⟨x, hE, hr, hx, hm, hn⟩
  · exact .inl h
  · exact .inr ⟨x, hE, hr.snoc e, hx, hm, hn⟩

/-- A response read after the poll numbered `E` leaves more than `E` successful polls. -/
theorem ReadClaim.lt {L : Launch} {g : Nat} {es : List Event} {E x : Nat}
    (h : ReadClaim L g es E x) :
    E < okPolls (clcResp L g) es := by
  obtain ⟨j, pc, p, acq, sc, pcr, a, bs, rr, hj, hc, -, -, -⟩ := h
  have hl : j < es.length := (List.getElem?_eq_some_iff.mp hj).1
  have hsub := List.Sublist.countP_le (p := okPoll (clcResp L g))
    (List.take_sublist_take_left (l := es) (show j + 1 ≤ es.length by omega))
  rw [List.take_length] at hsub
  rw [List.take_add_one, hj, Option.toList_some, List.countP_append] at hsub
  simp only [List.countP_singleton] at hsub
  rw [okPoll_wait rfl] at hsub
  simp only [Bool.true_and, decide_true, ↓reduceIte] at hsub
  unfold okPolls at hc ⊢
  omega

/-- A consumer's task: its successful response polls, less the one its task holds. -/
def epoch (L : Launch) (g : Nat) (d : D) (es : List Event) : Nat :=
  okPolls (clcResp L g) es - if d.site = .clcWait then 0 else 1

/-- The sites from the response's queries to the task's commit, holding the claimed CTA. -/
def D.afterQuery (d : D) : Bool := match d.site with
  | .clcFence | .clcBar | .ack | .accWait | .load _ | .loadWait _ | .accArrive | .drain _
  | .barA _ | .store .. | .barB _ | .fence _ | .tma _ | .commit _ => true
  | _ => false

/-- The sites from the group barrier to the task's commit, holding the next tile. -/
def D.afterBar (d : D) : Bool := match d.site with
  | .accWait | .load _ | .loadWait _ | .accArrive | .drain _ | .barA _ | .store .. | .barB _
  | .fence _ | .tma _ | .commit _ => true
  | _ => false

end Consumer

end

end PTX.Kernels.Fp16Gemm8192.Proof
