-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Thread.Cont

@[expose] public section

/-! # The elements of the vector accesses

An element of a vector load that is not the last keeps the value its bytes rebuild to and moves
to the next element; bytes that do not rebuild fault (`step_load_mid`). An element of a vector
store that is not the last moves to the next element (`step_store_mid`). After the last element
of a store the thread is at the next instruction (`store_last`); after the last element of a
load it holds the four values in the destinations (`load_last`). -/

namespace PTX.Kernels.RmsNorm.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

theorem vload_vec {s : Site} (h : s.vload = true) : s.vec = true := by
  cases s <;> simp_all [Site.vload, Site.vec]

/-- **An element of a vector load before the last.** -/
theorem step_load_mid {d : D} {t u : TState} {e : Event} {a : Acc} {ds : List Nat} {pc : Nat}
    {k : List Value → Option D} (hv : d.site.vload = true)
    (hn : ∀ e, next P g d e = loadNext d e k) (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hds : ds.length = 4) (hmid : d.sub + 1 < 4)
    (hf : Fires pc (.read a (afterLoad t ds)) e (some u)) : Cont P L g d e u := by
  obtain ⟨bs, -, rfl, hu⟩ := hf
  cases hu
  cases hb : rebuild 3 bs with
  | error f =>
    exact .inr ⟨by rw [hn]; simp [loadNext, hb], Machine.dead_of_fault (afterLoad_fault hb)⟩
  | ok v =>
    have hsub : t.sub = d.sub := h.2.1
    rw [afterLoad_mid hb (by rw [hsub, hds]; exact hmid)]
    refine .inl ⟨{ d with sub := d.sub + 1, acc := d.acc ++ [v] }, _,
      by rw [hn]; simp [loadNext, hb, hmid], .refl,
      ⟨h.1, congrArg (· + 1) hsub, congrArg (· ++ [v]) h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩, ?_⟩
    have ha := hi.acc
    simp only [hv, ↓reduceIte] at ha
    exact ⟨⟨fun _ => hmid, fun hn' => absurd (vload_vec hv) (by simp [hn'])⟩,
      by simp [hv, ha], hi.row, hi.exit, hi.bfa, hi.bfb, hi.ldws, hi.stts, hi.stws, hi.u, hi.raw⟩

/-- **An element of a vector store before the last.** -/
theorem step_store_mid {d d' : D} {t u : TState} {e : Event} {a : Acc} {bs : List Byte}
    {srcs : List Opnd} {pc : Nat} (hv : d.site.vec = true) (hvl : d.site.vload = false)
    (hn : ∀ e, next P g d e = storeNext d d') (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hsrc : srcs.length = 4) (hmid : d.sub + 1 < 4)
    (hf : Fires pc (.write a bs (afterStore t srcs)) e (some u)) : Cont P L g d e u := by
  obtain ⟨rfl, hu⟩ := hf
  cases hu
  have hsub : t.sub = d.sub := h.2.1
  rw [afterStore_mid (by rw [hsub, hsrc]; exact hmid)]
  refine .inl ⟨{ d with sub := d.sub + 1 }, _, by rw [hn]; simp [storeNext, hmid], .refl,
    ⟨h.1, congrArg (· + 1) hsub, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩, ?_⟩
  have ha := hi.acc
  exact ⟨⟨fun _ => hmid, fun hn' => absurd hv (by simp [hn'])⟩,
    by simpa [hvl] using ha, hi.row, hi.exit, hi.bfa,
    hi.bfb, hi.ldws, hi.stts, hi.stws, hi.u, hi.raw⟩

/-- After the last element of a vector store the thread is at the next instruction. -/
theorem store_last {d : D} {t u : TState} {e : Event} {a : Acc} {bs : List Byte}
    {srcs : List Opnd} {pc : Nat} (h : (code P L g).AtD d t) (hsrc : srcs.length = 4)
    (hlast : d.sub = 3) (hacc : d.acc = []) (hf : Fires pc (.write a bs (afterStore t srcs)) e
      (some u)) :
    e = ⟨pc, .wr a bs⟩ ∧ At u (d.site.pc + 1) (factsAt P g d.site.pc d) := by
  obtain ⟨rfl, hu⟩ := hf
  cases hu
  have hsub : t.sub = d.sub := h.2.1
  rw [afterStore_last (by rw [hsub, hsrc, hlast]; decide)]
  exact ⟨rfl, by simp only [h.1]; rfl, rfl, h.2.2.1.trans hacc, h.2.2.2.1, h.2.2.2.2⟩

/-- The state after the last element of a vector load into `ds` of values `vs`. -/
def afterVec (t : TState) (ds : List Nat) (vs : List Value) : TState :=
  { setRegs t ds vs with pc := t.pc + 1, sub := 0, acc := [] }

/-- After the last element of a vector load: bytes that do not rebuild fault; otherwise the
thread holds the four values in the destinations, at the next instruction. -/
theorem load_last {d : D} {t u : TState} {e : Event} {a : Acc} {ds : List Nat} {pc : Nat}
    {k : List Value → Option D} (hn : ∀ e, next P g d e = loadNext d e k)
    (h : (code P L g).AtD d t) (hds : ds.length = 4) (hlast : d.sub = 3)
    (hf : Fires pc (.read a (afterLoad t ds)) e (some u)) :
    ∃ bs, e = ⟨pc, .rd a bs⟩ ∧
      ((next P g d e = none ∧ Machine.Dead (K := kernel) (A := Prod) (L := L) (g := g) u) ∨
        ∃ v, next P g d e = (k (d.acc ++ [v])).map some ∧
          u = afterVec t ds (d.acc ++ [v])) := by
  obtain ⟨bs, -, rfl, hu⟩ := hf
  cases hu
  refine ⟨bs, rfl, ?_⟩
  cases hb : rebuild 3 bs with
  | error f =>
    exact .inl ⟨by rw [hn]; simp [loadNext, hb], Machine.dead_of_fault (afterLoad_fault hb)⟩
  | ok v =>
    have hsub : t.sub = d.sub := h.2.1
    refine .inr ⟨v, by rw [hn]; simp [loadNext, hb, hlast], ?_⟩
    rw [afterLoad_last hb (by rw [hsub, hds, hlast]; decide)]
    have hacc : t.acc = d.acc := h.2.2.1
    rw [hacc]
    rfl

/-- Facts of registers a step does not write carry over. -/
theorem holds_frame {R R' : Nat → Option Value} {live : List Nat} {v : Nat → Value}
    (h : Holds R (factsFrom live v)) (hfr : ∀ r ∈ live, R' r = R r) :
    Holds R' (factsFrom live v) :=
  holds_of_pointwise fun r hr => (hfr r hr).trans (holds_mem h (mem_factsFrom hr))

end
end PTX.Kernels.RmsNorm.Proof
