-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Interface

@[expose] public section

/-! # The events of the threads, by kind

Every event that is not undefined behaviour fires from a followed state, at the position its
state gives (`event_facts`). The event of a state's site is: a read of the site's footprint
(`rd_site`), a write of the value the state holds (`wr_site`), a barrier of the whole CTA
(`bar_site`), a shuffle of the state's operand (`shfl_site`), or the exit (`exit_site`). -/

namespace PTX.Kernels.RmsNorm.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat} {d : D}

/-- The facts of the state an event fires from. -/
structure At (P : Params) (L : Launch) (X : Execution) (g k : Nat) (d : D) (e : Event) : Prop where
  state : stateAt P L X g k = some (some d)
  event : SiteEvent P g d e
  index : k = d.idx g
  inv : Inv P g d
  data : RowData P g d ((X.tr g).take k)
  bc0 : ((X.tr g).take k).countP (Execution.isBarId 0) = d.bc0
  bc1 : ((X.tr g).take k).countP (Execution.isBarId 1) = d.bc1
  sc : ((X.tr g).take k).countP Execution.isShfl = d.sc g

/-- An event that is not undefined behaviour fires from a followed state. -/
theorem state_of_get (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts P L X) {k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) : ∃ d, stateAt P L X g k = some (some d) :=
  Frame.event_state (fun _ hg => sound hpre hg) hX ht.tracked he hub

/-- **The facts of an event** that is not undefined behaviour. -/
theorem event_facts (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts P L X) {k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) : g < L.threads ∧ ∃ d, At P L X g k d e := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hσ⟩ := state_of_get hpre hX ht he hub
  obtain ⟨h0, h1, h2⟩ := ht.counts hg hσ
  exact ⟨hg, d, hσ, ht.event hg he hσ, ht.index hg (len_of_get he).le hσ, ht.inv hg hσ,
    ht.data hg hσ, h0, h1, h2⟩

/-- Close the case of a site whose event has another form, or read off the event's form. -/
macro "ev_close" hf:ident : tactic => `(tactic| first
  | (obtain ⟨_, _, he, _⟩ := $hf; cases he; done)
  | (obtain ⟨_, _, he, _⟩ := $hf; cases he; simp; done)
  | (obtain ⟨he, _⟩ := $hf; cases he; done)
  | (obtain ⟨he, _⟩ := $hf; cases he; simp; done)
  | rfl)

/-- A read of a site: the footprint of the site's access. -/
theorem rd_site {pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (h : SiteEvent P g d ⟨pc, .rd a bs⟩) :
    (d.site = .ldxa ∧ a = vacc .global 0 (P.I + off g d.i) d.sub) ∨
    (d.site = .ldxb ∧ a = vacc .global 0 (P.I + off g d.i + 4096) d.sub) ∨
    (d.site = .ldws ∧
      a = { loc := ⟨.shared, g / 256, P.S + 4 * (g % 256 % 32) + 16384⟩, size := 4 }) ∨
    (d.site = .ldts ∧ a = { loc := ⟨.shared, g / 256, P.S + 16384⟩, size := 4 }) ∨
    (d.site = .ldwa ∧ a = vacc .global 0 (P.W + 16 * (g % 256)) d.sub) ∨
    (d.site = .ldsa0 ∧ a = vacc .shared (g / 256) (P.S + 32 * (g % 256)) d.sub) ∨
    (d.site = .ldsa1 ∧ a = vacc .shared (g / 256) (P.S + 32 * (g % 256) + 16) d.sub) ∨
    (d.site = .ldwb ∧ a = vacc .global 0 (P.W + 16 * (g % 256) + 4096) d.sub) ∨
    (d.site = .ldsb0 ∧ a = vacc .shared (g / 256) (P.S + 32 * (g % 256) + 8192) d.sub) ∨
    (d.site = .ldsb1 ∧ a = vacc .shared (g / 256) (P.S + 32 * (g % 256) + 8208) d.sub) := by
  obtain ⟨t, o, hf⟩ := h
  rcases hs : d.site <;> simp only [siteTmpl, hs, Fires] at hf <;> ev_close hf

/-- A write of a site: the footprint and the bytes of the value the state holds. -/
theorem wr_site {pc : Nat} {a : Acc} {bs : List Byte} (h : SiteEvent P g d ⟨pc, .wr a bs⟩) :
    (d.site = .stxa0 ∧ a = vacc .shared (g / 256) (P.S + 32 * (g % 256)) d.sub ∧
      bs = (xw d.xa d.sub).toBytes) ∨
    (d.site = .stxa1 ∧ a = vacc .shared (g / 256) (P.S + 32 * (g % 256) + 16) d.sub ∧
      bs = (xw d.xa (4 + d.sub)).toBytes) ∨
    (d.site = .stxb0 ∧ a = vacc .shared (g / 256) (P.S + 32 * (g % 256) + 8192) d.sub ∧
      bs = (xw d.xb d.sub).toBytes) ∨
    (d.site = .stxb1 ∧ a = vacc .shared (g / 256) (P.S + 32 * (g % 256) + 8208) d.sub ∧
      bs = (xw d.xb (4 + d.sub)).toBytes) ∨
    (d.site = .stws ∧
      a = { loc := ⟨.shared, g / 256, P.S + 4 * (g % 256 / 32) + 16384⟩, size := 4 } ∧
      bs = (bsumV (ssqV d) d.ra 5).toBytes) ∨
    (d.site = .stts ∧ a = { loc := ⟨.shared, g / 256, P.S + 16384⟩, size := 4 } ∧
      bs = (bsumV d.u d.rb 5).toBytes) ∨
    (d.site = .stoa ∧ a = vacc .global 0 (P.O + off g d.i) d.sub ∧
      bs = (outV d.raw d.rs0 d.rs1 (cpair d.tt) d.sub).toBytes) ∨
    (d.site = .stob ∧ a = vacc .global 0 (P.O + off g d.i + 4096) d.sub ∧
      bs = (outV d.raw d.rs0 d.rs1 (cpair d.tt) d.sub).toBytes) := by
  obtain ⟨t, o, hf⟩ := h
  rcases hs : d.site <;> simp only [siteTmpl, hs, Fires] at hf <;> ev_close hf

/-- A barrier of a site: barrier `0` of the whole CTA at the first two, barrier `1` at the
third. -/
theorem bar_site {pc id : Nat} {c : Option Nat} (h : SiteEvent P g d ⟨pc, .bar id c⟩) :
    c = none ∧
      ((d.site = .bar0 ∧ id = 0) ∨ (d.site = .bar1 ∧ id = 0) ∨ (d.site = .bar2 ∧ id = 1)) := by
  obtain ⟨t, o, hf⟩ := h
  rcases hs : d.site <;> simp only [siteTmpl, hs, Fires] at hf <;> ev_close hf

/-- A shuffle of a site: the warp-index shuffle, or a butterfly round of the state's operand. -/
theorem shfl_site {pc : Nat} {m : ShflMode} {a : Value} {b c : Nat} {recv : Value} {ok : Bool}
    (h : SiteEvent P g d ⟨pc, .shfl m a b c recv ok⟩) :
    (d.site = .shfl0 ∧ m = .idx ∧ a = b32 (g % 256 / 32) ∧ b = 0 ∧ c = 31) ∨
    (∃ k, d.site = .bfa k ∧ m = .bfly ∧ a = bsumV (ssqV d) d.ra k ∧ b = bfOff k ∧ c = 31) ∨
    (∃ k, d.site = .bfb k ∧ m = .bfly ∧ a = bfbOp d k ∧ b = bfOff k ∧ c = 31) := by
  obtain ⟨t, o, hf⟩ := h
  rcases hs : d.site <;> simp only [siteTmpl, hs, Fires] at hf <;> ev_close hf

/-- No site performs an atomic read-modify-write. -/
theorem rmw_site {pc : Nat} {a : Acc} {o : List (Option Byte)} {n : Option (List Byte)}
    (h : SiteEvent P g d ⟨pc, .rmw a o n⟩) : False := by
  obtain ⟨t, o', hf⟩ := h
  rcases hs : d.site <;> simp only [siteTmpl, hs, Fires] at hf <;> ev_close hf

/-- No site issues an asynchronous copy. -/
theorem copy_site {pc : Nat} {s : AsyncCopy.Spec} (h : SiteEvent P g d ⟨pc, .copy s⟩) : False := by
  obtain ⟨t, o', hf⟩ := h
  rcases hs : d.site <;> simp only [siteTmpl, hs, Fires] at hf <;> ev_close hf

/-- The event of the exit site is the exit. -/
theorem exit_site_of {e : Event} (h : SiteEvent P g d e) (hs : d.site = .exit) :
    ∃ pc, e = ⟨pc, .exit⟩ := by
  obtain ⟨t, o, hf⟩ := h
  simp only [siteTmpl, hs, Fires] at hf
  exact ⟨_, hf.1⟩

/-- The exit of a site. -/
theorem exit_site {pc : Nat} (h : SiteEvent P g d ⟨pc, .exit⟩) : d.site = .exit := by
  obtain ⟨t, o, hf⟩ := h
  rcases hs : d.site <;> simp only [siteTmpl, hs, Fires] at hf <;> ev_close hf

end
end PTX.Kernels.RmsNorm.Proof
