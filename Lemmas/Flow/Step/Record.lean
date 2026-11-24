-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.Combinators
public import Lemmas.Flow.MemTmpl

@[expose] public section

/-! # Step combinators of recording sites

A proof tool, in the form of `Step/Combinators.lean`, for sites whose machine records what the
event returned and decides its successor from it. The successor is a function of the value: a
state (`some (some d')`), the end of the thread's run before its next event, where a local
instruction faults on the value (`none`, with `Machine.Dead`), or, if the role chooses, no
followed state (`some none`).

* `fires_nc`: a weak global `.nc` load is a `readNC` event whose bytes the continuation
  rebuilds.
* `step_nc_sel`: a scalar `.nc` load.
* `step_nc_first`, `step_nc_last_sel`: the two elements of a two-element `.nc` load; the first
  keeps the thread at the instruction with its value in the accumulator.
* `step_shfl_valid`: a shuffle that writes the received value and its validity predicate. -/

namespace PTX.Flow.Code
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- A weak global `.nc` load that fires is a `readNC` event whose bytes its continuation
reassembles. -/
theorem fires_nc {t u : TState} {a : MemAccess} {e : Event} {base w : Nat}
    (hk : a.kind = .load) (hnc : a.nc = true) (hr : a.rule = some .threadAccess)
    (hs : a.locSpace? = some .global) (hb : a.addr.base = .reg base w) (hsw : a.sem = .weak)
    (hnl : A.any (·.ncLoads t.pc) = true)
    (hf : Fires t.pc (eventTmpl A L g t (.mem a)) e (some u)) :
    ∃ loc bs, bs.length = a.elem.width / 8 ∧ e = ⟨t.pc, .nc loc bs⟩ ∧
      u = afterLoad t a.regs bs := by
  rw [eventTmpl, memTmpl_direct_weakLoad (sp := .global) hr hs hb hk hsw] at hf
  unfold loadTmpl at hf
  split at hf
  · simp only [Fires] at hf
    exact absurd hf.2 (by simp)
  · rename_i a' heff
    have hsz : a'.size = a.elem.width / 8 := by
      cases h1 : effAddr L g t .global base a.addr.off <;>
        simp only [h1, bind, Except.bind, reduceCtorEq] at heff
      unfold elemAcc at heff
      split_ifs at heff
      cases heff
      rfl
    rw [hnc] at hf
    have hcond : (Space.global = Space.global ∧ (A.any fun x => x.ncLoads t.pc) = true) :=
      ⟨rfl, hnl⟩
    rw [ite_eq_left hcond] at hf
    obtain ⟨bs, hlen, he, hu⟩ := hf
    exact ⟨_, bs, hlen.trans hsz, he, Option.some.inj hu⟩

/-- The access conditions under which `fires_nc` inverts a `.nc` load. -/
structure NcLoad (A : List Assumption) (pc : Nat) (a : MemAccess) : Prop where
  kind : a.kind = .load
  nc : a.nc = true
  rule : a.rule = some .threadAccess
  space : a.locSpace? = some .global
  base : ∃ b w, a.addr.base = .reg b w
  sem : a.sem = .weak
  allowed : A.any (·.ncLoads pc) = true

theorem NcLoad.fires {pc : Nat} {t u : TState} {a : MemAccess} {e : Event} (h : NcLoad A pc a)
    (hpc : t.pc = pc) (hf : Fires pc (eventTmpl A L g t (.mem a)) e (some u)) :
    ∃ loc bs, bs.length = a.elem.width / 8 ∧ e = ⟨pc, .nc loc bs⟩ ∧
      u = afterLoad t a.regs bs := by
  obtain ⟨b, w, hb⟩ := h.base
  subst hpc
  exact fires_nc h.kind h.nc h.rule h.space hb h.sem h.allowed hf

/-- Where a recording site's successor is a function `nv` of what it returned. -/
theorem cont_sel {d : C.D} {e : Event} {u : TState} {s : Nat} {F : List (Nat × Value)}
    {o : Option (Option C.D)} (hi : C.inv d) (hn : C.next d e = o) (hu : At u s F)
    (hdead : o = none → Machine.Dead (K := K) (A := A) (L := L) (g := g) u)
    (hl : ∀ d', o = some (some d') → C.Lands d s F d') : C.Cont d e u := by
  rcases o with _ | _ | d'
  · exact .inr ⟨hn, hdead rfl⟩
  · exact .inl (.inl hn)
  · exact (hl d' rfl).cont hi hn hu

/-- A scalar `.nc` load into register `r` whose machine's successor is a function `nv` of the
value read. Bytes that do not rebuild fault the thread (`next = none`). -/
theorem step_nc_sel {d : C.D} {nv : Value → Option (Option C.D)} {gd : Option (Nat × Bool)}
    {a : MemAccess} {r : Nat} (hc0 : K.code[C.pc d]? = some ⟨gd, .mem a⟩)
    (hnc : NcLoad A (C.pc d) a) (hregs : a.regs = [r]) (hr : ∀ q ∈ C.facts d, q.1 ≠ r)
    (hok : ∀ x bs v, rebuild 3 bs = .ok v → C.next d ⟨C.pc d, .nc x bs⟩ = nv v)
    (herr : ∀ x bs f, rebuild 3 bs = .error f →
      C.next d ⟨C.pc d, .nc x bs⟩ = none ∨ C.next d ⟨C.pc d, .nc x bs⟩ = some none)
    (hs : C.sub d = 0) (ha : C.acc d = [])
    (hdead : ∀ v u, v.bytes = a.elem.width / 8 → nv v = none →
      At u (C.pc d + 1) ((r, v) :: C.facts d) → Machine.Dead (K := K) (A := A) (L := L) (g := g) u)
    (hl : ∀ v d', v.bytes = a.elem.width / 8 → nv v = some (some d') →
      C.Lands d (C.pc d + 1) ((r, v) :: C.facts d) d') :
    C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  have h0 := at_of_atD h hs ha
  obtain ⟨x, bs, hlen, rfl, rfl⟩ := hnc.fires h.1 hf
  rw [hregs]
  cases hv : rebuild 3 bs with
  | error f =>
    rcases herr x bs f hv with hn | hn
    · exact .inr ⟨hn, Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])⟩
    · exact .inl (.inl hn)
  | ok v =>
    have hst : { setReg t r v with pc := t.pc + 1, sub := 0, acc := [] } =
        PTX.next (setReg t r v) := by
      have hs0 := h0.2.1
      have ha0 := h0.2.2.1
      cases t
      simp_all [PTX.next, setReg]
    rw [afterLoad_ok h0.2.1 h0.2.2.1 hv, hst]
    have hb := (rebuild_bytes_eq_length 3 bs v hv).trans hlen
    have hu := At.set (v := v) h0 hr
    exact cont_sel hi (hok x bs v hv) hu (fun hn => hdead v _ hb hn hu) (hl v · hb)

/-- The first element of a two-element `.nc` load: the thread stays at the instruction with the
value in its accumulator, at the state `dn v`. -/
theorem step_nc_first {d : C.D} {dn : Value → C.D} {gd : Option (Nat × Bool)} {a : MemAccess}
    {r0 r1 : Nat} (hc0 : K.code[C.pc d]? = some ⟨gd, .mem a⟩) (hnc : NcLoad A (C.pc d) a)
    (hregs : a.regs = [r0, r1])
    (hok : ∀ x bs v, rebuild 3 bs = .ok v → C.next d ⟨C.pc d, .nc x bs⟩ = some (some (dn v)))
    (herr : ∀ x bs f, rebuild 3 bs = .error f →
      C.next d ⟨C.pc d, .nc x bs⟩ = none ∨ C.next d ⟨C.pc d, .nc x bs⟩ = some none)
    (hs : C.sub d = 0) (ha : C.acc d = [])
    (hpc : ∀ v, C.pc (dn v) = C.pc d) (hsub : ∀ v, C.sub (dn v) = 1)
    (hacc : ∀ v, C.acc (dn v) = [v]) (hF : ∀ v, C.facts (dn v) = C.facts d)
    (hinv : ∀ v, v.bytes = a.elem.width / 8 → C.inv d → C.inv (dn v)) : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨x, bs, hlen, rfl, rfl⟩ := hnc.fires h.1 hf
  rw [hregs]
  cases hv : rebuild 3 bs with
  | error f =>
    rcases herr x bs f hv with hn | hn
    · exact .inr ⟨hn, Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])⟩
    · exact .inl (.inl hn)
  | ok v =>
    have hs0 : t.sub = 0 := h.2.1.trans hs
    have ha0 : t.acc = [] := h.2.2.1.trans ha
    have hb := (rebuild_bytes_eq_length 3 bs v hv).trans hlen
    refine .inl (.inr ⟨dn v, _, hok x bs v hv, .refl, ⟨?_, ?_, ?_, ?_, ?_⟩, hinv v hb hi⟩)
    · simp [afterLoad, hv, hs0, h.1, hpc]
    · simp [afterLoad, hv, hs0, hsub]
    · simp [afterLoad, hv, hs0, ha0, hacc]
    · simp [afterLoad, hv, hs0, h.2.2.2.1]
    · simp only [afterLoad, hv, hs0, hF]
      simpa using h.2.2.2.2

/-- The second element of a two-element `.nc` load whose first element `v0` is in the
accumulator: both destinations are written and the thread continues at the next instruction; the
machine's successor is a function `nv` of the second value. -/
theorem step_nc_last_sel {d : C.D} {nv : Value → Option (Option C.D)} {gd : Option (Nat × Bool)}
    {a : MemAccess} {r0 r1 : Nat} {v0 : Value} (hc0 : K.code[C.pc d]? = some ⟨gd, .mem a⟩)
    (hnc : NcLoad A (C.pc d) a) (hregs : a.regs = [r0, r1]) (hr0 : ∀ q ∈ C.facts d, q.1 ≠ r0)
    (hr1 : ∀ q ∈ C.facts d, q.1 ≠ r1) (h01 : r0 ≠ r1)
    (hok : ∀ x bs v, rebuild 3 bs = .ok v → C.next d ⟨C.pc d, .nc x bs⟩ = nv v)
    (herr : ∀ x bs f, rebuild 3 bs = .error f →
      C.next d ⟨C.pc d, .nc x bs⟩ = none ∨ C.next d ⟨C.pc d, .nc x bs⟩ = some none)
    (hs : C.sub d = 1) (ha : C.acc d = [v0])
    (hdead : ∀ v u, v.bytes = a.elem.width / 8 → nv v = none →
      At u (C.pc d + 1) ((r1, v) :: (r0, v0) :: C.facts d) →
      Machine.Dead (K := K) (A := A) (L := L) (g := g) u)
    (hl : ∀ v d', v.bytes = a.elem.width / 8 → nv v = some (some d') →
      C.Lands d (C.pc d + 1) ((r1, v) :: (r0, v0) :: C.facts d) d') : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨x, bs, hlen, rfl, rfl⟩ := hnc.fires h.1 hf
  rw [hregs]
  cases hv : rebuild 3 bs with
  | error f =>
    rcases herr x bs f hv with hn | hn
    · exact .inr ⟨hn, Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])⟩
    · exact .inl (.inl hn)
  | ok v =>
    have hs0 : t.sub = 1 := h.2.1.trans hs
    have ha0 : t.acc = [v0] := h.2.2.1.trans ha
    have hu : At (afterLoad t [r0, r1] bs) (C.pc d + 1) ((r1, v) :: (r0, v0) :: C.facts d) := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [afterLoad, hv, hs0, h.1]
      · simp [afterLoad, hv, hs0]
      · simp [afterLoad, hv, hs0]
      · simp [afterLoad, hv, hs0, ha0, setRegs, setReg, h.2.2.2.1]
      · simp only [afterLoad, hv, hs0, ha0, Nat.reduceAdd, List.length_cons, List.length_nil,
          lt_self_iff_false, ↓reduceIte, List.cons_append, List.nil_append, setRegs]
        refine ⟨by simp [setReg], by simp [setReg, h01], ?_⟩
        exact holds_update (holds_update h.2.2.2.2 hr0) hr1
    have hb := (rebuild_bytes_eq_length 3 bs v hv).trans hlen
    exact cont_sel hi (hok x bs v hv) hu (fun hn => hdead v _ hb hn hu) (hl v · hb)

/-- A shuffle into register `r` and validity predicate `p` whose machine's successor is a
function `nv` of the received value and its validity. -/
theorem step_shfl_valid {d : C.D} {nv : Value → Bool → Option (Option C.D)}
    {gd : Option (Nat × Bool)} {mode : ShflMode} {ty : Option DType} {r p : Nat}
    {a b c mask : Opnd}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .warp ⟨.shfl mode, ty, [some r, some p], [a, b, c],
      some mask⟩⟩)
    (hr : ∀ q ∈ C.facts d, q.1 ≠ r) (hp : ∀ q ∈ C.facts d, q.1 ≠ p) (hrp : r ≠ p)
    (hn : ∀ m av bv cv recv ok, C.next d ⟨C.pc d, .shfl m av bv cv recv ok⟩ = nv recv ok)
    (hs : C.sub d = 0) (ha : C.acc d = [])
    (hdead : ∀ recv ok u, nv recv ok = none →
      At u (C.pc d + 1) ((p, .pred ok) :: (r, recv) :: C.facts d) →
      Machine.Dead (K := K) (A := A) (L := L) (g := g) u)
    (hl : ∀ recv ok d', nv recv ok = some (some d') →
      C.Lands d (C.pc d + 1) ((p, .pred ok) :: (r, recv) :: C.facts d) d') : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  have h0 := at_of_atD h hs ha
  obtain ⟨av, bv, cv, recv, ok, rfl, rfl⟩ := fires_shfl (p := some p) hf
  have h1 : At (setReg t r recv) (C.pc d) ((r, recv) :: C.facts d) :=
    ⟨h0.1, h0.2.1, h0.2.2.1, h0.2.2.2.1, Function.update_self .., holds_update h0.2.2.2.2 hr⟩
  have hp' : ∀ q ∈ (r, recv) :: C.facts d, q.1 ≠ p := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hrp
    · exact hp q hq
  have hu := At.set (v := .pred ok) h1 hp'
  exact cont_sel hi (hn ..) hu (fun hx => hdead recv ok _ hx hu) (hl recv ok)

end
end PTX.Flow.Code
