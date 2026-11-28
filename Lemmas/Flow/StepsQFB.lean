-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StepsQF
public import Lemmas.Flow.StepsQLdW

@[expose] public section

/-! # Strict loads and shuffles under the float tag invariant

The twins of `StepsQ.lean`'s `shflAnyQ` and `ldvNcQ` and of `StepsQLdW.lean`'s `ldWQ` for
`QTF qt`. -/

namespace PTX.Flow.Code
open PTX.Proof PTX.Flow.Havoc PTX.Flow.Tagged PTX.Flow.TyG

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- A data shuffle under the float tag invariant: the received word is 32 bits (`hW`); it goes
into `r`, the validity into `p`. -/
theorem shflF {qt : Nat → EnvF} {Wf : Event → Prop} {d dn : C.D} {mode : ShflMode}
    {ty : Option DType} {r p : Nat} {a b c mask : Opnd}
    (hc0 : K.code[C.pc d]? = some ⟨none, .warp ⟨.shfl mode, ty, [some r, some p], [a, b, c],
      some mask⟩⟩)
    (hr : ∀ q ∈ C.facts d, q.1 ≠ r) (hp : ∀ q ∈ C.facts d, q.1 ≠ p) (hrp : r ≠ p)
    {tr : TagF} (hW : ∀ e, Wf e → ∀ m av bv cv recv ok, e.kind = .shfl m av bv cv recv ok →
      tr.ok (some recv))
    (hn : ∀ e, C.next d e = some (some dn)) (hs : C.sub d = 0) (ha : C.acc d = [])
    (hs' : C.sub dn = 0) (ha' : C.acc dn = []) (hi : C.inv dn)
    (hq : afterF qt (C.pc d) [(r, tr), (p, .old .pred)] = true)
    (seg : ∀ recv ok, SegQ K A L g (QTF qt) (C.pc d + 1)
      ((p, .pred ok) :: (r, recv) :: C.facts d) (C.pc dn) (C.facts dn)) (e : Event) :
    C.StepForQ (QTF qt) Wf d e := by
  intro t u ins h _ hc hQ hWe hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  have h0 := at_of_atD h hs ha
  obtain ⟨av, bv, cv, recv, ok, rfl, rfl⟩ := fires_shfl (p := some p) hf
  have hy := hW _ hWe _ av bv cv recv ok rfl
  have hat1 : At (setReg t r recv) (C.pc d) ((r, recv) :: C.facts d) :=
    ⟨h0.1, h0.2.1, h0.2.2.1, h0.2.2.2.1, Function.update_self .., holds_update h0.2.2.2.2 hr⟩
  have hp' : ∀ q ∈ (r, recv) :: C.facts d, q.1 ≠ p := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hrp
    · exact hp q hq
  have hu := At.set (v := .pred ok) hat1 hp'
  have hQ' : QTF qt (PTX.next (setReg (setReg t r recv) p (.pred ok))) := by
    refine QTF.after1 hQ h.1 (by show t.pc + 1 = C.pc d + 1; rw [h.1]) (fun r' hl => ?_)
      (fun q hq' => ?_) hq
    · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
        not_or] at hl
      simp [PTX.next, setReg, Function.update_of_ne hl.1, Function.update_of_ne hl.2]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl
      · simpa [PTX.next, setReg, Function.update_of_ne hrp] using hy
      · exact ⟨ok, by simp [PTX.next, setReg]⟩
  obtain ⟨t', hr', hg, hq'⟩ := landQ hu hQ' (seg _ ok) hi hs' ha'
  exact .inl ⟨dn, t', hn _, hr', hg, hq'⟩

/-- A scalar weak load under the float tag invariant. -/
theorem ldWF {qt : Nat → EnvF} {Wf : Event → Prop} {P : Value → Prop} {d : C.D}
    {f : Value → C.D} {a : MemAccess} {r : Nat}
    (hc : K.code[C.pc d]? = some ⟨none, .mem a⟩) (hk : a.kind = .load) (hnc : a.nc = false)
    (hext : a.ext = .same) (hr : a.regs = [r])
    (hW : ∀ e, Wf e → e.pc = C.pc d → ∀ x bs, e.kind = .rd x bs →
      ∃ v, rebuild 3 bs = .ok v ∧ P v)
    (hn : ∀ x bs v, rebuild 3 bs = .ok v → P v →
      C.next d ⟨C.pc d, .rd x bs⟩ = some (some (f v)))
    (hs : C.sub d = 0) (ha : C.acc d = []) (hoff : ∀ p ∈ C.facts d, p.1 ≠ r)
    {tr : TagF} (hv : ∀ v, P v → tr.ok (some v))
    (hq : afterF qt (C.pc d) [(r, tr)] = true)
    (hok : ∀ v, P v → C.sub (f v) = 0 ∧ C.acc (f v) = [] ∧ C.inv (f v) ∧
      SegQ K A L g (QTF qt) (C.pc d + 1) ((r, v) :: C.facts d) (C.pc (f v)) (C.facts (f v)))
    (e : Event) : C.StepForQ (QTF qt) Wf d e := by
  intro t u ins h _ hc' hQ hWe hf
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain ⟨x, bs, rfl, rfl⟩ := fires_load hk hnc hf hext
  obtain ⟨v, hy, hPv⟩ := hW _ hWe (by rw [← h.1]) x bs rfl
  have ht := at_of_atD h hs ha
  rw [hr, afterLoad_ok ht.2.1 ht.2.2.1 hy]
  obtain ⟨hs', ha', hi, seg⟩ := hok v hPv
  obtain ⟨hP, hS0, hA, hFl, hR⟩ := ht
  have hu : At { setReg t r v with pc := t.pc + 1, sub := 0, acc := [] }
      (C.pc d + 1) ((r, v) :: C.facts d) :=
    ⟨by show t.pc + 1 = _; rw [hP], rfl, rfl, hFl, Function.update_self ..,
      holds_update hR hoff⟩
  have hQ' : QTF qt { setReg t r v with pc := t.pc + 1, sub := 0, acc := [] } :=
    QTF.after1 hQ hP (by show t.pc + 1 = C.pc d + 1; rw [hP]) (fun r' hl => by
      simp [setReg, Function.update_of_ne (by simpa using hl)])
      (fun q hq' => by
        simp only [List.mem_singleton] at hq'
        subst hq'
        simpa [setReg] using hv v hPv) hq
  obtain ⟨t', hr', hg, hq'⟩ := landQ hu hQ' seg hi hs' ha'
  exact .inl ⟨f v, t', hn x bs v hy hPv, hr', hg, hq'⟩

/-- An element of a pair of `.nc` loads under the float tag invariant: the payload is a 32-bit
word (`hW`) and the registers `r0 r1` take the tag `tr` of such words (`htr`). -/
theorem ldvNcF {qt : Nat → EnvF} {Wf : Event → Prop} {d : C.D}
    {dok : Value → C.D} {a : MemAccess}
    {live : List Nat} {val : Nat → Value} {base w r0 r1 : Nat} {sp : Space}
    (hc0 : K.code[C.pc d]? = some ⟨none, .mem a⟩) (_hl : (Op.mem a).isLocal = false)
    (hru : a.rule = some .threadAccess) (hloc : a.locSpace? = some sp)
    (hb : a.addr.base = .reg base w) (hk : a.kind = .load) (hsem : a.sem = .weak)
    (hnc : a.nc = true) (hregs : a.regs = [r0, r1])
    (hW : ∀ e, Wf e → ∀ x bs, e.kind = .nc x bs → ∃ y, rebuild 3 bs = .ok (.bits 32 y))
    (hlast : ¬ C.sub d + 1 < 2 → ∃ y0, C.acc d = [.bits 32 y0])
    (hok : ∀ x bs v, rebuild 3 bs = .ok v → C.next d ⟨C.pc d, .nc x bs⟩ = some (some (dok v)))
    (mid : C.sub d + 1 < 2 → ∀ v, C.pc (dok v) = C.pc d ∧
      C.sub (dok v) = C.sub d + 1 ∧ C.acc (dok v) = C.acc d ++ [v] ∧
      C.facts (dok v) = C.facts d ∧ C.inv (dok v))
    (hF : C.facts d = factsFrom live val) (hoff : ∀ r ∈ live, r ∉ a.regs)
    {tr : TagF} (htr : ∀ y, tr.ok (some (.bits 32 y)))
    (hq : afterF qt (C.pc d) [(r0, tr), (r1, tr)] = true)
    (last : ¬ C.sub d + 1 < 2 → ∀ v, C.sub (dok v) = 0 ∧ C.acc (dok v) = [] ∧
      C.inv (dok v) ∧ SegQ K A L g (QTF qt) (C.pc d + 1) (C.facts d) (C.pc (dok v))
        (C.facts (dok v))) (e : Event) : C.StepForQ (QTF qt) Wf d e := by
  intro t u ins h hi hc hQ hWe hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨x, bs, rfl, rfl⟩ := fires_loadNc hru hloc hb hk hsem hnc hf
  obtain ⟨hP, hS0, hA, hFl, hR⟩ := h
  obtain ⟨y, hy⟩ := hW _ hWe x bs rfl
  have hlen : a.regs.length = 2 := by rw [hregs]; rfl
  by_cases hm : C.sub d + 1 < 2
  · obtain ⟨hpc, hs, ha, hF', hinv⟩ := mid hm (.bits 32 y)
    have hm' : t.sub + 1 < a.regs.length := by rw [hS0, hlen]; exact hm
    have hu : afterLoad t a.regs bs =
        { t with sub := t.sub + 1, acc := t.acc ++ [.bits 32 y] } := by
      simp [afterLoad, hy, hm']
    rw [hu]
    refine .inl ⟨dok (.bits 32 y), _, hok x bs _ hy, .refl, ⟨⟨?_, ?_, ?_, hFl, ?_⟩, hinv⟩,
      QTF.same hQ rfl rfl⟩
    · exact hP.trans hpc.symm
    · show t.sub + 1 = C.sub (dok _)
      rw [hS0, hs]
    · show t.acc ++ [_] = C.acc (dok _)
      rw [hA, ha]
    · rw [hF']; exact hR
  · obtain ⟨hs0, ha0, hinv, seg⟩ := last hm (.bits 32 y)
    obtain ⟨y0, h0⟩ := hlast hm
    have hm' : ¬ t.sub + 1 < a.regs.length := by rw [hS0, hlen]; exact hm
    have hacc : t.acc = [.bits 32 y0] := hA.trans h0
    obtain ⟨u0, hu0⟩ : ∃ u0, u0 = afterLoad t a.regs bs := ⟨_, rfl⟩
    have hu : u0 = { setRegs t [r0, r1] [.bits 32 y0, .bits 32 y] with
        pc := t.pc + 1, sub := 0, acc := [] } := by
      have hm2 : ¬ t.sub = 0 := by omega
      rw [hu0]; simp [afterLoad, hy, hm2, hacc, hregs]
    obtain ⟨-, -, -, hskF⟩ := setRegs_skel t [r0, r1] [.bits 32 y0, .bits 32 y]
    have hAt : At u0 (C.pc d + 1) (C.facts d) := by
      have hreg := hR
      rw [hF] at hreg
      have hoff' : ∀ r ∈ live, r ∉ [r0, r1] := by rw [← hregs]; exact hoff
      rw [hu]
      refine ⟨by show t.pc + 1 = _; rw [hP], rfl, rfl, ?_, ?_⟩
      · show (setRegs t [r0, r1] [.bits 32 y0, .bits 32 y]).fault = none
        rw [hskF]; exact hFl
      · rw [hF]
        exact holds_setRegs_frame hreg (fun r hr => ⟨hoff' r hr, hr, rfl⟩)
    have hQ' : QTF qt u0 := by
      rw [hu]
      refine QTF.after1 hQ hP (by simp [hP]) (fun r hl => ?_) (fun q hq' => ?_) hq
      · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
          not_or] at hl
        simp [setRegs, setReg, Function.update_of_ne hl.1, Function.update_of_ne hl.2]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
        rcases hq' with rfl | rfl
        · by_cases h1 : r0 = r1
          · subst h1; simpa [setRegs, setReg] using htr y
          · simpa [setRegs, setReg, Function.update_of_ne h1] using htr y0
        · simpa [setRegs, setReg] using htr y
    obtain ⟨t', hr, hg, hq'⟩ := landQ hAt hQ' seg hinv hs0 ha0
    rw [← hu0]
    exact .inl ⟨dok (.bits 32 y), t', hok x bs _ hy, hr, hg, hq'⟩

end PTX.Flow.Code
