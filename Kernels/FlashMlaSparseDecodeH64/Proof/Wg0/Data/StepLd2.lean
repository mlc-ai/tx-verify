-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.StepKinds
public import Lemmas.Flow.Step.VecLoad

@[expose] public section

/-! # The strict step of a two-element shared load of warpgroup 0's data machine

`skW_ld2`: the peer elements (`pld k`), one element per event. The first element keeps the site
(`el = 1`, the accumulator holds the word read, the facts stay); the second follows only bytes that
rebuild to a value satisfying the window's condition `Cd`, and the exact window segment leads to the
next site. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- The block's reads after the peer element `k` is read as the pair `(a0, v)`. -/
def pwSet (b : Blk) (k : Nat) (a0 v : Value) : Blk :=
  { b with pw := fun j => if j = k then (a0, v) else b.pw j }

/-- No fact of the state is on a register of `ds`. -/
theorem facts_fresh_l {d : D} {ds : List Nat} {pc : Nat} (hp : d.c.site.pc = pc)
    (hr : ∀ r ∈ ds, r ∉ Control.ctlLive pc) (hw : ∀ q ∈ wF (scX L) d.c.site d.b, q.1 ∉ ds) :
    ∀ q ∈ Control.facts P L g w d.c ++ wF (scX L) d.c.site d.b, q.1 ∉ ds := by
  intro q hq hq1
  rcases List.mem_append.mp hq with h | h
  · have h2 : q.1 ∈ (Control.facts P L g w d.c).map Prod.fst := List.mem_map_of_mem h
    rw [facts_keys hp] at h2
    exact hr _ hq1 h2
  · exact hw q h hq1

/-- **A two-element load.** -/
theorem skW_ld2 {d : D} {k : Fin 8} {c' : Control.D} {a : MemAccess} {r0 r1 pc pc' : Nat}
    {e : Event} {Cd : Value → Prop} {mk : Value → Blk}
    (hOk : ∀ x bs, e.kind = .rd x bs → ∃ v, rebuild 3 bs = .ok v ∧ (d.c.el ≠ 0 → Cd v))
    (hs : d.c.site = .pld k) (hp : (Site.pld k).pc = pc) (hp' : c'.site.pc = pc')
    (hc : kernel.code[(Site.pld k).pc]? = some ⟨none, .mem a⟩) (hk : a.kind = .load)
    (hnc0 : a.nc = false) (hx : a.ext = .same) (hr : a.regs = [r0, r1]) (hne : r0 ≠ r1)
    (hok : d.ok = true)
    (hsm : d.c.el = 0 → ∀ x bs v, rebuild 3 bs = .ok v →
      Control.succ P L g w d.c ⟨pc, .rd x bs⟩ = some (some { d.c with el := 1, a0 := v }))
    (hsl : d.c.el ≠ 0 → ∀ x bs, Control.succ P L g w d.c ⟨pc, .rd x bs⟩ = some (some c'))
    (hso : d.c.el ≠ 0 → succOk d.c c' = true)
    (hrec : ∀ x bs v, d.c.el ≠ 0 → rebuild 3 bs = .ok v →
      record d.c ⟨pc, .rd x bs⟩ d.b = mk v)
    (he1 : c'.el = 0) (hel : 0 < Control.elems c'.site)
    (hoff : ∀ q ∈ Control.facts P L g w d.c ++ wF (scX L) d.c.site d.b, q.1 ∉ [r0, r1])
    (hseg : ∀ v, Cd v → ∃ n, Seg kernel Assumptions.all L g n (pc + 1)
      ((Control.facts P L g w d.c ++ wF (scX L) d.c.site d.b) ++ [(r0, d.c.a0), (r1, v)]) pc'
      (Control.facts P L g w c' ++ wF (scX L) c'.site (mk v))) :
    (code P L g w).StepFor d e := by
  classical
  let Ok : Event → Prop := fun e =>
    ∀ x bs, e.kind = .rd x bs → ∃ v, rebuild 3 bs = .ok v ∧ (d.c.el ≠ 0 → Cd v)
  suffices h : ((code P L g w).cut Ok).StepFor d e from
    @StepFor.of_cut _ _ _ _ (code P L g w) Ok d e h hOk
  intro t u ins hat hi hc' hf
  have hpc : d.c.site.pc = pc := by rw [hs]; exact hp
  have hna : d.c.site ≠ .arrS := by rw [hs]; nofun
  have hcc : kernel.code[d.c.site.pc]? = some ⟨none, .mem a⟩ := by rw [hs]; exact hc
  have hel2 : d.c.el < 2 := by
    have h : d.c.el < Control.elems d.c.site := hi
    rw [hs] at h; exact h
  have herr : ∀ x bs f, rebuild 3 bs = .error f →
      ((code P L g w).cut Ok).next d ⟨d.c.site.pc, .rd x bs⟩ = none ∨
      ((code P L g w).cut Ok).next d ⟨d.c.site.pc, .rd x bs⟩ = some none := by
    intro x bs f hv
    right
    have hO : ¬ Ok ⟨d.c.site.pc, .rd x bs⟩ := by
      intro h
      obtain ⟨v', hv', -⟩ := h x bs rfl
      rw [hv] at hv'
      cases hv'
    exact cut_next_not _ _ hO
  by_cases he0 : d.c.el = 0
  · have hn : ∀ x bs v, rebuild 3 bs = .ok v →
        ((code P L g w).cut Ok).next d ⟨d.c.site.pc, .rd x bs⟩ =
        some (some ⟨{ d.c with el := 1, a0 := v }, d.b, d.hist, true⟩) := by
      intro x bs v hv
      have hO : Ok ⟨d.c.site.pc, .rd x bs⟩ := by
        intro x' bs' hk'
        obtain ⟨rfl, rfl⟩ : x = x' ∧ bs = bs' := by simpa using hk'
        exact ⟨v, hv, fun h => absurd he0 h⟩
      rw [cut_next _ _ hO]
      show (Control.succ P L g w d.c _).map _ = _
      rw [hpc, hsm he0 x bs v hv]
      show some (some (dataNext L d _ _)) = _
      rw [dataNext_eq hna]
      simp [hok, record, hs, he0, succOk]
    refine (Code.step_vload_mid (C := (code P L g w).cut Ok) (a := a)
      (dn := fun v => ⟨{ d.c with el := 1, a0 := v }, d.b, d.hist, true⟩) hcc hk hnc0 hx
      (by show d.c.el + 1 < _; rw [hr]; simp [he0]) hn herr (fun _ => rfl)
      (fun _ => by show 1 = d.c.el + 1; omega)
      (fun v => by simp [Control.D.acc, he0, hs])
      (fun v => ?_)
      (fun _ _ => by show 1 < Control.elems d.c.site; rw [hs]; simp [Control.elems])).step
      ins hat hi hc' hf
    show Control.facts P L g w { d.c with el := 1, a0 := v } ++
      (if (true : Bool) then wF (scX L) d.c.site d.b else []) =
      Control.facts P L g w d.c ++ (if d.ok then wF (scX L) d.c.site d.b else [])
    rw [hok]; rfl
  · have hn : ∀ x bs v, rebuild 3 bs = .ok v → Cd v →
        ((code P L g w).cut Ok).next d ⟨d.c.site.pc, .rd x bs⟩ =
        some (some ⟨c', mk v, d.hist, true⟩) := by
      intro x bs v hv hcd
      have hO : Ok ⟨d.c.site.pc, .rd x bs⟩ := by
        intro x' bs' hk'
        obtain ⟨rfl, rfl⟩ : x = x' ∧ bs = bs' := by simpa using hk'
        exact ⟨v, hv, fun _ => hcd⟩
      rw [cut_next _ _ hO]
      show (Control.succ P L g w d.c _).map _ = _
      rw [hpc, hsl he0 x bs]
      show some (some (dataNext L d c' _)) = _
      rw [dataNext_eq hna, hrec x bs v he0 hv]
      simp [hok, hso he0]
    have hsub : d.c.el = 1 := by omega
    refine (Code.step_vload_last (C := (code P L g w).cut Ok) (a := a)
      (nv := fun v => if Cd v then some (some ⟨c', mk v, d.hist, true⟩) else some none)
      hcc hk hnc0 hx (by show ¬ d.c.el + 1 < _; rw [hr]; simp [hsub])
      (by rw [hr]; simp [hne]) (fun q hq => by rw [hr]; exact hoff q (by
        have := facts_ok (P := P) (L := L) (g := g) (w := w) hok
        exact this ▸ hq)) ?_ herr (fun v => by by_cases h : Cd v <;> simp [h]) ?_).step
      ins hat hi hc' hf
    · intro x bs v hv
      by_cases hcd : Cd v
      · rw [hn x bs v hv hcd]; simp [hcd]
      · have hO : ¬ Ok ⟨d.c.site.pc, .rd x bs⟩ := by
          intro h
          obtain ⟨v', hv', hc2⟩ := h x bs rfl
          rw [hv] at hv'
          obtain rfl := Except.ok.inj hv'
          exact hcd (hc2 he0)
        rw [cut_next_not _ _ hO]; simp [hcd]
    · intro v d' hd
      by_cases hcd : Cd v
      · simp only [hcd, ↓reduceIte] at hd
        obtain rfl := Option.some.inj (Option.some.inj hd)
        refine ⟨fun _ => ?_, he1, by simp [Control.D.acc, he1],
          fun _ => by show c'.el < _; rw [he1]; exact hel⟩
        obtain ⟨n, h⟩ := hseg v hcd
        refine ⟨n, ?_⟩
        show Seg _ _ _ _ _ (d.c.site.pc + 1) _ c'.site.pc _
        rw [hpc, hp']
        refine (h.weaken_start fun R hR => ?_)
        have hR' : Holds R (a.regs.zip (((code P L g w).cut Ok).acc d ++ [v]) ++
            ((code P L g w).facts d)) := hR
        have hacc : ((code P L g w).cut Ok).acc d = [d.c.a0] := by
          simp [Control.D.acc, he0, hs]
        rw [hacc, hr, facts_ok hok] at hR'
        have h2 := (holds_append _ _ _).mp hR'
        refine (holds_append _ _ _).mpr ⟨h2.2, ?_⟩
        simpa using h2.1
      · simp only [hcd, ↓reduceIte] at hd; cases hd

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
