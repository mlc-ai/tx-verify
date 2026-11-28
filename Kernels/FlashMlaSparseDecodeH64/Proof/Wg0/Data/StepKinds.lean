-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.OutStepS
public import Lemmas.Flow.WfNext
public import Lemmas.Flow.CutNext
public import Lemmas.Flow.Step.TcSteps

@[expose] public section

/-! # The strict steps of warpgroup 0's data machine at the data-only windows, by kind

`skW_<kind>`: the strict step (`Code.StepFor`) of the data machine at a state of a site whose window
to the next event writes data registers only (`Gen/SegS*.lean`). The local code from the event to
the successor's event is an exact segment from the control facts and the data facts to the
successor's, taken as a hypothesis of the kind and given per site by `segS_<pc>`. The state is on
the chain (`ok`), so its data facts are the site's.

* `skW_nx`: an event that continues at the next instruction (`bar.sync`, `tcgen05.wait::ld`);
* `skW_st`: a one-source store;
* `skW_ld1`: a one-register shared load that follows only bytes that rebuild. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- The facts of the data machine at a state on the chain. -/
theorem facts_ok {d : D} (hok : d.ok = true) :
    (code P L g w).facts d = Control.facts P L g w d.c ++ wF (scX L) d.c.site d.b := by
  simp [dF, hok]

/-- The successor after an event of a non-arrival site on the chain. -/
theorem next_on {d : D} {c' : Control.D} {b' : Blk} (hna : d.c.site ≠ .arrS) (hok : d.ok = true)
    (hso : succOk d.c c' = true) {e : Event} (hrec : record d.c e d.b = b') :
    dataNext L d c' e = ⟨c', b', d.hist, true⟩ := by
  rw [dataNext_eq hna, hrec, hso]
  simp [hok]

theorem facts_next {d : D} {c' : Control.D} {b' : Blk} :
    (code P L g w).facts ⟨c', b', d.hist, true⟩ =
      Control.facts P L g w c' ++ wF (scX L) c'.site b' :=
  facts_ok rfl

/-- The control facts of a state, from those of its registers but one and that register's. -/
theorem facts_of_erase {c : Control.D} {R : Nat → Option Value} {r : Nat}
    (hr : r ∈ Control.ctlLive c.site.pc) (hv : R r = some (Control.valueOf P L g w c r))
    (h : Holds R (factsFrom ((Control.ctlLive c.site.pc).erase r) (Control.valueOf P L g w c))) :
    Holds R (Control.facts P L g w c) := by
  unfold Control.facts
  refine holds_of_pointwise fun r' hr' => ?_
  by_cases he : r' = r
  · subst he; exact hv
  · exact holds_mem h (mem_factsFrom ((List.mem_erase_of_ne he).mpr hr'))

/-- As `facts_sub`, for the facts without one register. -/
theorem facts_sub_erase {c c' : Control.D} {r : Nat}
    (hv : Control.valueOf P L g w c' = Control.valueOf P L g w c)
    (hl : ∀ q ∈ (Control.ctlLive c'.site.pc).erase r, q ∈ Control.ctlLive c.site.pc) :
    ∀ R, Holds R (Control.facts P L g w c) →
      Holds R (factsFrom ((Control.ctlLive c'.site.pc).erase r) (Control.valueOf P L g w c')) := by
  intro R h
  unfold Control.facts at h
  rw [hv]
  exact holds_factsFrom_mono h hl

theorem facts_keys {c : Control.D} {pc : Nat} (h : c.site.pc = pc) :
    (Control.facts P L g w c).map Prod.fst = Control.ctlLive pc := by
  rw [← h]; exact factsFrom_keys

/-- The control facts of a state whose site changes are held by the facts of the state before,
when the registers live there are live before. -/
theorem facts_sub {c c' : Control.D}
    (hv : Control.valueOf P L g w c' = Control.valueOf P L g w c)
    (hl : ∀ r ∈ Control.ctlLive c'.site.pc, r ∈ Control.ctlLive c.site.pc) :
    ∀ R, Holds R (Control.facts P L g w c) → Holds R (Control.facts P L g w c') := by
  intro R h
  unfold Control.facts at h ⊢
  rw [hv]
  exact holds_factsFrom_mono h hl

theorem dropReg_of_fresh {r : Nat} {F : List (Nat × Value)} (h : ∀ q ∈ F, q.1 ≠ r) :
    dropReg r F = F := by
  unfold dropReg
  exact List.filter_eq_self.mpr fun q hq => by simpa using h q hq

/-- The successor of a state on the chain is landed on by the exact segment. -/
theorem skW_lands {d : D} {c' : Control.D} {b' : Blk} {pc pc' : Nat}
    (hp : d.c.site.pc = pc) (hp' : c'.site.pc = pc') (he0 : d.c.el = 0)
    (he1 : d.c.el = 0 → c'.el = 0) (hel : d.c.el = 0 → c'.el < Control.elems c'.site)
    (hok : d.ok = true)
    (hseg : ∃ n, Seg kernel Assumptions.all L g n (pc + 1)
      (Control.facts P L g w d.c ++ wF (scX L) d.c.site d.b) pc'
      (Control.facts P L g w c' ++ wF (scX L) c'.site b')) :
    (code P L g w).Lands d ((code P L g w).pc d + 1) ((code P L g w).facts d)
      ⟨c', b', d.hist, true⟩ := by
  refine ⟨fun _ => ?_, he1 he0, by simp [Control.D.acc, he1 he0], fun _ => hel he0⟩
  rw [facts_ok hok, facts_next]
  show ∃ n, Seg _ _ _ _ _ (d.c.site.pc + 1) _ c'.site.pc _
  rw [hp, hp']
  exact hseg

theorem skW_next {d : D} {c' : Control.D} {b' : Blk} (hna : d.c.site ≠ .arrS) (hok : d.ok = true)
    (hsucc : ∀ e, Control.succ P L g w d.c e = some (some c')) (hso : succOk d.c c' = true)
    (hrec : ∀ e, record d.c e d.b = b') (e : Event) :
    (code P L g w).next d e = some (some ⟨c', b', d.hist, true⟩) := by
  show (Control.succ P L g w d.c e).map _ = _
  rw [hsucc e]
  show some (some (dataNext L d c' e)) = _
  rw [next_on hna hok hso (hrec e)]

theorem el0_of_one {d : D} (hel1 : Control.elems d.c.site = 1)
    (hi : d.c.el < Control.elems d.c.site) : d.c.el = 0 := by
  omega

/-- **An event that continues at the next instruction.** -/
theorem skW_nx {d : D} {c' : Control.D} {ins0 : Instr} {b' : Blk} {pc pc' : Nat}
    (hp : d.c.site.pc = pc) (hp' : c'.site.pc = pc') (hna : d.c.site ≠ .arrS)
    (hc : kernel.code[d.c.site.pc]? = some ins0)
    (hadv : ∀ {t e u}, Fires d.c.site.pc (eventTmpl Assumptions.all L g t ins0.op) e (some u) →
      u = PTX.next t)
    (hel1 : Control.elems d.c.site = 1) (hok : d.ok = true)
    (hsucc : ∀ e, Control.succ P L g w d.c e = some (some c'))
    (hso : succOk d.c c' = true) (hrec : ∀ e, record d.c e d.b = b')
    (he1 : d.c.el = 0 → c'.el = 0)
    (hel : d.c.el = 0 → c'.el < Control.elems c'.site)
    (hseg : ∃ n, Seg kernel Assumptions.all L g n (pc + 1)
      (Control.facts P L g w d.c ++ wF (scX L) d.c.site d.b) pc'
      (Control.facts P L g w c' ++ wF (scX L) c'.site b')) (e : Event) :
    (code P L g w).StepFor d e := by
  refine fun {t u} ins hat hi hc' hf => ?_
  have he0 := el0_of_one hel1 hi
  exact (Code.step_issue (C := code P L g w) hc hadv (skW_next hna hok hsucc hso hrec)
    (by exact he0) (by simp [Control.D.acc, he0]) (skW_lands hp hp' he0 he1 hel hok hseg)).step
    ins hat hi hc' hf

/-- **A one-source store.** -/
theorem skW_st {d : D} {c' : Control.D} {a : MemAccess} {b' : Blk} {pc pc' : Nat}
    (hp : d.c.site.pc = pc) (hp' : c'.site.pc = pc') (hna : d.c.site ≠ .arrS)
    (hc : kernel.code[d.c.site.pc]? = some ⟨none, .mem a⟩) (hk : a.kind = .store)
    (hsr : a.srcs.length = 1)
    (hel1 : Control.elems d.c.site = 1) (hok : d.ok = true)
    (hsucc : ∀ e, Control.succ P L g w d.c e = some (some c'))
    (hso : succOk d.c c' = true) (hrec : ∀ e, record d.c e d.b = b')
    (he1 : d.c.el = 0 → c'.el = 0)
    (hel : d.c.el = 0 → c'.el < Control.elems c'.site)
    (hseg : ∃ n, Seg kernel Assumptions.all L g n (pc + 1)
      (Control.facts P L g w d.c ++ wF (scX L) d.c.site d.b) pc'
      (Control.facts P L g w c' ++ wF (scX L) c'.site b')) (e : Event) :
    (code P L g w).StepFor d e := by
  refine fun {t u} ins hat hi hc' hf => ?_
  have he0 := el0_of_one hel1 hi
  exact (Code.step_vec_last (C := code P L g w) hc hk
    (by show ¬ d.c.el + 1 < _; rw [hsr]; omega) (skW_next hna hok hsucc hso hrec)
    (by simp [Control.D.acc, he0]) (skW_lands hp hp' he0 he1 hel hok hseg)).step ins hat hi hc' hf

/-- No fact of the state is on the register `r`. -/
theorem facts_fresh {d : D} {r pc : Nat} (hp : d.c.site.pc = pc) (hr : r ∉ Control.ctlLive pc)
    (hw : ∀ q ∈ wF (scX L) d.c.site d.b, q.1 ≠ r) :
    ∀ q ∈ Control.facts P L g w d.c ++ wF (scX L) d.c.site d.b, q.1 ≠ r := by
  intro q hq hq1
  rcases List.mem_append.mp hq with h | h
  · have h2 : q.1 ∈ (Control.facts P L g w d.c).map Prod.fst := List.mem_map_of_mem h
    rw [facts_keys hp, hq1] at h2
    exact hr h2
  · exact hw q h hq1

/-- **A one-register load** that follows only bytes that rebuild to a value satisfying `Cd`
(the window's condition); the register is fresh. -/
theorem skW_ld1 {d : D} {c' : Control.D} {a : MemAccess} {r pc pc' : Nat} {mk : Value → Blk}
    {e : Event} {Cd : Value → Prop}
    (hOk : ∀ x bs, e.kind = .rd x bs → ∃ v, rebuild 3 bs = .ok v ∧ Cd v)
    (hp : d.c.site.pc = pc) (hp' : c'.site.pc = pc') (hna : d.c.site ≠ .arrS)
    (hc : kernel.code[d.c.site.pc]? = some ⟨none, .mem a⟩) (hk : a.kind = .load)
    (hnc0 : a.nc = false) (hx : a.ext = .same) (hr : a.regs = [r])
    (hel1 : Control.elems d.c.site = 1) (hok : d.ok = true)
    (hsucc : ∀ x bs, Control.succ P L g w d.c ⟨d.c.site.pc, .rd x bs⟩ = some (some c'))
    (hso : succOk d.c c' = true)
    (hrec : ∀ x bs v, rebuild 3 bs = .ok v → record d.c ⟨d.c.site.pc, .rd x bs⟩ d.b = mk v)
    (he1 : d.c.el = 0 → c'.el = 0) (hel : d.c.el = 0 → c'.el < Control.elems c'.site)
    (hoff : ∀ q ∈ Control.facts P L g w d.c ++ wF (scX L) d.c.site d.b, q.1 ≠ r)
    (hseg : ∀ v, Cd v → ∃ n, Seg kernel Assumptions.all L g n (pc + 1)
      ((Control.facts P L g w d.c ++ wF (scX L) d.c.site d.b) ++ [(r, v)]) pc'
      (Control.facts P L g w c' ++ wF (scX L) c'.site (mk v))) :
    (code P L g w).StepFor d e := by
  classical
  let Ok : Event → Prop := fun e => ∀ x bs, e.kind = .rd x bs → ∃ v, rebuild 3 bs = .ok v ∧ Cd v
  suffices h : ((code P L g w).cut Ok).StepFor d e from
    @StepFor.of_cut _ _ _ _ (code P L g w) Ok d e h hOk
  intro t u ins hat hi hc' hf
  have he0 := el0_of_one hel1 hi
  have hn : ∀ x bs v, rebuild 3 bs = .ok v →
      ((code P L g w).cut Ok).next d ⟨d.c.site.pc, .rd x bs⟩ =
      if Cd v then some (some ⟨c', mk v, d.hist, true⟩) else some none := by
    intro x bs v hv
    by_cases hcd : Cd v
    · have hO : Ok ⟨d.c.site.pc, .rd x bs⟩ := by
        intro x' bs' hk'
        obtain ⟨rfl, rfl⟩ : x = x' ∧ bs = bs' := by simpa using hk'
        exact ⟨v, hv, hcd⟩
      rw [cut_next _ _ hO]
      simp only [hcd, ↓reduceIte]
      show (Control.succ P L g w d.c _).map _ = _
      rw [hsucc x bs]
      show some (some (dataNext L d c' _)) = _
      rw [next_on hna hok hso (hrec x bs v hv)]
    · have hO : ¬ Ok ⟨d.c.site.pc, .rd x bs⟩ := by
        intro h
        obtain ⟨v', hv', hc2⟩ := h x bs rfl
        rw [hv] at hv'
        obtain rfl := Except.ok.inj hv'
        exact hcd hc2
      rw [cut_next_not _ _ hO]
      simp only [hcd, ↓reduceIte]
  refine (Code.step_load_sel (C := (code P L g w).cut Ok) (r := r)
    (nv := fun v => if Cd v then some (some ⟨c', mk v, d.hist, true⟩) else some none)
    hc hk hnc0 hx hr hn ?_
    (by exact he0) (by simp [Control.D.acc, he0])
    (fun v => by by_cases h : Cd v <;> simp [h]) ?_).step ins hat hi hc' hf
  · intro x bs f hv
    right
    have hO : ¬ Ok ⟨d.c.site.pc, .rd x bs⟩ := by
      intro h
      obtain ⟨v', hv', -⟩ := h x bs rfl
      rw [hv] at hv'
      cases hv'
    exact cut_next_not _ _ hO
  · intro v d' hd
    by_cases hcd : Cd v
    · simp only [hcd, ↓reduceIte] at hd
      obtain rfl := Option.some.inj (Option.some.inj hd)
      refine ⟨fun _ => ?_, he1 he0, by simp [Control.D.acc, he1 he0], fun _ => hel he0⟩
      obtain ⟨n, h⟩ := hseg v hcd
      refine ⟨n, ?_⟩
      show Seg _ _ _ _ _ (d.c.site.pc + 1) _ c'.site.pc _
      rw [hp, hp']
      refine (h.weaken_start fun R hR => ?_)
      have hR' : Holds R ((r, v) :: dropReg r ((code P L g w).facts d)) := hR
      rw [facts_ok hok, dropReg_of_fresh hoff] at hR'
      exact (holds_append _ _ _).mpr ⟨hR'.2, ⟨hR'.1, trivial⟩⟩
    · simp only [hcd, ↓reduceIte] at hd; cases hd

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
