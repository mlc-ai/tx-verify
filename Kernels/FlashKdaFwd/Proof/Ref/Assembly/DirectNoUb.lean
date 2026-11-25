-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.DirectData
public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.Tracked
public import Kernels.FlashKdaFwd.Proof.Ref.Conversion.Exports
public import Kernels.FlashKdaFwd.Proof.Ref.CarryLoad.Exports
public import Kernels.FlashKdaFwd.Proof.Ref.Compute.ExportsProtocolLib
public import Kernels.FlashKdaFwd.Proof.Ref.Epilogue.Exports
public import Lemmas.Step.ExitLast

@[expose] public section

/-!
# No thread makes an undefined-behaviour event

The three fields `computeNoUb`, `loadNoUb`, `storeNoUb` of `DirectFacts` (`Proof/Top/Wire.lean`)
say that no event of a thread is undefined behaviour (an event `⟨pc, .ub f⟩`). They are proved
here for every consistent execution under the precondition, from the data half `DataHalf`
(`DirectData.lean`; `Values.lean: dataHalf` proves it from the value layers).

**Words.** A *followed state* of thread `g` at position `k` is the state of its machine before
its `k`-th event (`At (code L) X g k s`). The machine's *successor* along the event `e` is
`Thread.next L g s e`: `some (some s')` (a state), `none` (*dead*: an instruction between two
events faulted, or the event was the thread's `ret`) or `some none` (the machine *gives up*,
which never happens: `Assembly.tracked`). A *stage* is one of the seven phases of a thread's
run with that phase's invariant at the state (`Assembly.Stage`).

**The induction.** It is the chain's `Assembly.followed` (`Tracked.lean`): every position of a
launched thread up to the end of its trace has a followed state, given `Alive L X` ("no event
other than a `ret` leads from a followed state to a dead one"). So two things are proved per
stage, each from the phase's control half and the data half of the sites of that phase:

* `alive` (`Alive L X`): the successor is not dead. The chain's `alive_of` leaves the four
  phases with a data condition: `conversion_alive` (`Conversion.conversion_ok`; at a load the
  successor is `DataHalf.convLoad`, at a store the condition is `DataHalf.convStore` read
  through the event's closed form), `carryLoad_alive` (`CarryLoad.carry_ok` with
  `DataHalf.carryLoad`), `compute_alive` (`Compute.ok_control` at the seven control positions,
  `DataHalf.tileNext` at the 262 positions of the data path), `store_alive`
  (`Store.store_good`: only an element read can lead to a dead state, `DataHalf.elemRead`).
* `noUb_at`: the event at a followed state is not undefined behaviour. Startup:
  `Startup.noUb_startup`; Conversion: `Conversion.ub_conversion` and `DataHalf.convStore`;
  CarryLoad: `CarryLoad.carry_noUb`; Compute: the closed form `Compute.EvAt` and
  `DataHalf.matrixEv`; Producer: `Producer.ev_not_ub`; Store: the exact event `Store.EvX` and
  `DataHalf.elemStore`; epilogue: `Epilogue.epilogue_ok` and `DataHalf.finalStore`.

`noUb` joins the two: an event at position `k` has no `ret` before it (`Execution.exit_last`),
so its position has a followed state. `everFollowed` is the statement about states for the
other layers: every position that an event follows has a followed state.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly.Direct
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly

noncomputable section
set_option linter.unusedVariables false

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-! ### Sites of the tile loop -/

/-- The kinds of site of the data path of the tile loop. -/
def isBody : Compute.SK → Bool
  | .ld _ | .ldMx _ | .mma _ | .mv _ | .st _ | .stWr _ => true
  | .load j => decide (159 ≤ j.val) && decide (j.val ≤ 176)
  | _ => false

/-- Every position of a tile between the two polls and the named barrier is on the data
path. -/
theorem body_pos : ∀ n < 268, 2 ≤ n → n < 264 → isBody (Compute.skOf n) = true := by
  decide +kernel

/-- A site of a kind of the data path is a site of `TileSite`. -/
theorem tileSite_of {k : Compute.SK} {s : Site} (hat : k.At s) (hb : isBody k = true) :
    TileSite s := by
  cases k <;> simp only [isBody, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hb
  all_goals simp only [Compute.SK.At] at hat
  · subst hat; exact trivial
  · obtain ⟨row, rfl⟩ := hat; exact trivial
  · subst hat; exact trivial
  · subst hat; exact trivial
  · subst hat; exact trivial
  · obtain ⟨row, rfl⟩ := hat; exact trivial
  · subst hat; exact hb

/-- A site of the kind of a warp matrix event is a site of `MatrixSite`. -/
theorem matrixSite_of {k : Compute.SK} {s : Site} (hat : k.At s)
    (hm : Compute.Proto.isMx k = true) : MatrixSite s := by
  cases k <;> simp only [Compute.Proto.isMx, Bool.false_eq_true] at hm
  all_goals simp only [Compute.SK.At] at hat
  · obtain ⟨row, rfl⟩ := hat; exact trivial
  · subst hat; exact trivial
  · subst hat; exact trivial
  · subst hat; exact trivial

/-! ### The successor of a followed state -/

/-- The state before position `k + 1` is the machine's successor along the event at `k`. -/
theorem stateAt_next {k : Nat} {s : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : At (code L) X g k s) :
    Frame.stateAt (code L) X g (k + 1) = Thread.next L g s e := by
  rw [Frame.stateAt_succ he, hσ]
  rfl

/-- A followed successor is not dead. -/
theorem alive_of_followed {k : Nat} {s : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : At (code L) X g k s)
    (h : ∃ s', Frame.stateAt (code L) X g (k + 1) = some (some s')) :
    Thread.next L g s e ≠ none := by
  obtain ⟨s', hs'⟩ := h
  rw [stateAt_next he hσ] at hs'
  rw [hs']
  exact fun h => by cases h

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hD : DataHalf P L mem0 X) (hg : g < L.threads)
include hpre hX hD hg

/-! ### No thread dies -/

/-- **Conversion phase**: the successor of an event at a state of the invariant is not
dead. -/
theorem conversion_alive {j0 k : Nat} {s : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : At (code L) X g k s) (hI : Conversion.Inv P X g j0 k s) :
    Thread.next L g s e ≠ none := by
  obtain ⟨pos, hr, -, -, hev⟩ := Conversion.event_at hpre hX hg he hσ hI
  have hok : Conversion.DataOk s e → Thread.next L g s e ≠ none := fun hdata => by
    obtain ⟨-, s', hn⟩ := Conversion.conversion_ok hpre hX hg he hσ hI hdata
    rw [hn]
    exact fun h => by cases h
  cases pos with
  | ld j u => exact alive_of_followed he hσ (hD.convLoad g k s e j hg hσ hr.site he)
  | st j u =>
    have hub := hD.convStore g k s e j hg hσ hr.site he
    refine hok ⟨fun a bs hk => ?_, fun j' hs => ?_⟩
    · rcases hev with ⟨v', -, rfl⟩ | ⟨f, -, rfl⟩ <;> cases hk
    · have h := hr.site.symm.trans hs
      simp only [Conversion.Pos.site, Site.store.injEq, Fin.mk.injEq] at h
      obtain rfl : j = j' := Fin.ext h
      rcases hev with ⟨v', hv, -⟩ | ⟨f, -, rfl⟩
      · exact ⟨v', hv⟩
      · exact absurd rfl (hub _ f)
  | fence =>
    refine hok ⟨fun a bs hk => ?_, fun j' hs => ?_⟩
    · rw [show e = _ from hev] at hk
      cases hk
    · have h := hr.site.symm.trans hs
      simp [Conversion.Pos.site] at h
  | bar j =>
    refine hok ⟨fun a bs hk => ?_, fun j' hs => ?_⟩
    · rw [show e = _ from hev] at hk
      cases hk
    · have h := hr.site.symm.trans hs
      simp [Conversion.Pos.site] at h

/-- **CarryLoad phase**: the successor of an event at a state of the invariant is not dead. -/
theorem carryLoad_alive {j0 k : Nat} {s : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : At (code L) X g k s) (hI : CarryLoad.Inv P X g j0 k s) :
    Thread.next L g s e ≠ none := by
  have hdata : CarryLoad.DataOk e := by
    intro a bs hk
    obtain ⟨pos, hr, hev, -⟩ := CarryLoad.event_at hpre hX hg he hσ hI
    cases pos with
    | ld j =>
      obtain ⟨bs', -, rfl⟩ := hev
      obtain rfl : bs' = bs := by
        simp only [Kind.rd.injEq] at hk
        exact hk.2
      have hs : s.site = .load ⟨31 + j.val, by omega⟩ := by
        rw [hr.site]
        simp only [CarryLoad.Pos.site, CarryLoad.ldSite, j.isLt, ↓reduceDIte]
      exact hD.carryLoad g k s j _ _ _ hg (by rw [block_mod hpre]; exact hr.pos.1) hσ hs he
    | fence =>
      rw [show e = _ from hev] at hk
      cases hk
  obtain ⟨-, s', hn⟩ := CarryLoad.carry_ok hpre hX hg he hσ hI hdata
  rw [hn]
  exact fun h => by cases h

/-- **Compute phase**: the successor of an event at a state of the invariant is not dead. -/
theorem compute_alive {j0 k : Nat} {s : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : At (code L) X g k s) (hI : Compute.Inv P L X g j0 k s) :
    Thread.next L g s e ≠ none := by
  obtain ⟨pos, hR, -⟩ := hI
  have hctl : pos.control → Thread.next L g s e ≠ none := fun hctl => by
    obtain ⟨tt, ins, o, hat, -, hc, hf⟩ := Frame.fired_site (sounds hpre) hX he hσ
    obtain ⟨s', hn⟩ := Compute.ok_control hpre hg hR hctl hat hc hf
    rw [hn]
    exact fun h => by cases h
  cases pos with
  | entry => exact hctl trivial
  | tile t n =>
    have hn : n < 268 := hR.facts.pos
    by_cases hb : 2 ≤ n ∧ n < 264
    · have hts : TileSite s.site := tileSite_of hR.site (body_pos n hn hb.1 hb.2)
      have hc : g % L.block < 128 := by
        rw [block_mod hpre]
        exact Compute.Proto.refAt_compute hR
      exact alive_of_followed he hσ (hD.tileNext g k s e hg hc hσ hts he)
    · exact hctl (show n ≤ 1 ∨ 264 ≤ n by omega)

/-- **Store phase**: the successor of an event at a state of the invariant is not dead. -/
theorem store_alive {k : Nat} {s : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : At (code L) X g k s) (hI : Store.Inv P X g k s) : Thread.next L g s e ≠ none := by
  obtain ⟨pos, hr, -, -, ⟨d', hd⟩ | ⟨hrd, hn⟩⟩ := Store.store_good hpre hX hg he hσ hI
  · rw [hd]
    exact fun h => by cases h
  · have hs : ElemReadSite s.site := by
      rw [hr.site]
      cases pos <;> first | exact hrd.elim | exact trivial | rfl
    exact alive_of_followed he hσ (hD.elemRead g k s e hg hσ hs he)

omit hg in
/-- **No thread dies**: no event of a launched thread other than its `ret` leads from a
followed state to a dead state. -/
theorem alive : Alive L X :=
  alive_of hpre hX fun g k s e hg he hσ h => by
    rcases h with ⟨j0, hI⟩ | ⟨j0, hI⟩ | ⟨-, j0, hI⟩ | ⟨-, hI⟩
    · exact conversion_alive hpre hX hD hg he hσ hI
    · exact carryLoad_alive hpre hX hD hg he hσ hI
    · exact compute_alive hpre hX hD hg he hσ hI
    · exact store_alive hpre hX hD hg he hσ hI

/-! ### The event at a followed state is not undefined behaviour -/

/-- **Compute phase**: the event at a state of the invariant is not undefined behaviour. -/
theorem compute_noUb {j0 k : Nat} {s : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : At (code L) X g k s) (hI : Compute.Inv P L X g j0 k s) :
    ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
  obtain ⟨pos, hR, -⟩ := hI
  have hev := Compute.Proto.ev_at hpre hX hR hσ he
  rintro pc f rfl
  cases pos with
  | entry => cases (show (⟨pc, .ub f⟩ : Event) = _ from hev)
  | tile t n =>
    have hn : n < 268 := hR.facts.pos
    rcases Compute.Proto.pos_cases hn with rfl | rfl | rfl | rfl | rfl | rfl | ⟨h2, h264⟩
    · obtain ⟨ok, h⟩ := Compute.Proto.evAt_0.mp hev
      cases h
    · obtain ⟨ok, h⟩ := Compute.Proto.evAt_1.mp hev
      cases h
    · cases Compute.Proto.evAt_264.mp hev
    · cases Compute.Proto.evAt_265.mp hev
    · cases Compute.Proto.evAt_266.mp hev
    · cases Compute.Proto.evAt_267.mp hev
    · rw [Compute.Proto.evAt_body h2 h264] at hev
      by_cases ha : (Compute.Proto.addrOf n).2.2 = 0
      · have hm : MatrixSite s.site := matrixSite_of hR.site (Compute.Proto.mx_pos n hn h2 h264 ha)
        exact hD.matrixEv g k s _ hg (by rw [block_mod hpre]; exact Compute.Proto.refAt_compute hR)
          hσ hm he pc f rfl
      · rw [ite_eq_right ha] at hev
        rcases hev with ⟨bs, h, -⟩ | ⟨bs, h, -⟩ <;> cases h

/-- **The event at a followed state is not undefined behaviour.** -/
theorem noUb_at {k : Nat} {s : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : At (code L) X g k s) : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
  obtain ⟨hst, hub⟩ := stage_event hpre hX hg he hσ
  cases hst with
  | startup hI =>
    rintro pc f rfl
    exact hI.inv.not_left (Startup.noUb_startup hpre hX hg he hσ)
  | conversion _ _ hI =>
    rintro pc f rfl
    obtain ⟨j, hs, -⟩ := Conversion.ub_conversion hpre hX hg he hσ hI
    exact hD.convStore g k s _ j hg hσ hs he pc f rfl
  | carryLoad _ _ hI => exact CarryLoad.carry_noUb hpre hX hg he hσ hI
  | compute _ _ _ _ hI => exact compute_noUb hpre hX hD hg he hσ hI
  | producer hr _ _ _ hI =>
    obtain ⟨pos, w, p, x, rfl, -, -, hev, -⟩ := Producer.producer_good hpre hX hg hr he hσ hI
    exact Producer.ev_not_ub hev
  | store hr _ _ _ hI _ =>
    obtain ⟨pos, hr', -, hev, -⟩ := Store.store_good hpre hX hg he hσ (hI hub)
    cases pos with
    | gst t row c j =>
      rcases hev with ⟨v, -, rfl⟩ | ⟨f, -, rfl⟩
      · exact fun pc f h => by cases h
      · exact hD.elemStore g k s _ j hg hσ hr'.site he
    | _ => exact Store.EvX.noUb hev (fun _ _ _ _ h => by cases h)
  | epilogue _ _ _ hI =>
    refine (Epilogue.epilogue_ok hpre hX hg he hσ (hI hub) fun j hs => ?_).1
    obtain ⟨pos, hr', hon, -, -, -, hex⟩ := Epilogue.event_at hpre hX hg he hσ (hI hub)
    have h := hr'.site.symm.trans hs
    cases pos with
    | st j' =>
      simp only [Epilogue.Pos.site, Site.store.injEq, Fin.mk.injEq] at h
      obtain rfl : j' = j := Fin.ext (by omega)
      rcases hex with ⟨v, hv, -⟩ | ⟨f, -, rfl⟩
      · exact ⟨v, hv⟩
      · exact absurd rfl
          (hD.finalStore g k s _ j' hg (by rw [block_mod hpre]; exact hon) hσ hr'.site he _ f)
    | _ => simp [Epilogue.Pos.site] at h

omit hg in
/-- **Every position that an event follows has a followed state.** -/
theorem everFollowed {k : Nat} {e : Event} (he : X.get (g, k) = some e) :
    ∃ s, At (code L) X g k s := by
  have hg := Frame.lt_of_get hX he
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  refine followed hpre hX (alive hpre hX hD) hg (Nat.le_of_lt hk) fun i pc hi hx => ?_
  have := Execution.exit_last hX hg hx
  omega

omit hg in
/-- **No thread makes an undefined-behaviour event.** -/
theorem noUb (g k pc : Nat) (f : Fault) : X.get (g, k) ≠ some ⟨pc, .ub f⟩ := by
  intro he
  obtain ⟨s, hσ⟩ := everFollowed hpre hX hD he
  exact noUb_at hpre hX hD (Frame.lt_of_get hX he) he hσ pc f rfl

end

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly.Direct
