-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.Tmem
public import Kernels.InklingRelDecode.Proof.Interface.IpTmZero
public import Kernels.InklingRelDecode.Proof.Interface.ScBase

@[expose] public section

/-!
# The allocation's store writes the zero word (`AllocWordZero`)

`Interface.AllocWordZero Q L X`: the store of the allocated address that follows lane 0's
`tcgen05.alloc` (the state `DStart.Site.allocWr`) writes the bytes of the 32-bit zero.

The store is the next event of the allocation's request (the machine's step from
`DStart.Site.alloc` to `allocWr`), which is a recorded operation of its CTA's history: the
operation completed, since its thread went on (`TmemAlloc.covered_record`). It is a 512-column
allocation (`Tmem1.alloc_zero`: the history's first record, so at column 0), and the allocator's
result for it is the 32-bit value 0 (`Consistent.tmemPairResult`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem1
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface Tmem.Pair
open PTX.Kernels.InklingRelDecode.Proof.BarOrd

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A step into the allocation's store comes from the allocation, in lane 0 of the warp. -/
theorem pred_allocWr {g : Nat} {s : TSt} {e : Event} {tm : Value}
    (hn : (threadCode L g Q).next s e = some (some (.d (.dstart ⟨.allocWr, tm⟩)))) :
    (∃ tm0, s = .d (.dstart ⟨.alloc, tm0⟩)) ∧ laneOf L g = 0 := by
  cases s with
  | w s =>
    obtain ⟨a, -, h⟩ := map_map_eq_some_some (show (WComp.next L g s e).map
      (Option.map TSt.w) = some (some (.d (.dstart ⟨.allocWr, tm⟩))) from hn)
    cases h
  | d s =>
    obtain ⟨a, ha, h⟩ := map_map_eq_some_some (show (DComp.next L g Q s e).map
      (Option.map TSt.d) = some (some (.d (.dstart ⟨.allocWr, tm⟩))) from hn)
    have h' : a = .dstart ⟨.allocWr, tm⟩ := TSt.d.inj h
    subst h'
    cases s with
    | dstart d =>
      obtain ⟨site, tm0⟩ := d
      cases site
      · by_cases hl : laneOf L g = 0
        · exact ⟨⟨tm0, rfl⟩, hl⟩
        · simp [DComp.next, DComp.dstartNext, DStart.next, hl] at ha
      all_goals
        simp only [DComp.next, DComp.dstartNext, DStart.next, Option.map_some,
          Option.some.injEq] at ha
        repeat' split at ha
        all_goals simp at ha
    | pro d => exact absurd rfl (pro_ne ha ⟨.allocWr, tm⟩)
    | sm d => exact absurd rfl (sm_ne ha ⟨.allocWr, tm⟩)
    | epi d =>
      exact absurd rfl (map_ne (f := DComp.St.epi) (fun _ _ => by simp) ha ⟨.allocWr, tm⟩)

/-- **`Interface.AllocWordZero`**: the allocation's store writes the zero word. -/
theorem allocWordZero (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) : AllocWordZero Q L X := by
  intro g k pc a bs tm hget hσ
  have hg : g < L.threads := Frame.lt_of_get hX hget
  have hklt : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp hget).1
  cases k with
  | zero =>
    exfalso
    have hs : Frame.stateAt (code L Q) X g 0 = some (some (.d (.dstart ⟨.allocWr, tm⟩))) := hσ
    rw [Frame.stateAt_zero] at hs
    have h2 := Option.some.inj (Option.some.inj hs)
    change (if g % L.block < 128 then TSt.d (DComp.code L g Q).init
      else .w (WComp.code L g Q).init) = _ at h2
    split_ifs at h2
    · change TSt.d (.dstart (DStart.D.start L g)) = _ at h2
      unfold DStart.D.start at h2
      split_ifs at h2 <;> simp at h2
  | succ k0 =>
    obtain ⟨e0, he0⟩ : ∃ e0, (X.tr g)[k0]? = some e0 :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hσ' : Frame.stateAt (code L Q) X g (k0 + 1) =
        some (some (.d (.dstart ⟨.allocWr, tm⟩))) := hσ
    rw [Frame.stateAt_succ he0] at hσ'
    cases hk0 : Frame.stateAt (code L Q) X g k0 with
    | none => rw [hk0] at hσ'; simp at hσ'
    | some o =>
      cases o with
      | none => rw [hk0] at hσ'; simp [Flow.Code.toMachine] at hσ'
      | some s0 =>
        rw [hk0] at hσ'
        simp only [Option.bind_some] at hσ'
        have hn : (threadCode L g Q).next s0 e0 =
            some (some (.d (.dstart ⟨.allocWr, tm⟩))) := hσ'
        obtain ⟨⟨tm0, rfl⟩, hlane⟩ := pred_allocWr hn
        have hget0 : X.get (g, k0) = some e0 := he0
        have hk0' : St Q L X g k0 = some (some (.d (.dstart ⟨.alloc, tm0⟩))) := hk0
        obtain ⟨u, hF⟩ := fired_cont hX hf hg hget0 hk0' (by simp [ExitState])
        have hshape := DStart.shape_of_pre hpre (fired_dstart hF)
        simp only [DStart.Shape] at hshape
        subst hshape
        have hb : L.block = 256 := hpre.block
        have hl : g % L.block < 32 := (res_event_state hpre hX hf hget0).1
        have hlane' : g % L.block % 32 = 0 := hlane
        have hg0 : g % L.block = 0 := by omega
        obtain ⟨cta, hcta⟩ : ∃ cta, g = cta * L.block := ⟨g / L.block, by
          have := Nat.div_add_mod g L.block
          rw [Nat.mul_comm] at this
          omega⟩
        subst hcta
        have hto := (Proof2.tmem1Facts hpre hX).toTmem1Ops
        have hal : X.get (cta * L.block, k0) = some ⟨DStart.evPc DStart.Site.alloc,
            .tc (.resource .one (some ⟨.shared, cta * L.block / L.block, L.sharedBase⟩)
              (.alloc 512))⟩ := hget0
        have hcov := hX.tmemPairBlocking.covered
          ⟨DStart.evPc DStart.Site.alloc, _, _, _, hal, trivial⟩ (by omega)
        rw [show cta * L.block = cta * L.block + 0 * 32 by simp] at hcov
        obtain ⟨r, hr, hri⟩ := covered_record hX hto hcov
        obtain ⟨hcta, hw0, -⟩ := record_info hX hto hr
        have hwi : r.own.event L 0 = (cta * L.block, k0) := by
          simp [WarpRequest.event, hw0, hcta, hri]
        obtain ⟨base, hwa⟩ : ∃ base, r.action = .alloc 512 base := by
          obtain ⟨-, -, -, hreq, -⟩ := record_info hX hto hr
          have hev := ((hX.tmemPair.1 _).1 r hr).2.2.2.2.1 0
          rw [hwi, hal] at hev
          simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq,
            TcKind.resource.injEq] at hev
          exact Tmem.Action.request_eq_alloc (hreq.trans hev.2.2.2.symm)
        obtain ⟨-, rfl⟩ := alloc_zero hX hto hr _ _ hwa
        exact hX.tmemPairResult (cta * L.block, k0) _ .one _ 512 hal cta r 0 hr hwi hwa pc a bs hget

end
end PTX.Kernels.InklingRelDecode.Proof.Tmem1
