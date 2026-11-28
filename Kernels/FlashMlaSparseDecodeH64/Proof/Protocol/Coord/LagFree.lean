-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Coord.LagReady
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.TmaLane
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Elect
public import Lemmas.Protocol.KRingFirst
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Bar0
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.ObjNe
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Export.Bar
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Export.Time
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.Time
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Time

@[expose] public section

/-! # The index ring's free side: progress row (`coordFree`, waits at 2446 and 2534)

The index lanes wait at pc 2446 or 2534 on `coordFree j` of their CTA with the parity of their
successful polls plus one (the first use of each slot passes). Block `r` of slot `j = r % 4` is
released by the arrivals of warpgroup 0's 128 lanes at `cfArrW0 r` and of the TMA lane at
`cfArrT r`, awaited by the index lanes in block `r + 4` at `cfWait (r + 4)`. The schedule
(`coordFree_lag`, `Sched.LagN`, `δ = 1`): `τ u = 0` for `u = 0`, else
`cfArrW0 (4 (u - 1) + j) + 2`; producers warpgroup 0's lanes (`wg0_cfEarly`, `wg0_cfExit`) and
the CTA's TMA producer (`TmaProd`, `tma_producer`: before every channel event, or the election's
winner with `tma_cfEarly`, `tma_cfExit`), short of the CTA's uses of the slot; consumers the lanes
whose next event is one of the two waits (`ix_cfWait`).

At a blocked poll with a successful earlier poll, the final phase is the waiter's successful
polls less one and some consumer of the ring has made no more arrivals (`Unit.Obj.reach_short`,
reuse paths `cfReach` from the ring, `KRing.reachE`). The ring's 129th consumer `tmaThread` is
the TMA producer when it has arrived (`cfArr_tma`), else the producer has no arrival either.
Before the waiter's first successful poll the object is in phase 0 (`KRing.empty_first`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing

noncomputable section
set_option maxRecDepth 4000

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The producers of `coordFree j` of CTA `c` while they lag: warpgroup 0's lanes and the TMA
producer, short of the uses of the slot. -/
def CfProd (P : Params) (L : Launch) (X : Execution) (c : Nat) (j : Fin 4) (y : Nat) : Prop :=
  ((∃ b < 128, y = c * L.block + b) ∨ TmaProd P L X c y) ∧
    arrivals (mbarLoc L c (.coordFree j)) (X.tr y) < ringUses 4 j.val (blocksOf P L c)

/-- Lane `g`'s next event is an index lane's wait (pc 2446 or 2534) on `coordFree j` of CTA
`c`. -/
def CfCons (L : Launch) (m : Mem0) (X : Execution) (c : Nat) (j : Fin 4) (g : Nat) : Prop :=
  ∃ pc p ok acq sc, (pc = 2446 ∨ pc = 2534) ∧ Sched.NextEv L kernel Assumptions.all m X g
    ⟨pc, .wait (mbarLoc L c (.coordFree j)) p ok acq sc⟩

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
include hp hX hFw

/-- **The `coordFree` schedule** of slot `j` of CTA `c`. -/
theorem coordFree_lag (hub : ¬ HasUb X) (c : Nat) (j : Fin 4) :
    Sched.LagN (timed P L) X (mbarLoc L c (.coordFree j)) 1 (CfProd P L X c j)
      (CfCons L m X c j) (fun u => if u = 0 then 0 else cfArrW0 (4 * (u - 1) + j.val) + 2)
      (ringUses 4 j.val (blocksOf P L c)) (arrivesOn (mbarLoc L c (.coordFree j))) := by
  have hj := j.isLt
  refine ⟨fun a b h => ?_, fun g hg => ?_, fun y hy hyt => ?_, fun y k pc hy hx => ?_,
    fun g hg => ?_⟩
  · simp only [cfArrW0, frame, stride, loopBase, wg0Off, w0ArrV]
    split_ifs <;> omega
  · obtain ⟨pc, p, ok, acq, sc, hpc, hn⟩ := hg
    obtain ⟨-, -, -, hw⟩ := ix_cfWait hp hX hFw hpc hn
    split_ifs with h0
    · exact Nat.zero_le _
    · simp only [cfWait, cfArrW0, frame, stride, loopBase, ixOff, ixWait, wg0Off, w0ArrV] at hw ⊢
      omega
  · obtain ⟨hk, hlt⟩ := hy
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rcases hk with ⟨b, hb, rfl⟩ | ⟨hyc, hw, ⟨-, ht⟩ | ⟨k, inst, hk⟩⟩
    · have hyc : (c * L.block + b) / L.block = c := by rw [hp.block]; omega
      have hw : MbarRow.warp L (c * L.block + b) < 4 := by
        simp only [MbarRow.warp, tidOf_x_eq hp, hp.block]
        omega
      have := wg0_cfEarly hp hX hFw hub hw hyt j (by simp only [MbarRow.loc, hyc]; exact hlt)
      simp only [MbarRow.loc, hyc, arrivals] at this
      omega
    · simp only [electSlot, tmaOrg, cfArrW0, frame, stride, loopBase, wg0Off, w0ArrV] at ht ⊢
      omega
    · have := tma_cfEarly hp hX hFw hk hub hyc hlt
      simp only [arrivals, cfArrT, cfArrW0, frame, stride, loopBase, tmaOff, tmaCf, wg0Off,
        w0ArrV] at this ⊢
      omega
  · obtain ⟨hk, -⟩ := hy
    rcases hk with ⟨b, hb, rfl⟩ | ⟨hyc, hw, ⟨hnx, -⟩ | ⟨k', inst, hk⟩⟩
    · have hyc : (c * L.block + b) / L.block = c := by rw [hp.block]; omega
      have hw : MbarRow.warp L (c * L.block + b) < 4 := by
        simp only [MbarRow.warp, tidOf_x_eq hp, hp.block]
        omega
      have := wg0_cfExit hp hX hFw hw j hx (startup_exit hp hX hFw hx)
      simp only [MbarRow.loc, hyc] at this
      exact this
    · exact (hnx k pc hx).elim
    · exact tma_cfExit hp hX hFw hk hyc hx
  · obtain ⟨pc, p, ok, acq, sc, hpc, hn⟩ := hg
    have := (ix_cfWait hp hX hFw hpc hn).2.2.1
    omega

variable (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : CoordInputs L X)

include hR in
omit hp hFw in
/-- **A lane of warp 5 that arrived on `coordFree s` of its CTA is the CTA's `tmaThread`.** -/
theorem cfArr_tma (hO : TmaOne L X) {c y : Nat} {s : Fin 4} (hw : MbarRow.warp L y = 5)
    (hyc : y / L.block = c) (hpos : 0 < arrivals (mbarLoc L c (.coordFree s)) (X.tr y)) :
    y = tmaThread L X c := by
  obtain ⟨e, he, hok⟩ := List.countP_pos_iff.mp hpos
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
  have hget : X.get (y, k) = some (X.tr y)[k] := List.getElem?_eq_getElem hk
  generalize (X.tr y)[k] = ev at hok hget
  obtain ⟨pc, kind⟩ := ev
  cases kind with
  | arrive l tx cnt rel sc =>
    simp only [arrivesOn, sourceArrive, decide_eq_true_eq] at hok
    subst hok
    rcases coordFree_use hR (Frame.lt_of_get hX hget) hget rfl with ⟨n, h⟩ |
      ⟨⟨q, ⟨ok, h⟩, -⟩, -⟩ | ⟨hcc, -, -⟩
    · cases h
    · cases h
    · rcases hcc with ⟨h4, -, -⟩ | ⟨hT, hu⟩
      · rw [hw] at h4
        omega
      · rw [← hyc]
        exact tma_thread_eq hO hget (fun _ h => by cases h) hT hu
  | _ => simp [arrivesOn, sourceArrive] at hok

include hR hI hB hN

/-- **The reuse paths of `coordFree s`** as index lane `a` polls it (`KRing.reachE`). -/
theorem cfReach (c : Nat) (s : Fin 4) (a : Fin 32) :
    Unit.Reach L kernel Assumptions.all X (mbarLoc L c (.coordFree s)) 129 (coordCons L X c) 1
      (idxLane L c a) :=
  fun _ hx _ hj => (coordSlot hp hX hFw hR hI hB hN c s).reachE hX hx a (by omega) (by omega)

/-- **An index lane's wait on `coordFree s` is blocked** by a lagging consumer of the ring, when
the object's records do not fault. -/
theorem coordFree_blk (hub : ¬ HasUb X) {g q pc : Nat} {s : Fin 4} {sc : MbarScope}
    (hpc : pc = 2446 ∨ pc = 2534)
    (hff : ∀ r ∈ X.objects (MbarRow.loc L g (.coordFree s)), r.fault = none)
    (hq : q = (okPolls (MbarRow.loc L g (.coordFree s)) (X.tr g) + 1) % 2)
    (hrel : Step.Released L X g)
    (hn : Sched.NextEv L kernel Assumptions.all m X g
      ⟨pc, .wait (MbarRow.loc L g (.coordFree s)) q false true sc⟩) :
    Sched.WaitBlk (timed P L) X g (MbarRow.loc L g (.coordFree s)) q := by
  simp only [MbarRow.loc] at hff hq hn ⊢
  have hg := hn.lt
  have hb := hp.block
  obtain ⟨hw7, -, hlt, -⟩ := ix_cfWait hp hX hFw hpc hn
  simp only [MbarRow.warp, tidOf_x_eq hp] at hw7
  have ha : idxLane L (g / L.block) ⟨g % 384 - 224, by omega⟩ = g := by
    simp only [idxLane, hb]
    omega
  have hb0 := bar0_next hp hFw hn (fun _ h => by cases h) (by show 97 < pc; omega)
  have O := coordFree_obj hp hX hFw hR hI hB hN.tmaOne (g / L.block) s
  obtain ⟨st, hst⟩ := Unit.final_of_init hX O.init O.noInval
    (objects_ne hp hX hFw hI hg (.inr ⟨rfl, hrel⟩) (k := (X.tr g).length)
      (by rwa [List.take_length]) (.coordFree s))
  refine ⟨st, hst, fun hpar => ?_⟩
  rw [hq, Nat.mod_mod] at hpar
  by_cases h0 : okPolls (mbarLoc L (g / L.block) (.coordFree s)) (X.tr g) = 0
  · rw [h0] at hpar
    have := (coordSlot hp hX hFw hR hI hB hN (g / L.block) s).empty_first hX O
      (fun _ h => h) (by decide) ⟨g % 384 - 224, by omega⟩ (by
        show okPolls (mbarLoc L (g / L.block) (.coordFree s))
          (X.tr (idxLane L (g / L.block) ⟨g % 384 - 224, by omega⟩)) = 0
        rw [ha]
        exact h0) hst
    omega
  have hpar' : st.phase % 2 = (okPolls (mbarLoc L (g / L.block) (.coordFree s))
      (X.tr (idxLane L (g / L.block) ⟨g % 384 - 224, by omega⟩)) + 1) % 2 := by
    rw [ha]
    exact hpar
  obtain ⟨hph, b, hbl⟩ := O.reach_short hX (cfReach hp hX hFw hR hI hB hN (g / L.block) s _) hff
    hst (by rw [ha]; omega) hpar'
  rw [ha] at hph
  have hne : X.tr g ≠ [] := by
    intro h
    simp [h] at hb0
  have hcons : CfCons L m X (g / L.block) s g := ⟨_, _, _, _, _, hpc, hn⟩
  have hL := coordFree_lag hp hX hFw hub (g / L.block) s
  by_cases hb128 : b.val < 128
  · simp only [coordCons, hb128, ↓reduceIte] at hbl
    have hyc : (g / L.block * L.block + b.val) / L.block = g / L.block := by rw [hb]; omega
    exact hL.blk hX hub hg hcons hne
      ⟨.inl ⟨b.val, hb128, rfl⟩, by simp only [arrivals] at hbl ⊢; omega⟩ (by rw [hb]; omega)
      (by rw [hyc]) (by simp only [arrivals] at hbl ⊢; omega)
  · simp only [coordCons, hb128, ↓reduceIte] at hbl
    obtain ⟨y, hyt, hyP, -⟩ := tma_producer hp hX hFw hub (c := g / L.block) (by rw [hb]; omega)
    obtain ⟨hyc, hyw, -⟩ := id hyP
    have hy : arrivals (mbarLoc L (g / L.block) (.coordFree s)) (X.tr y) ≤ st.phase := by
      by_cases hpos : 0 < arrivals (mbarLoc L (g / L.block) (.coordFree s)) (X.tr y)
      · rw [cfArr_tma hX hR hN.tmaOne hyw hyc hpos]
        exact hbl
      · omega
    exact hL.blk hX hub hg hcons hne ⟨.inr hyP, by simp only [arrivals] at hy ⊢; omega⟩
      hyt (by rw [hyc]) (by simp only [arrivals] at hy ⊢; omega)

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
