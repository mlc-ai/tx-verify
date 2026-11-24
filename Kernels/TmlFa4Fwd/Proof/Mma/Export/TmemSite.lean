-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Kernel.FrameU

public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Issue
public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Win
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Smem
public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Words
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Coll
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Mma.Export.SafePre
import Kernels.TmlFa4Fwd.Proof.Mma.Ref
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # An MMA site's operation on the trace: one state to its Tensor Memory facts -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The trace counts of a lane that won an election, from its place. -/
theorem counts_at {k : Nat} {d : D} {n : Cls → Nat} {r : Nat} {w : Bool}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (minj p L g d n)))
    (hQ : RefQ p L g d.site.ord d.v (rc n) r w) (hw : 1 ≤ n (.mma .won)) :
    (∀ o, okPolls (Tm.bar L (g / L.block) o) ((X.tr g).take k) = acqAt d.site.ord r o) ∧
      ∀ o, ((X.tr g).take k).countP (commitsTo (Tm.bar L (g / L.block) o)) =
        commitAt d.site.ord r o := by
  have hwt : w = true := by
    have h1 := hQ.won
    cases w
    · simp only [rc, Bool.false_eq_true, ite_false] at h1; omega
    · rfl
  subst hwt
  refine ⟨fun o => ?_, fun o => ?_⟩
  · have h := hQ.acq o
    rw [← h]
    show _ = n (.mma (.acquire (bl L g o)))
    rw [← count hσ]
    rfl
  · have h := hQ.com o
    simp only [ite_true] at h
    rw [← h]
    show _ = n (.mma (.commit (bl L g o)))
    rw [← count hσ]
    rfl

/-- The counts of a place that the Tensor Memory facts use. -/
structure PlaceQk (pl r st u : Nat) : Prop where
  com : commitAt pl r (80 + 8 * st) = u
  p : acqAt pl r (96 + 8 * st) = u
  p2 : acqAt pl r (112 + 8 * st) = u
  kv : acqAt pl r 32 + acqAt pl r 40 + acqAt pl r 48 = 2 * u + 1
  rel : commitAt pl r 56 + commitAt pl r 64 + commitAt pl r 72 ≤ 2 * u
  q : acqAt pl r (8 * st) = 1
  qrel : commitAt pl r (16 + 8 * st) = 0
  el : electAll pl r + 1 = 8 * u + (if st = 0 then (if u = 0 then 2 else 0) else 4)

structure PlacePv (pl r st u hi : Nat) : Prop where
  com : commitAt pl r (80 + 8 * st) = u + 1
  p : acqAt pl r (96 + 8 * st) = u + 1
  p2 : acqAt pl r (112 + 8 * st) = u + hi
  kv : 2 * u + 2 ≤ acqAt pl r 32 + acqAt pl r 40 + acqAt pl r 48 ∧
    acqAt pl r 32 + acqAt pl r 40 + acqAt pl r 48 ≤ 2 * u + 2 + st
  rel : commitAt pl r 56 + commitAt pl r 64 + commitAt pl r 72 ≤ 2 * u + 1
  oc : commitAt pl r (144 + 8 * st) = 0
  el : st = 1 → electAll pl r = 8 * u + 9

theorem ringCount_sum (n : Nat) : ringCount n 0 + ringCount n 1 + ringCount n 2 = n := by
  simp only [ringCount]
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 3 ∧ n = 3 * q + r :=
    ⟨n / 3, n % 3, Nat.mod_lt _ (by decide), by omega⟩
  interval_cases r <;> omega

theorem acqAt_kv (q r : Nat) : acqAt q r 32 + acqAt q r 40 + acqAt q r 48 = ringAcq q r := by
  rw [← ringCount_sum (ringAcq q r)]
  simp only [acqAt]
  norm_num

theorem commitAt_kv (q r : Nat) :
    commitAt q r 56 + commitAt q r 64 + commitAt q r 72 = ringRel q r := by
  rw [← ringCount_sum (ringRel q r)]
  simp only [commitAt]
  norm_num

/-- The place arithmetic of one literal place. -/
macro "place" : tactic => `(tactic| (
  constructor <;> (try rw [acqAt_kv]) <;> (try rw [commitAt_kv]) <;>
    simp only [commitAt, acqAt, electAll, ringAcq, ringRel, pq] <;> norm_num <;> (try omega)))

theorem place_qk0 : PlaceQk 6 0 0 0 := by place
theorem place_qk1 : PlaceQk 12 0 1 0 := by place
theorem place_qk2 (r : Nat) : PlaceQk 32 r 0 (r + 1) := by place
theorem place_qk3 (r : Nat) : PlaceQk 45 r 1 (r + 1) := by place
theorem place_pv0 (r : Nat) : PlacePv 26 r 0 r 0 := by place
theorem place_pv0' (r : Nat) : PlacePv 28 r 0 r 1 := by place
theorem place_pv1 (r : Nat) : PlacePv 39 r 1 r 0 := by place
theorem place_pv1' (r : Nat) : PlacePv 41 r 1 r 1 := by place
theorem place_pv2 (r : Nat) : PlacePv 70 r 0 r 0 := by place
theorem place_pv2' (r : Nat) : PlacePv 72 r 0 r 1 := by place
theorem place_pv3 (r : Nat) : PlacePv 77 r 1 r 0 := by place
theorem place_pv3' (r : Nat) : PlacePv 79 r 1 r 1 := by place

theorem qk_of_place {k : Nat} {d : D} {n : Cls → Nat} {r : Nat} {w : Bool} {st u : Nat}
    {b : Fin 4} {j : Fin 8} {e : Event}
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (minj p L g d n)))
    (hQ : RefQ p L g d.site.ord d.v (rc n) r w) (hw : 1 ≤ n (.mma .won))
    (hI : IssueQk L g d.v b j e.kind) (hdst : (truncBits 32 (qkAcc d.v b)).toNat = 128 * st)
    (hP : PlaceQk d.site.ord r st u)
    (hA : ∀ da, TcShared.decode (qv L (neg (.qk b j)) j).toNat = some da → da = Tm.qkA L st j)
    (hB : ∀ db, TcShared.decode (qlo (qkStart d.v b) j ||| dhi <<< 32).toNat = some db →
      db = Tm.qkB L (2 * u % 3) j) : Tm.Qk L X g k st u j := by
  obtain ⟨ha, hc⟩ := counts_at hσ hQ hw
  obtain ⟨da, db, hda, hdb, hk⟩ := hI
  refine ⟨⟨e.pc, da, db, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [he, ← hdst]
    obtain ⟨pc, kd⟩ := e
    simp only at hk
    rw [hk]
  · rintro d' s acc mask ⟨pc, hi⟩
    rw [he] at hi
    cases hi
    simp only [Kind.tc.injEq, TcKind.mma.injEq] at hk
    obtain ⟨-, rfl, -⟩ := hk
    exact ⟨hA da hda, hB db hdb⟩
  · exact (hc _).trans hP.com
  · exact (ha _).trans hP.p
  · exact (ha _).trans hP.p2
  · unfold Tm.kvPolls; rw [ha, ha, ha]; exact hP.kv
  · unfold Tm.kvRels; rw [hc, hc, hc]; exact hP.rel
  · exact (ha _).trans hP.q
  · exact (hc _).trans hP.qrel
  · rw [mma_elections hX hσ hQ]; exact hP.el

theorem pv_of_place {k : Nat} {d : D} {n : Cls → Nat} {r : Nat} {w : Bool} {st u : Nat}
    {b : Fin 4} {j : Fin 8} {e : Event}
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (minj p L g d n)))
    (hQ : RefQ p L g d.site.ord d.v (rc n) r w) (hw : 1 ≤ n (.mma .won))
    (hI : IssuePv L g d.v b j e.kind) (hdst : (truncBits 32 (pvAcc d.v b)).toNat = 256 + 128 * st)
    (hA : (truncBits 32 (pvA d.v b)).toNat = 128 * st + 64)
    (hacc : (if j.val = 0 then scmpi .ne .b d.v.accum 0 else true) = (j.val != 0 || u != 0))
    (hP : PlacePv d.site.ord r st u (if 5 < j.val then 1 else 0))
    (hB : ∀ db, TcShared.decode (pvlo (pvB d.v b) j.val ||| dhi <<< 32).toNat = some db →
      db = Tm.pvB L ((2 * u + 1) % 3) j) : Tm.Pv L X g k st u j := by
  obtain ⟨ha, hc⟩ := counts_at hσ hQ hw
  obtain ⟨db, hdb, hk⟩ := hI
  refine ⟨⟨e.pc, db, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [he, ← hdst, ← hacc]
    obtain ⟨pc, kd⟩ := e
    simp only at hk
    rw [hk, hA]
    have e1 : (128 * st + 64) / 2 ^ 16 * 2 ^ 16 +
        (((128 * st + 64 : Nat) % 2 ^ 16 : Int) + (8 * j.val : Nat)).toNat =
        128 * st + 64 + 8 * j.val := by omega
    rw [e1]
  · rintro d' s acc mask ⟨pc, hi⟩
    rw [he] at hi
    cases hi
    simp only [Kind.tc.injEq, TcKind.mma.injEq] at hk
    obtain ⟨-, rfl, -⟩ := hk
    exact hB db hdb
  · exact (hc _).trans hP.com
  · exact (ha _).trans hP.p
  · exact (ha _).trans hP.p2
  · unfold Tm.kvPolls; rw [ha, ha, ha]; exact hP.kv
  · unfold Tm.kvRels; rw [hc, hc, hc]; exact hP.rel
  · exact (hc _).trans hP.oc
  · intro h; rw [mma_elections hX hσ hQ]; exact hP.el h

theorem accum_of {v : V} {r : Nat} (h : LoopRegs v r) : scmpi .ne .b v.accum 0 = (r != 0) := by
  obtain ⟨-, -, -, hacc⟩ := h
  rw [hacc]
  by_cases hr : r = 0
  · subst hr; decide
  · rw [ite_eq_right hr]
    have : (r != 0) = true := by simpa using hr
    rw [this]; decide

theorem acc_eq {v : V} {r : Nat} (h : LoopRegs v r) (j : Fin 8) :
    (if j.val = 0 then scmpi .ne .b v.accum 0 else true) = (j.val != 0 || r != 0) := by
  rw [accum_of h]
  split <;> simp_all

theorem kn_qk_tab : (∀ j, kn (.qk 0 j) 1 = true) ∧ (∀ j, kn (.qk 1 j) 2 = true) ∧
    (∀ j, kn (.qk 2 j) 1 = true) ∧ ∀ j, kn (.qk 3 j) 2 = true := by decide

theorem kn_pv_tab : (∀ j, kn (.pv 0 j) 5 = true ∧ kn (.pv 0 j) 3 = true) ∧
    (∀ j, kn (.pv 1 j) 8 = true ∧ kn (.pv 1 j) 7 = true) ∧
    (∀ j, kn (.pv 2 j) 11 = true ∧ kn (.pv 2 j) 9 = true) ∧
    ∀ j, kn (.pv 3 j) 13 = true ∧ kn (.pv 3 j) 12 = true := by decide

theorem pv_ord : ∀ b j, 20 ≤ (Site.pv b j).ord ∧ (Site.pv b j).ord < 100 := by decide

theorem kn_qk0 : (∀ j, kn (.qk 0 j) 0 = true) ∧ (∀ j, kn (.qk 1 j) 0 = true) ∧
    (∀ j, kn (.qk 2 j) 6 = true) ∧ ∀ j, kn (.qk 3 j) 6 = true := by decide

theorem kn_pv4 : (∀ j, kn (.pv 0 j) 4 = true) ∧ (∀ j, kn (.pv 1 j) 4 = true) ∧
    (∀ j, kn (.pv 2 j) 10 = true) ∧ ∀ j, kn (.pv 3 j) 10 = true := by decide

/-- **A QK site's MMA.** -/
theorem qk_site (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat} {d : D}
    {n : Cls → Nat} {e : Event} {b : Fin 4} {j : Fin 8} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (minj p L g d n)))
    (hs : d.site = .qk b j) (hJ : RefCounts p L g (d, rc n)) (hw : 1 ≤ n (.mma .won))
    (hI : IssueQk L g d.v b j e.kind) (hW : WOk L d) :
    ∃ u, Tm.Qk L X g k (b.val % 2) u j := by
  obtain ⟨r, w, hQ, -⟩ := hJ
  have hpre := hQ.pre
  have hregs := hQ.regs
  simp only [hs] at hpre hregs
  have key : ∀ st u n, (truncBits 32 (qkAcc d.v b)).toNat = 128 * st → b.val % 2 = st →
      2 * u % 3 = n → (qkStart d.v b).toNat = 65536 + (L.sharedBase + 68608 + 32768 * n) / 16 →
      PlaceQk (Site.qk b j).ord r st u → Tm.Qk L X g k st u j := fun st u n h1 hb hn hst h2 =>
    qk_of_place hX he hσ hQ hw hI h1 (by rw [hs]; exact h2)
      (fun da hda => hb ▸ qkA_decode hp b j hda)
      (fun db hdb => hn ▸ kB_decode hp (hn ▸ Nat.mod_lt _ (by decide)) hst j hdb)
  have h6 : LoopRegs d.v r → (slotDesc L (slot1 d.v) 65536).toNat =
      65536 + (L.sharedBase + 68608 + 32768 * ((2 * r + 2) % 3)) / 16 := fun hr => by
    rw [(slot1_eq hr).1]
    exact (slotDesc_val hp (Nat.mod_lt _ (by decide))).1
  obtain ⟨hqk0, hqk1, hqk2, hqk3⟩ := kn_qk_tab
  obtain ⟨hkq0, hkq1, hkq2, hkq3⟩ := kn_qk0
  fin_cases b
  · obtain rfl := hpre (by show (6 : Nat) < 20; decide)
    refine ⟨0, key 0 0 0 ?_ rfl rfl ?_ place_qk0⟩
    · have h := hW 1 (by rw [hs]; exact hqk0 j)
      show (truncBits 32 d.v.s1).toNat = _
      rw [show d.v.s1 = i32 0 from h]; rfl
    · have h := hW 0 (by rw [hs]; exact hkq0 j)
      show d.v.s0.toNat = _
      rw [show d.v.s0 = shSrc L {} 0 from h]; exact kv0_val hp
  · obtain rfl := hpre (by show (12 : Nat) < 20; decide)
    refine ⟨0, key 1 0 0 ?_ rfl rfl ?_ place_qk1⟩
    · have h := hW 2 (by rw [hs]; exact hqk1 j)
      show (truncBits 32 d.v.s2).toNat = _
      rw [show d.v.s2 = i32 128 from h]; rfl
    · have h := hW 0 (by rw [hs]; exact hkq1 j)
      show d.v.s0.toNat = _
      rw [show d.v.s0 = shSrc L {} 0 from h]; exact kv0_val hp
  · refine ⟨r + 1, key 0 (r + 1) ((2 * r + 2) % 3) ?_ rfl (by omega) ?_ (place_qk2 r)⟩
    · have h := hW 1 (by rw [hs]; exact hqk2 j)
      show (truncBits 32 d.v.s1).toNat = _
      rw [show d.v.s1 = i32 0 from h]; rfl
    · have h := hW 6 (by rw [hs]; exact hkq2 j)
      show d.v.s6.toNat = _
      rw [show d.v.s6 = slotDesc L (slot1 d.v) 65536 from h]
      exact h6 (hregs (by show 20 ≤ (32 : Nat) ∧ (32 : Nat) < 100; decide))
  · refine ⟨r + 1, key 1 (r + 1) ((2 * r + 2) % 3) ?_ rfl (by omega) ?_ (place_qk3 r)⟩
    · have h := hW 2 (by rw [hs]; exact hqk3 j)
      show (truncBits 32 d.v.s2).toNat = _
      rw [show d.v.s2 = i32 128 from h]; rfl
    · have h := hW 6 (by rw [hs]; exact hkq3 j)
      show d.v.s6.toNat = _
      rw [show d.v.s6 = slotDesc L (slot1 d.v) 65536 from h]
      exact h6 (hregs (by show 20 ≤ (45 : Nat) ∧ (45 : Nat) < 100; decide))

/-- **A PV site's MMA.** -/
theorem pv_site (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat} {d : D}
    {n : Cls → Nat}
    {e : Event} {b : Fin 4} {j : Fin 8} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (minj p L g d n)))
    (hs : d.site = .pv b j) (hJ : RefCounts p L g (d, rc n)) (hw : 1 ≤ n (.mma .won))
    (hI : IssuePv L g d.v b j e.kind) (hW : WOk L d) :
    ∃ u, Tm.Pv L X g k (b.val % 2) u j := by
  obtain ⟨r, w, hQ, -⟩ := hJ
  have hr : LoopRegs d.v r := hQ.regs (by
    simp only [hs]; exact pv_ord b j)
  have key : ∀ st, st < 2 → (truncBits 32 (pvAcc d.v b)).toNat = 256 + 128 * st →
      (truncBits 32 (pvA d.v b)).toNat = 128 * st + 64 →
      PlacePv (Site.pv b j).ord r st r (if 5 < j.val then 1 else 0) →
      pvB d.v b = slotDesc L d.v.slot 67108864 → Tm.Pv L X g k st r j :=
    fun st _ h1 h2 h3 h4 =>
      pv_of_place hX he hσ hQ hw hI h1 h2 (acc_eq hr j) (by rw [hs]; exact h3) fun db hdb => by
        rw [h4, hr.1] at hdb
        exact vB_decode hp (Nat.mod_lt _ (by decide)) (slotDesc_val hp (Nat.mod_lt _ (by decide))).2
          j hdb
  obtain ⟨hpv0, hpv1, hpv2, hpv3⟩ := kn_pv_tab
  obtain ⟨hp40, hp41, hp42, hp43⟩ := kn_pv4
  fin_cases b
  · refine ⟨r, key 0 (by decide) ?_ ?_ ?_ ?_⟩
    · show (truncBits 32 d.v.s5).toNat = _
      rw [show d.v.s5 = i32 256 from hW 5 (by rw [hs]; exact (hpv0 j).1)]; rfl
    · show (truncBits 32 d.v.s3).toNat = _
      rw [show d.v.s3 = i32 64 from hW 3 (by rw [hs]; exact (hpv0 j).2)]; rfl
    · show PlacePv (26 + if 5 < j.val then 2 else 0) _ _ _ _
      split
      · exact place_pv0' r
      · exact place_pv0 r
    · exact hW 4 (by rw [hs]; exact hp40 j)
  · refine ⟨r, key 1 (by decide) ?_ ?_ ?_ ?_⟩
    · show (truncBits 32 d.v.s8).toNat = _
      rw [show d.v.s8 = i32 384 from hW 8 (by rw [hs]; exact (hpv1 j).1)]; rfl
    · show (truncBits 32 d.v.s7).toNat = _
      rw [show d.v.s7 = i32 192 from hW 7 (by rw [hs]; exact (hpv1 j).2)]; rfl
    · show PlacePv (39 + if 5 < j.val then 2 else 0) _ _ _ _
      split
      · exact place_pv1' r
      · exact place_pv1 r
    · exact hW 4 (by rw [hs]; exact hp41 j)
  · refine ⟨r, key 0 (by decide) ?_ ?_ ?_ ?_⟩
    · show (truncBits 32 d.v.s11).toNat = _
      rw [show d.v.s11 = i32 256 from hW 11 (by rw [hs]; exact (hpv2 j).1)]; rfl
    · show (truncBits 32 d.v.s9).toNat = _
      rw [show d.v.s9 = i32 64 from hW 9 (by rw [hs]; exact (hpv2 j).2)]; rfl
    · show PlacePv (70 + if 5 < j.val then 2 else 0) _ _ _ _
      split
      · exact place_pv2' r
      · exact place_pv2 r
    · exact hW 10 (by rw [hs]; exact hp42 j)
  · refine ⟨r, key 1 (by decide) ?_ ?_ ?_ ?_⟩
    · show (truncBits 32 d.v.s13).toNat = _
      rw [show d.v.s13 = i32 384 from hW 13 (by rw [hs]; exact (hpv3 j).1)]; rfl
    · show (truncBits 32 d.v.s12).toNat = _
      rw [show d.v.s12 = i32 192 from hW 12 (by rw [hs]; exact (hpv3 j).2)]; rfl
    · show PlacePv (77 + if 5 < j.val then 2 else 0) _ _ _ _
      split
      · exact place_pv3' r
      · exact place_pv3 r
    · exact hW 10 (by rw [hs]; exact hp43 j)

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option maxHeartbeats 8000000 in
/-- **An MMA is fired at a QK or PV site.** -/
theorem mma_site {d : D} {pc dd : Nat} {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hev : Ev p L g d ⟨pc, .tc (.mma dd sp acc mask)⟩) :
    (∃ b j, d.site = .qk b j) ∨ ∃ b j, d.site = .pv b j := by
  obtain ⟨s, v⟩ := d
  cases s
  case qk b j => exact .inl ⟨b, j, rfl⟩
  case pv b j => exact .inr ⟨b, j, rfl⟩
  all_goals exfalso
  all_goals simp only [Ev] at hev
  all_goals first
    | (unfold Epilogue.Ev at hev; split at hev <;> simp_all [Epilogue.isStore]; done)
    | skip
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals (simp only [reduceCtorEq, Kind.tc.injEq, TcKind.commit.injEq] at *)

/-- The state of the role an MMA is issued from. -/
theorem mma_state (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw : Prologue.warpIndex L g = 12) {k d : Nat} {sp : TcMma.OperandSpec}
    {acc : Bool} {mask : List Nat} (hi : X.MmaIssue (g, k) d sp acc mask) :
    ∃ e dd n, X.get (g, k) = some e ∧
      Frame.stateAt (thread p L) X g k = some (some (minj p L g dd n)) ∧
      RefCounts p L g (dd, rc n) ∧ Ev p L g dd e ∧
      ((∃ b j, dd.site = .qk b j) ∨ ∃ b j, dd.site = .pv b j) := by
  obtain ⟨pc, he⟩ := hi
  have hG := good_at hp hX (Frame.lt_of_get hX he) hw k
  rcases good_cases hp hX he (by intro pc f h; cases h) hG with ⟨s, n, hσ, hS, -⟩ |
    ⟨s, n, hσ, -⟩ | ⟨dd, n, hσ, -, hJ, -⟩
  · exfalso
    obtain ⟨hev, hx, -⟩ := start_fired hp hX he hσ
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site
    case enter r => simp [exit] at hx
    case sh j => fin_cases j <;> simp [Startup.Ev] at hev
    all_goals simp [Startup.Ev] at hev
  · exfalso
    obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ :=
      Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ (by intro f h; cases h)
    have hk3 := Mma.pre_kind hp hat hc hf
    cases s with
    | set => obtain ⟨inst, hk⟩ := hk3.1 rfl; cases hk
    | alloc => have hk := hk3.2.1 rfl; cases hk
    | wr => obtain ⟨c, hk⟩ := hk3.2.2 rfl; cases hk
    | enter => exact absurd hinv.2 (by simp [Mma.Start.exit])
  · have hev := (mfired hp hX he hσ).1
    exact ⟨_, dd, n, he, hσ, hJ, hev, mma_site hev⟩

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option maxHeartbeats 8000000 in
/-- **A commit is fired at a commit site.** -/
theorem commit_site {d : D} {pc : Nat} {s : TcCommit.Spec}
    (hev : Ev p L g d ⟨pc, .tc (.commit s)⟩) : ∃ c, d.site = .cm c := by
  obtain ⟨st, v⟩ := d
  cases st
  case cm c => exact ⟨c, rfl⟩
  all_goals exfalso
  all_goals simp only [Ev] at hev
  all_goals first
    | (unfold Epilogue.Ev at hev; split at hev <;> simp_all [Epilogue.isStore]; done)
    | skip
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals (simp only [reduceCtorEq, Kind.tc.injEq, TcKind.commit.injEq] at *)

/-- The state of the role a commit is issued from. -/
theorem commit_state (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw : Prologue.warpIndex L g = 12) {k : Nat} {s : TcCommit.Spec} (hi : X.Commit (g, k) s) :
    ∃ dd n, g < L.threads ∧
      Frame.stateAt (thread p L) X g k = some (some (minj p L g dd n)) ∧
      winSite dd.site = true := by
  obtain ⟨pc, he⟩ := hi
  have hG := good_at hp hX (Frame.lt_of_get hX he) hw k
  rcases good_cases hp hX he (by intro pc f h; cases h) hG with ⟨s, n, hσ, hS, -⟩ |
    ⟨s, n, hσ, -⟩ | ⟨dd, n, hσ, -, hJ, -⟩
  · exfalso
    obtain ⟨hev, hx, -⟩ := start_fired hp hX he hσ
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site
    case enter r => simp [exit] at hx
    case sh j => fin_cases j <;> simp [Startup.Ev] at hev
    all_goals simp [Startup.Ev] at hev
  · exfalso
    obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ :=
      Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ (by intro f h; cases h)
    have hk3 := Mma.pre_kind hp hat hc hf
    cases s with
    | set => obtain ⟨inst, hk⟩ := hk3.1 rfl; cases hk
    | alloc => have hk := hk3.2.1 rfl; cases hk
    | wr => obtain ⟨c, hk⟩ := hk3.2.2 rfl; cases hk
    | enter => exact absurd hinv.2 (by simp [Mma.Start.exit])
  · obtain ⟨c, hc⟩ := commit_site (mfired hp hX he hσ).1
    exact ⟨dd, n, Frame.lt_of_get hX he, hσ, by rw [hc]; rfl⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
