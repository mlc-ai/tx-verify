-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.PrologueIndex
public import Kernels.Fp16Gemm8192.Proof.Thread.RankDefs
public import Kernels.Fp16Gemm8192.Proof.Thread.Prologue
public import Kernels.Fp16Gemm8192.Proof.Thread.Mma
public import Lemmas.Flow.TcTmpl

@[expose] public section

/-! # The MMA warps' path to their election

A thread of warp 8 or 9 runs the common prologue (its shuffle, its fence, its arrival and wait at
the cluster barrier, its register count) and then reaches the MMA state `mmaStart`. `mmaPath k`
says where the thread stands before its `k`-th event, for `k` from 1 to 6: the prologue's sites,
and at 6 the MMA state. Both the elected threads (`MmaLeader`) and the unelected ones go through
this path. An execution where no lane elects keeps the thread at most six events long: a seventh
event would fire the election's template, and the full mask makes that template an election event.
So the thread's final state is one of the six states of its path, none of them exits, and each one
is at most 58 in the sequential schedule. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A full-mask election fires an election event: its mask reads as the full mask, which holds
every lane below 32, so the election's template does not fault. -/
theorem fires_elect_full {A : List Assumption} {g : Nat} {t : TState}
    {dst : Option Nat} {p : Nat} {mask : Opnd} {pc : Nat} {e : Event} {o : Option TState}
    {bits : BitVec 64} (hm : readBits L g t 32 mask = .ok bits) (hb : bits.toNat = 4294967295)
    (hf : Fires pc (eventTmpl A L g t (.warp ⟨.elect, none, [dst, some p], [], some mask⟩)) e o) :
    ∃ inst leader, e = ⟨pc, .elect 4294967295 inst leader⟩ := by
  have hlane : laneOf L g < 32 := by
    unfold laneOf
    exact Nat.mod_lt _ (by norm_num)
  have hmem : electMember bits.toNat (laneOf L g) := by
    unfold electMember
    refine ⟨hlane, ?_⟩
    have h32 : (4294967295 : Nat) = 2 ^ 32 - 1 := by norm_num
    rw [hb, h32, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hlane
  simp only [eventTmpl, warpTmpl_elect, electTmpl, hm] at hf
  rw [ite_eq_left hmem] at hf
  obtain ⟨inst, leader, rfl, -⟩ := hf
  exact ⟨inst, leader, by rw [hb]⟩

set_option maxHeartbeats 4000000 in
/-- The shuffle returns the warp index, which is neither zero nor the first warp's, so the
thread's first event leaves it at its fence. -/
theorem mmaPath1 (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat}
    (hg : g < L.threads) (hw0 : Prologue.warpOf L g ≠ 0)
    (h0 : 0 < (X.tr g).length) :
    Frame.stateAt (code L) X g 1 = some (some (.inl ⟨.fence, Prologue.warpOf L g⟩)) := by
  rw [stateAt_one hpre hX hg h0, ite_eq_right hw0]
  simp [Prologue.afterElect, Prologue.afterInits, Prologue.first_false_of_warp hw0, hw0]

set_option maxHeartbeats 4000000 in
/-- The fence is followed by the fence after the initialization. -/
theorem mmaPath2 (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat}
    (hg : g < L.threads) (hw0 : Prologue.warpOf L g ≠ 0)
    (h1 : 1 < (X.tr g).length) :
    Frame.stateAt (code L) X g 2 = some (some (.inl ⟨.fenceInit, Prologue.warpOf L g⟩)) := by
  obtain ⟨e, he⟩ : ∃ e, (X.tr g)[1]? = some e := ⟨_, List.getElem?_eq_getElem h1⟩
  show Frame.stateAt (code L) X g (1 + 1) = _
  rw [stateAt_succ_inl he (mmaPath1 hpre hX hg hw0 (by omega))]
  simp [Prologue.next]

set_option maxHeartbeats 4000000 in
/-- The fence after the initialization is followed by the cluster arrive. -/
theorem mmaPath3 (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat}
    (hg : g < L.threads) (hw0 : Prologue.warpOf L g ≠ 0)
    (h2 : 2 < (X.tr g).length) :
    Frame.stateAt (code L) X g 3 = some (some (.inl ⟨.arrive, Prologue.warpOf L g⟩)) := by
  obtain ⟨e, he⟩ : ∃ e, (X.tr g)[2]? = some e := ⟨_, List.getElem?_eq_getElem h2⟩
  show Frame.stateAt (code L) X g (2 + 1) = _
  rw [stateAt_succ_inl he (mmaPath2 hpre hX hg hw0 (by omega))]
  simp [Prologue.next]

set_option maxHeartbeats 4000000 in
/-- The cluster arrive is followed by the cluster wait. -/
theorem mmaPath4 (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat}
    (hg : g < L.threads) (hw0 : Prologue.warpOf L g ≠ 0)
    (h3 : 3 < (X.tr g).length) :
    Frame.stateAt (code L) X g 4 = some (some (.inl ⟨.wait, Prologue.warpOf L g⟩)) := by
  obtain ⟨e, he⟩ : ∃ e, (X.tr g)[3]? = some e := ⟨_, List.getElem?_eq_getElem h3⟩
  show Frame.stateAt (code L) X g (3 + 1) = _
  rw [stateAt_succ_inl he (mmaPath3 hpre hX hg hw0 (by omega))]
  simp [Prologue.next]

set_option maxHeartbeats 4000000 in
/-- The cluster wait of warps 8 and 9 (`w / 4 = 2`) is followed by the register count. -/
theorem mmaPath5 (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat}
    (hg : g < L.threads) (hw0 : Prologue.warpOf L g ≠ 0) (hq : Prologue.warpOf L g / 4 = 2)
    (h4 : 4 < (X.tr g).length) :
    Frame.stateAt (code L) X g 5 = some (some (.inl ⟨.setMaxReg, Prologue.warpOf L g⟩)) := by
  obtain ⟨e, he⟩ : ∃ e, (X.tr g)[4]? = some e := ⟨_, List.getElem?_eq_getElem h4⟩
  show Frame.stateAt (code L) X g (4 + 1) = _
  rw [stateAt_succ_inl he (mmaPath4 hpre hX hg hw0 (by omega))]
  simp [Prologue.next, hq]

set_option maxHeartbeats 4000000 in
/-- The register count of warps 8 and 9 is followed by their MMA state. -/
theorem mmaPath6 (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat}
    (hg : g < L.threads) (hw : Prologue.warpOf L g = 8 ∨ Prologue.warpOf L g = 9)
    (h5 : 5 < (X.tr g).length) :
    Frame.stateAt (code L) X g 6 =
      some (some (.inr (.mma (Prologue.mmaStart L g (Prologue.warpOf L g))))) := by
  obtain ⟨e, he⟩ : ∃ e, (X.tr g)[5]? = some e := ⟨_, List.getElem?_eq_getElem h5⟩
  show Frame.stateAt (code L) X g (5 + 1) = _
  rw [stateAt_succ_inl he (mmaPath5 hpre hX hg (by omega) (by omega) (by omega))]
  have h11 : Prologue.warpOf L g ≠ 11 := by omega
  have h10 : Prologue.warpOf L g ≠ 10 := by omega
  simp [Prologue.next, h11, h10, hw]

set_option maxHeartbeats 8000000 in
/-- **An MMA thread without an election is before its election.** A thread of warp 8 or 9 on a
leader CTA with no election event has at most six events, and its final state is a prologue
state (no exit, time at most 56) or its MMA election state (no exit, time 58). -/
theorem mma_unelected_thm (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) :
    ∀ {g : Nat}, g < L.threads → g / L.block % 2 = 0 →
    (g % L.block / 32 = 8 ∨ g % L.block / 32 = 9) →
    (∀ j pc mask inst leader, ¬ X.Elect (g, j) pc mask inst leader) →
    ∃ d, Frame.stateAt (code L) X g (X.tr g).length = some (some d) ∧ d.exitOff = none ∧
      d.vtime L g (X.tr g) ≤ 58 := by
  intro g hg hlead hw hnoel
  have hw89 : Prologue.warpOf L g = 8 ∨ Prologue.warpOf L g = 9 := hw
  have hleader : Loader.leader L g = true := by simp [Loader.leader, hlead]
  -- A seventh event would be the election, which the full mask makes an election event.
  have hn6 : (X.tr g).length ≤ 6 := by
    by_contra hlt
    obtain ⟨e6, he6⟩ : ∃ e, (X.tr g)[6]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hs6 := mmaPath6 hpre hX hg hw89 (by omega)
    obtain ⟨m0, hm0s, hm0⟩ : ∃ m0 : Mma.D, m0.site = .elect ∧
        Frame.stateAt (code L) X g 6 = some (some (.inr (.mma m0))) :=
      ⟨Prologue.mmaStart L g (Prologue.warpOf L g), by simp [Prologue.mmaStart, hleader], hs6⟩
    obtain ⟨s, _, _, _, _, _, _, _⟩ := m0
    simp only at hm0s
    subst hm0s
    obtain ⟨t, ins, _, hat, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he6 hm0
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_3)
    have hmask : readBits L g t 32 (.reg 836) = .ok (BitVec.ofNat 64 4294967295) :=
      readBits_b32 (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom
        (show 836 ∈ Flow.live Mma.Site.elect.pc by table_decide))) (by decide)
    obtain ⟨inst, leader, rfl⟩ := fires_elect_full hmask (by decide) hfire
    exact hnoel 6 _ 4294967295 inst leader he6
  rcases (show (X.tr g).length = 0 ∨ (X.tr g).length = 1 ∨ (X.tr g).length = 2 ∨
      (X.tr g).length = 3 ∨ (X.tr g).length = 4 ∨ (X.tr g).length = 5 ∨
      (X.tr g).length = 6 by omega) with h | h | h | h | h | h | h
  · refine ⟨.inl ⟨.shfl, 0⟩, ?_, rfl, ?_⟩
    · rw [h]
      exact stateAt_zero L X g
    · simp [ThreadD.vtime, Prologue.Site.vtime]
  · refine ⟨.inl ⟨.fence, Prologue.warpOf L g⟩, ?_, rfl, ?_⟩
    · rw [h]
      exact mmaPath1 hpre hX hg (by omega) (by omega)
    · simp [ThreadD.vtime, Prologue.Site.vtime]
  · refine ⟨.inl ⟨.fenceInit, Prologue.warpOf L g⟩, ?_, rfl, ?_⟩
    · rw [h]
      exact mmaPath2 hpre hX hg (by omega) (by omega)
    · simp [ThreadD.vtime, Prologue.Site.vtime]
  · refine ⟨.inl ⟨.arrive, Prologue.warpOf L g⟩, ?_, rfl, ?_⟩
    · rw [h]
      exact mmaPath3 hpre hX hg (by omega) (by omega)
    · simp [ThreadD.vtime, Prologue.Site.vtime]
  · refine ⟨.inl ⟨.wait, Prologue.warpOf L g⟩, ?_, rfl, ?_⟩
    · rw [h]
      exact mmaPath4 hpre hX hg (by omega) (by omega)
    · simp [ThreadD.vtime, Prologue.Site.vtime]
  · refine ⟨.inl ⟨.setMaxReg, Prologue.warpOf L g⟩, ?_, rfl, ?_⟩
    · rw [h]
      exact mmaPath5 hpre hX hg (by omega) (by omega) (by omega)
    · simp [ThreadD.vtime, Prologue.Site.vtime]
  · refine ⟨.inr (.mma (Prologue.mmaStart L g (Prologue.warpOf L g))), ?_, ?_, ?_⟩
    · rw [h]
      exact mmaPath6 hpre hX hg hw89 (by omega)
    · simp [ThreadD.exitOff, Mma.exitOff, Prologue.mmaStart, hleader]
    · simp [ThreadD.vtime, Mma.vtime, Prologue.mmaStart, hleader]

end
end PTX.Kernels.Fp16Gemm8192.Proof
