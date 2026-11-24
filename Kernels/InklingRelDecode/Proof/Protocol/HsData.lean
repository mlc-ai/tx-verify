-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SrAll
public import Kernels.InklingRelDecode.Proof.Protocol.IpAll
public import Kernels.InklingRelDecode.Proof.Protocol.RdAll
public import Kernels.InklingRelDecode.Proof.Protocol.BarLaneAll
public import Kernels.InklingRelDecode.Proof.Safety.All

@[expose] public section

/-!
# The data of the S/P/O handshake package, and the polls of the kernel

The handshake package `Sr.SrPkg` names, for every CTA `c`, the committing lane `cm`, thread 0 of
the default partition `p0`, the Tensor Memory base `tm` and the lanes of the MMA warp `Mma`. Here
they are fixed as functions of the launch and the execution:

* `p0Of L c = c * L.block`, the first thread of the CTA;
* `tmOf c = 0`, the base column of the allocation (`Rs.SmBaseZero`);
* `MmaOf L c`, the 32 threads of warp 7 of the CTA;
* `cmOf L X c`, the thread of warp 7 of the CTA that made a full-mask election returning its own
  lane (`LeadOf`), and the last thread of the CTA's warp 7 when there is none. Two such threads
  are one (`lead_unique`, `ElectOk`).

`poll_class`: every successful poll of a launched thread is an acquire poll at CTA scope, on one
of the handshake's or the ring's barriers of the thread's own CTA, with the role and site that
fires it.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Hs
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady pReady oDone oFinal kvReady kvEmpty)
open PTX.Kernels.InklingRelDecode.Proof.SO (IsMma)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The lanes of the MMA warp (warp 7) of CTA `c`. -/
def MmaOf (L : Launch) (c h : Nat) : Prop :=
  h < L.threads ∧ h / L.block = c ∧ h % L.block / 32 = 7

/-- Thread 0 of CTA `c`. -/
def p0Of (L : Launch) (c : Nat) : Nat := c * L.block

/-- The Tensor Memory base column of every CTA. -/
def tmOf (_ : Nat) : Nat := 0

/-- A lane of the MMA warp of CTA `c` that made a full-mask election returning its own lane. -/
def LeadOf (L : Launch) (X : Execution) (c g : Nat) : Prop :=
  MmaOf L c g ∧ ∃ m pc inst, X.get (g, m) = some ⟨pc, .elect 4294967295 inst (laneOf L g)⟩

open Classical in
/-- The committing lane of CTA `c`: the elected lane of the MMA warp, if one was elected. -/
def cmOf (L : Launch) (X : Execution) (c : Nat) : Nat :=
  if h : ∃ g, LeadOf L X c g then Classical.choose h else c * L.block + 224

/-- **Two elected lanes of the MMA warp of one CTA are one thread** (`ElectOk`, clause 3: one
leader per warp and mask). -/
theorem lead_unique (hX : Consistent L kernel asms mem0 X) {c g h : Nat} (hg : LeadOf L X c g)
    (hh : LeadOf L X c h) : g = h := by
  obtain ⟨⟨hgl, hgc, hgw⟩, m1, pc1, inst1, he1⟩ := hg
  obtain ⟨⟨hhl, hhc, hhw⟩, m2, pc2, inst2, he2⟩ := hh
  have hsw : SameWarp L g h := ⟨⟨hgl, hhl, hgc.trans hhc.symm⟩, by omega⟩
  have hld := hX.elect.2.2 (e := (g, m1)) (f := (h, m2)) _ _ _ inst1 inst2 _ _ he1 he2 hsw
  have hlane : g % L.block = h % L.block := by
    unfold laneOf at hld
    omega
  have h1 := Nat.div_add_mod g L.block
  have h2 := Nat.div_add_mod h L.block
  rw [hgc, hlane] at h1
  rw [hhc] at h2
  omega

/-- **The committing lane is every elected lane.** -/
theorem cm_eq (hX : Consistent L kernel asms mem0 X) {c g : Nat} (hg : LeadOf L X c g) :
    cmOf L X c = g := by
  have hex : ∃ g, LeadOf L X c g := ⟨g, hg⟩
  unfold cmOf
  simp only [hex, dite_true]
  exact lead_unique hX (Classical.choose_spec hex) hg

/-- **The committing lane is a lane of the MMA warp of the CTA.** -/
theorem cm_mma (hpre : Pre Q L mem0) {c : Nat} (hc : c < L.grid) : MmaOf L c (cmOf L X c) := by
  have hb : L.block = 256 := hpre.block
  unfold cmOf
  split
  · rename_i h
    exact (Classical.choose_spec h).1
  · refine ⟨?_, ?_, ?_⟩
    · unfold Launch.threads
      rw [hb]
      have : (c + 1) * 256 ≤ L.grid * 256 := Nat.mul_le_mul_right _ hc
      rw [Nat.add_mul] at this
      omega
    · rw [hb]
      omega
    · rw [hb]
      omega

/-- **`Lane.cm_ok`.** -/
theorem cm_ok (hpre : Pre Q L mem0) {c : Nat} (hc : c < L.grid) :
    cmOf L X c < L.threads ∧ cmOf L X c / L.block = c :=
  ⟨(cm_mma hpre hc).1, (cm_mma hpre hc).2.1⟩

/-- **`Lane.tmOk`.** -/
theorem tmOk (c : Nat) : SO.TmOk (tmOf c) := by
  unfold SO.TmOk tmOf
  omega

/-- **Thread 0 is a softmax thread of its CTA.** -/
theorem p0_soft (hpre : Pre Q L mem0) {c : Nat} (hc : c < L.grid) : Sr.SoftOf L c (p0Of L c) := by
  have hb : L.block = 256 := hpre.block
  unfold Sr.SoftOf p0Of
  refine ⟨?_, ?_, ?_⟩
  · unfold Launch.threads
    rw [hb]
    have : (c + 1) * 256 ≤ L.grid * 256 := Nat.mul_le_mul_right _ hc
    rw [Nat.add_mul] at this
    omega
  · rw [hb]
    omega
  · rw [hb]
    omega

/-- **An MMA is issued by the elected lane of its CTA's MMA warp.** -/
theorem mma_lead (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {x : EvId} (hx : IsMma X x) :
    LeadOf L X (x.1 / L.block) x.1 := by
  obtain ⟨pcx, dx, sx, ax, mx, hxe⟩ := hx.get
  obtain ⟨g, k⟩ := x
  obtain ⟨hg, hw, m0, pc0, inst, ld, hel, hl⟩ :=
    IpMma.mma_event_data hpre hX hf.sound hf.tracked hf.roleWarp hxe
  refine ⟨⟨hg, rfl, ?_⟩, m0, pc0, inst, ?_⟩
  · unfold Worker.warpOf at hw
    exact hw
  · rw [hl]
    exact hel

/-- **Every MMA of CTA `c` is the committing lane's.** -/
theorem mma_cm (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {c : Nat} {x : EvId} (hx : IsMma X x) (hxc : x.1 / L.block = c) :
    x.1 = cmOf L X c := by
  subst hxc
  exact (cm_eq hX (mma_lead hpre hX hf hx)).symm

/-! ### The polls -/

/-- **The successful polls of a launched thread**, by role and site: the softmax region's polls of
`s_ready` (at `waitS`) and of `o_done` (at `waitO`), the loader's poll of `kv_empty`, the MMA
warp's polls of `kv_ready` and `p_ready`, the epilogue's poll of `o_final`; all acquire polls at
CTA scope on a barrier of the thread's own CTA. -/
theorem poll_class (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k pc : Nat} {m : Loc} {p : Nat} {acq : Bool}
    {sc : MbarScope} (he : X.get (g, k) = some ⟨pc, .wait m p true acq sc⟩) :
    acq = true ∧ sc = .cta ∧
      ((∃ d : Sm.D, St Q L X g k = some (some (.d (.sm d))) ∧ d.site = .waitS ∧
          m = sReady L (g / L.block) (d.i % 2) ∧ p = d.i / 2 % 2) ∨
        (∃ d : Sm.D, St Q L X g k = some (some (.d (.sm d))) ∧ d.site = .waitO ∧
          m = oDone L (g / L.block) ∧ p = SO.oDoneParity d.i) ∨
        (∃ (d : Loader.D) (P : Loader.Pro), St Q L X g k = some (some (.w (.loader d P))) ∧
          d.site = .wait ∧ m = kvEmpty L (g / L.block) (d.i % 3)) ∨
        (∃ (d : Mma.D) (P : Loader.Pro), St Q L X g k = some (some (.w (.mma d P))) ∧
          d.site = .kvWait ∧ m = kvReady L (g / L.block) (d.i % 3)) ∨
        (∃ (d : Mma.D) (P : Loader.Pro), St Q L X g k = some (some (.w (.mma d P))) ∧
          d.site = .pWait ∧ m = pReady L (g / L.block) ((d.i - 1) % 2) ∧
            p = (d.i - 1) / 2 % 2) ∨
        (∃ d : Epi.D, St Q L X g k = some (some (.d (.epi d))) ∧ d.site = .wait ∧
          m = oFinal L (g / L.block) ∧ p = 0)) := by
  have hg : g < L.threads := event_thread_lt hX he
  rcases wait_event_state hpre hX hf.sound hf.tracked hf.ldRng hg he ⟨_, _, _, _, _, rfl⟩ with
    ⟨d, hσ, ⟨hs, ok, hev⟩ | hs⟩ | ⟨d, P, hσ, hs, hsh⟩ | ⟨d, P, hσ, hs, hsh⟩ | ⟨d, hσ, hs, ok, hev⟩
  · simp only [Event.mk.injEq, Kind.wait.injEq] at hev
    obtain ⟨-, rfl, rfl, -, rfl, rfl⟩ := hev
    refine ⟨rfl, rfl, .inl ⟨d, hσ, hs, ?_, rfl⟩⟩
    rfl
  · obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ (by simp [ExitState])
    obtain ⟨ok, hev⟩ := Rd.waitOShape_of (ProA.sharedOk_of_pre hpre) g d _ u (fired_sm hF) hs
    simp only [Event.mk.injEq, Kind.wait.injEq] at hev
    obtain ⟨-, rfl, rfl, -, rfl, rfl⟩ := hev
    exact ⟨rfl, rfl, .inr (.inl ⟨d, hσ, hs, rfl, rfl⟩)⟩
  · have hsh' := hsh
    unfold EvW.LdShape at hsh'
    rw [hs] at hsh'
    obtain ⟨ok, hev⟩ := hsh'
    simp only [Event.mk.injEq, Kind.wait.injEq] at hev
    obtain ⟨-, rfl, -, -, rfl, rfl⟩ := hev
    exact ⟨rfl, rfl, .inr (.inr (.inl ⟨d, P, hσ, hs, rfl⟩))⟩
  · rcases hs with hs | hs
    · have hsh' := hsh
      unfold EvW.MmShape at hsh'
      rw [hs] at hsh'
      obtain ⟨ok, hev⟩ := hsh'
      simp only [Event.mk.injEq, Kind.wait.injEq] at hev
      obtain ⟨-, rfl, -, -, rfl, rfl⟩ := hev
      exact ⟨rfl, rfl, .inr (.inr (.inr (.inl ⟨d, P, hσ, hs, rfl⟩)))⟩
    · have hsh' := hsh
      unfold EvW.MmShape at hsh'
      rw [hs] at hsh'
      obtain ⟨ok, hev⟩ := hsh'
      simp only [Event.mk.injEq, Kind.wait.injEq] at hev
      obtain ⟨-, rfl, rfl, -, rfl, rfl⟩ := hev
      exact ⟨rfl, rfl, .inr (.inr (.inr (.inr (.inl ⟨d, P, hσ, hs, rfl, rfl⟩))))⟩
  · simp only [Event.mk.injEq, Kind.wait.injEq] at hev
    obtain ⟨-, rfl, rfl, -, rfl, rfl⟩ := hev
    exact ⟨rfl, rfl, .inr (.inr (.inr (.inr (.inr ⟨d, hσ, hs, rfl, rfl⟩))))⟩

/-- **Every successful poll of the kernel is an acquire poll.** -/
theorem poll_acq (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k pc : Nat} {m : Loc} {p : Nat} {acq : Bool}
    {sc : MbarScope} (he : X.get (g, k) = some ⟨pc, .wait m p true acq sc⟩) : acq = true :=
  (poll_class hpre hX hf he).1

end
end PTX.Kernels.InklingRelDecode.Proof.Hs
