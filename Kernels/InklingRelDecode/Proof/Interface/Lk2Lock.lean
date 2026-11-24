-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk2Field
public import Kernels.InklingRelDecode.Proof.Interface.LkMachine
public import Kernels.InklingRelDecode.Proof.Thread.Lk2Ex

@[expose] public section

/-!
# Warp lockstep: the lanes of a warp agree on the loop counters of the workers

`exT` is the pair of loop counters a thread's state has at its next synchronizing state
(`Thread/Lk2Ex.lean`). Given the lockstep of the keys up to the ordinal `n`, the lanes of a warp at
their `n`-th synchronizing states have the same counters (`counters_lock`): the counters after a
synchronizing step are a function of the state's counters and site (`field_lock`), and the one
exception, the loop entry `bar0` of the loader and of the MMA warp, where the counters come from
words the prologue stored, is the premise `Bar0Counters` (it follows from `NumPreRead` and
`NumWordRead`: `Interface/Lk2Bar0.lean`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Lk (wSy syPc exL exM exW stW stL stMm exSilent_W exStep_W
  wRole role_eq)

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The counters of a thread's state at its next synchronizing state. -/
def exT : TSt → Nat × Nat
  | .d _ => (0, 0)
  | .w s => exW s

/-- The counters after a step of a synchronizing state. -/
def stT : TSt → Nat × Nat
  | .d _ => (0, 0)
  | .w s => stW s

theorem exT_silent {g : Nat} {s : TSt} {e : Event} {t : TSt} (_hg : g < L.threads)
    (hs : ¬ (kernelSkel Q L).sy s) (hn : (threadCode L g Q).next s e = some (some t)) :
    exT t = exT s := by
  cases s with
  | d s =>
    obtain ⟨a, -, rfl⟩ := next_d_inv hn
    rfl
  | w s =>
    obtain ⟨a, ha, rfl⟩ := next_w_inv hn
    have hs' : wSy s = false := by
      have : ¬ wSy s = true := hs
      simpa using this
    exact exSilent_W ha hs'

theorem exT_step {g : Nat} {s : TSt} {e : Event} {t : TSt} (_hg : g < L.threads)
    (hs : (kernelSkel Q L).sy s) (hn : (threadCode L g Q).next s e = some (some t)) :
    exT t = stT s := by
  cases s with
  | d s =>
    obtain ⟨a, -, rfl⟩ := next_d_inv hn
    rfl
  | w s =>
    obtain ⟨a, ha, rfl⟩ := next_w_inv hn
    exact exStep_W ha hs

theorem exT_init (g : Nat) : exT (threadCode L g Q).init = (0, 0) := by
  show exT (if g % L.block < 128 then TSt.d (DComp.code L g Q).init
    else .w (WComp.code L g Q).init) = (0, 0)
  split <;> rfl

theorem loader_site_eq {a b : Loader.Site} (ha : syPc a.pc = true) (hb : syPc b.pc = true)
    (h : a.pc = b.pc) : a = b := by
  cases a <;> cases b <;> first | rfl | (exfalso; revert ha hb h; decide +kernel)

/-- **No MMA state of a thread is at the barrier of a lane that skips a half** (`qkSkip`,
`pvSkip`): every broadcast of warp 7 receives 7 (`Ring.MmaBcast`, `Protocol/MmBcast.lean`). -/
def NoSkip (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g a : Nat} {d : Mma.D} {P : Loader.Pro}, g < L.threads →
    St Q L X g a = some (some (.w (.mma d P))) → d.site.isSkip = false

/-- **The agreement of the lanes at the loop entry**: the counters the loader and the MMA warp
carry at `bar0` are the same in two lanes of a warp. -/
structure Bar0Counters (Q : Params) (L : Launch) (X : Execution) : Prop where
  loader : ∀ {g h a b : Nat} {d d' : Loader.D} {P P' : Loader.Pro}, SameWarp L g h →
    St Q L X g a = some (some (.w (.loader d P))) →
    St Q L X h b = some (some (.w (.loader d' P'))) → d.site = .bar0 → d'.site = .bar0 →
    d.i = d'.i ∧ d.n = d'.n
  mma : ∀ {g h a b : Nat} {d d' : Mma.D} {P P' : Loader.Pro}, SameWarp L g h →
    St Q L X g a = some (some (.w (.mma d P))) →
    St Q L X h b = some (some (.w (.mma d' P'))) → d.site = .bar0 → d'.site = .bar0 →
    d.i = d'.i ∧ d.n = d'.n

theorem stT_loader (hb : Bar0Counters Q L X) {g h a b : Nat} {d d' : Loader.D}
    {P P' : Loader.Pro} (hw : SameWarp L g h) (hsa : St Q L X g a = some (some (.w (.loader d P))))
    (hsb : St Q L X h b = some (some (.w (.loader d' P'))))
    (hs : wSy (.loader d P) = true) (hs' : wSy (.loader d' P') = true)
    (hpc : d.site.pc = d'.site.pc) (hx : exL d = exL d') : stL d = stL d' := by
  have hs0 := PTX.Kernels.InklingRelDecode.Proof.Lk.sy_loader hs
  have hd := loader_site_eq hs0 (PTX.Kernels.InklingRelDecode.Proof.Lk.sy_loader hs') hpc
  by_cases hb0 : d.site = .bar0
  · have hb0' : d'.site = .bar0 := hd ▸ hb0
    obtain ⟨h1, h2⟩ := hb.loader hw hsa hsb hb0 hb0'
    simp only [stL, hb0, hb0', h1, h2]
  · obtain ⟨s0, pro, i, n, p0, p1, ln⟩ := d
    obtain ⟨s0', pro', i', n', p0', p1', ln'⟩ := d'
    simp only at hd hb0 hx hs0 ⊢
    subst hd
    cases s0 <;> first
      | (exfalso; revert hs0; decide +kernel)
      | exact absurd rfl hb0
      | (simp only [exL, stL, Prod.mk.injEq] at hx ⊢; omega)
      | simp only [stL]

theorem stT_mma (hb : Bar0Counters Q L X) (hns : NoSkip Q L X) {g h a b : Nat} {d d' : Mma.D}
    {P P' : Loader.Pro} (hw : SameWarp L g h) (hsa : St Q L X g a = some (some (.w (.mma d P))))
    (hsb : St Q L X h b = some (some (.w (.mma d' P'))))
    (hs : wSy (.mma d P) = true) (hs' : wSy (.mma d' P') = true)
    (hpc : d.site.pc = d'.site.pc) (hx : exM d = exM d') : stMm d = stMm d' := by
  have hs0 := PTX.Kernels.InklingRelDecode.Proof.Lk.sy_mma hs
  have hd := Mma.Site.eq_of_pc (hns hw.1.1 hsa) (hns hw.1.2.1 hsb) hpc
  by_cases hb0 : d.site = .bar0
  · have hb0' : d'.site = .bar0 := hd ▸ hb0
    obtain ⟨h1, h2⟩ := hb.mma hw hsa hsb hb0 hb0'
    simp only [stMm, hb0, hb0', h1, h2]
  · obtain ⟨s0, i, n, tm, pro⟩ := d
    obtain ⟨s0', i', n', tm', pro'⟩ := d'
    simp only at hd hb0 hx hs0 ⊢
    subst hd
    cases s0 <;> first
      | exact absurd rfl hb0
      | (exfalso; revert hs0; decide +kernel)
      | (exfalso; clear hx hsa hsb hs hs' hpc hb0; rename_i j; revert hs0; revert j; decide +kernel)
      | (simp only [exM, stMm, Prod.mk.injEq] at hx ⊢; omega)
      | (simp only [exM, Prod.mk.injEq] at hx
         obtain ⟨h1, h2⟩ := hx
         subst h1 h2
         simp only [stMm, Mma.afterQk, Mma.iterNext]
         split <;> rfl)
      | simp only [stMm]

/-- **Two lanes of a warp at one synchronizing site with the same counters have the same
counters after the step.** -/
theorem counters_pair (hb : Bar0Counters Q L X) (hns : NoSkip Q L X)
    {g h a b : Nat} {sa sb t t' : TSt} {e e' : Event} (hw : SameWarp L g h)
    (ha : a ≤ (X.tr g).length) (hbb : b ≤ (X.tr h).length)
    (hsa : St Q L X g a = some (some sa)) (hsb : St Q L X h b = some (some sb))
    (hn : (threadCode L g Q).next sa e = some (some t))
    (hn' : (threadCode L h Q).next sb e' = some (some t'))
    (hsya : (kernelSkel Q L).sy sa) (hsyb : (kernelSkel Q L).sy sb)
    (hk : (kernelSkel Q L).key g sa = (kernelSkel Q L).key h sb) (hx : exT sa = exT sb) :
    stT sa = stT sb := by
  have hca := cls_inv a sa ha hsa
  have hcb := cls_inv b sb hbb hsb
  have hw2 : g % L.block / 32 = h % L.block / 32 := hw.2
  have hpc : TSt.pc sa = TSt.pc sb := by
    rw [← (kernelSkel Q L).pc_key (g := g) hsya, ← (kernelSkel Q L).pc_key (g := h) hsyb, hk]
  cases sa with
  | d s => cases sb with
    | d s' => rfl
    | w s' =>
      exfalso
      have h1 := hca.mp trivial
      have h2 : ¬ h % L.block < 128 := fun hh => by simpa [TSt.isD] using hcb.mpr hh
      omega
  | w s => cases sb with
    | d s' =>
      exfalso
      have h1 := hcb.mp trivial
      have h2 : ¬ g % L.block < 128 := fun hh => by simpa [TSt.isD] using hca.mpr hh
      omega
    | w s' =>
      obtain ⟨u, hu, -⟩ := next_w_inv hn
      obtain ⟨u', hu', -⟩ := next_w_inv hn'
      have hs : wSy s = true := hsya
      have hs' : wSy s' = true := hsyb
      have hpc' : WComp.pc s = WComp.pc s' := hpc
      have hr := role_eq hs hs' hu hu' hpc'
      cases s with
      | loader d P => cases s' with
        | loader d' P' => exact stT_loader hb hw hsa hsb hs hs' hpc hx
        | _ => simp [wRole] at hr
      | mma d P => cases s' with
        | mma d' P' => exact stT_mma hb hns hw hsa hsb hs hs' hpc hx
        | _ => simp [wRole] at hr
      | worker w => cases s' <;> first | rfl | (simp [wRole] at hr)
      | idle w => cases s' <;> first | rfl | (simp [wRole] at hr)
      | exit w => cases s' <;> first | rfl | (simp [wRole] at hr)

/-- **The lanes of a warp at their `n`-th synchronizing states have the same loop counters**,
given the lockstep of the keys up to `n` and the agreement at the loop entry. -/
theorem counters_lock (ht : Frame.Tracked (code L Q) X) (hb : Bar0Counters Q L X)
    (hns : NoSkip Q L X) :
    ∀ n, (∀ m, m ≤ n → Lock (kernelSkel Q L) X m) → ∀ {g h a b : Nat} {s s' : TSt},
      SameWarp L g h → a ≤ (X.tr g).length → b ≤ (X.tr h).length →
      St Q L X g a = some (some s) → St Q L X h b = some (some s') → (kernelSkel Q L).sy s →
      (kernelSkel Q L).sy s' → syN (kernelSkel Q L) X g a = n → syN (kernelSkel Q L) X h b = n →
      exT s = exT s' :=
  field_lock (kernelSkel Q L) ht exT stT (fun hg hs hn => exT_silent hg hs hn)
    (fun hg hs hn => exT_step hg hs hn) (fun _ => by rw [exT_init, exT_init])
    (fun hw ha hbb hsa hsb _ _ hn hn' hsya hsyb hk hx =>
      counters_pair hb hns hw ha hbb hsa hsb hn hn' hsya hsyb hk hx)

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
