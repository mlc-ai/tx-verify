-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.LkSkel
public import Kernels.InklingRelDecode.Proof.Thread.LkD
public import Kernels.InklingRelDecode.Proof.Thread.LkWStep

@[expose] public section

/-!
# Warp lockstep: the skeleton of the kernel's thread machines

`kernelSkel` is `Skel` for `threadCode`: the synchronizing states, keys and agreement of the
default partition (`Thread/LkD.lean`) and of the workers (`Thread/LkW.lean`). `lock_kernel` is
`lock_all` for it: given the agreement `kernelAgree` at the synchronizing events of lanes of a
warp, the lanes' `n`-th synchronizing states are at one key, so at one site.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {Q : Params} {L : Launch}

/-- The key of a thread's state. -/
def tKey (L : Launch) (g : Nat) : TSt → PTX.Kernels.InklingRelDecode.Proof.Lk.Key
  | .d s => PTX.Kernels.InklingRelDecode.Proof.Lk.dKey L g s
  | .w s => PTX.Kernels.InklingRelDecode.Proof.Lk.kOf
      (PTX.Kernels.InklingRelDecode.Proof.Lk.wKey L g s)

/-- The state's event is synchronizing. -/
def tSy : TSt → Prop
  | .d s => PTX.Kernels.InklingRelDecode.Proof.Lk.dSy s = true
  | .w s => PTX.Kernels.InklingRelDecode.Proof.Lk.wSy s = true

/-- **What two lanes of a warp agree on at their synchronizing events.** -/
def tAgree (L : Launch) (g h : Nat) : TSt → TSt → Event → Event → Prop
  | .d s, .d s', e, e' => PTX.Kernels.InklingRelDecode.Proof.Lk.dAgree L g h s s' e e'
  | .w s, .w s', e, e' => PTX.Kernels.InklingRelDecode.Proof.Lk.WAgree L g h s s' e e'
  | _, _, _, _ => True

theorem next_d_inv {g : Nat} {s : DComp.St} {e : Event} {t : TSt}
    (h : (threadCode L g Q).next (.d s) e = some (some t)) :
    ∃ a, DComp.next L g Q s e = some (some a) ∧ t = .d a := by
  obtain ⟨a, ha, rfl⟩ := map_map_eq_some_some h
  exact ⟨a, ha, rfl⟩

theorem next_w_inv {g : Nat} {s : WComp.WSt} {e : Event} {t : TSt}
    (h : (threadCode L g Q).next (.w s) e = some (some t)) :
    ∃ a, WComp.next L g s e = some (some a) ∧ t = .w a := by
  obtain ⟨a, ha, rfl⟩ := map_map_eq_some_some h
  exact ⟨a, ha, rfl⟩

/-- **The skeleton of the kernel's thread machines.** -/
def kernelSkel (Q : Params) (L : Launch) : Skel Q L PTX.Kernels.InklingRelDecode.Proof.Lk.Key where
  sy := tSy
  key := tKey L
  pcOf := fun k => k.1
  agree := tAgree L
  init := by
    intro g h hw
    have hw2 : g % L.block / 32 = h % L.block / 32 := hw.2
    show tKey L g (if g % L.block < 128 then .d (DComp.code L g Q).init
        else .w (WComp.code L g Q).init) =
      tKey L h (if h % L.block < 128 then .d (DComp.code L h Q).init
        else .w (WComp.code L h Q).init)
    split <;> split
    · exact PTX.Kernels.InklingRelDecode.Proof.Lk.d_init Q hw
    · exfalso; omega
    · exfalso; omega
    · exact congrArg PTX.Kernels.InklingRelDecode.Proof.Lk.kOf
        (PTX.Kernels.InklingRelDecode.Proof.Lk.w_init Q hw)
  pc_key := by
    intro g s hs
    cases s with
    | d s => exact PTX.Kernels.InklingRelDecode.Proof.Lk.d_sy_key L g hs
    | w s => exact PTX.Kernels.InklingRelDecode.Proof.Lk.w_sy_key (L := L) (g := g) hs
  silent := by
    intro g s e t hg hns hn
    cases s with
    | d s =>
      obtain ⟨a, ha, rfl⟩ := next_d_inv hn
      exact PTX.Kernels.InklingRelDecode.Proof.Lk.d_silent ha (by simpa [tSy] using hns)
    | w s =>
      obtain ⟨a, ha, rfl⟩ := next_w_inv hn
      exact congrArg PTX.Kernels.InklingRelDecode.Proof.Lk.kOf
        (PTX.Kernels.InklingRelDecode.Proof.Lk.w_silent (L := L) (g := g) ha
          (by simpa [tSy] using hns))
  step := by
    intro g h s s' e e' t t' hw hc hc' hs hs' hk ha hn hn'
    cases s with
    | d s =>
      cases s' with
      | d s' =>
        obtain ⟨a, ha1, rfl⟩ := next_d_inv hn
        obtain ⟨b, hb1, rfl⟩ := next_d_inv hn'
        exact PTX.Kernels.InklingRelDecode.Proof.Lk.d_step Q hw hs hs' hk ha ha1 hb1
      | w s' =>
        exfalso
        have hw2 : g % L.block / 32 = h % L.block / 32 := hw.2
        have h1 := hc.mp trivial
        have h2 : ¬ h % L.block < 128 := fun hh => by simpa [TSt.isD] using hc'.mpr hh
        omega
    | w s =>
      cases s' with
      | d s' =>
        exfalso
        have hw2 : g % L.block / 32 = h % L.block / 32 := hw.2
        have h1 := hc'.mp trivial
        have h2 : ¬ g % L.block < 128 := fun hh => by simpa [TSt.isD] using hc.mpr hh
        omega
      | w s' =>
        obtain ⟨a, ha1, rfl⟩ := next_w_inv hn
        obtain ⟨b, hb1, rfl⟩ := next_w_inv hn'
        exact congrArg PTX.Kernels.InklingRelDecode.Proof.Lk.kOf
          (PTX.Kernels.InklingRelDecode.Proof.Lk.w_step hw hs hs'
            (congrArg (fun k => k.1) hk) ha ha1 hb1)

/-- **The agreement premise**: at the synchronizing states of the lanes of a warp with one ordinal
(and one key, and given the lockstep up to that ordinal), the lanes agree on what steers the
branch to the next synchronizing state (`tAgree`). -/
def LaneAgree (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ n, (∀ m, m ≤ n → Lock (kernelSkel Q L) X m) → ∀ {g h a b : Nat} {s s' : TSt} {e e' : Event},
    SameWarp L g h → (X.tr g)[a]? = some e → (X.tr h)[b]? = some e' →
    St Q L X g a = some (some s) → St Q L X h b = some (some s') →
    (kernelSkel Q L).sy s → (kernelSkel Q L).sy s' → syN (kernelSkel Q L) X g a = n →
    syN (kernelSkel Q L) X h b = n → (kernelSkel Q L).key g s = (kernelSkel Q L).key h s' →
    (kernelSkel Q L).agree g h s s' e e'

/-- **The lanes of a warp are at one key at every synchronizing ordinal.** -/
theorem lock_kernel (ht : Frame.Tracked (code L Q) X) (hA : LaneAgree Q L X) :
    ∀ n, Lock (kernelSkel Q L) X n := lock_all (kernelSkel Q L) ht hA

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
