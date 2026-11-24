-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk2Count
public import Kernels.InklingRelDecode.Proof.Interface.LedgerInv
public import Kernels.InklingRelDecode.Proof.Interface.ShapeTrace
public import Kernels.InklingRelDecode.Proof.Interface.FootRoleAll
public import Kernels.InklingRelDecode.Proof.Interface.FootRoleRead
public import Kernels.InklingRelDecode.Proof.Thread.FootRole

@[expose] public section

/-!
# Warp lockstep: the worker dispatch

At the load of its role byte (`Worker.Site.ldRole`) a worker thread leaves for the role the byte
names. The lanes of a warp read the same role: in the first round (one barrier-1 event before the
load) the byte names the warp's role (`RoleReads`: the loader for warp 6, the MMA role for warp
7, the idle role for warps 4 and 5), so the index is a function of the warp; in a later round the
byte names the exit (`RoleReads`). Two lanes of a warp
at their `n`-th synchronizing states are in the same round, because they have made the same
number of barrier-1 events (`b1N_lock`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Lk (roleIdx)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem dispatch_cases (P : Loader.Pro) (bs : List (Option Byte)) :
    (Ledger.roleIdx bs = none ∧ Worker.dispatch P bs = none) ∨
      ∃ x : BitVec 64, Ledger.roleIdx bs = some x.toNat ∧
        Worker.dispatch P bs =
          some (some ⟨(Worker.roleSite (truncBits 32 x).toNat).getD .bad0, P⟩) := by
  unfold Ledger.roleIdx Worker.dispatch
  cases hr : rebuild 3 bs with
  | error f => left; simp
  | ok v =>
    cases he : extendLoaded (MemExt.zero 32) 8 v with
    | error f => left; simp [he]
    | ok w =>
      cases w with
      | bits wd x =>
        by_cases hw : wd = 32
        · subst hw
          right
          exact ⟨x, by simp [he], by simp [he]⟩
        · left
          simp [he, hw]
      | _ => left; simp [he]

/-- **A role byte of one value gives one dispatch**: the sites are those of the index. -/
theorem dispatch_site_eq {P P' : Loader.Pro} {bs bs' : List (Option Byte)}
    (h : Ledger.roleIdx bs = Ledger.roleIdx bs') :
    (Worker.dispatch P bs).map (Option.map Worker.D.site) =
      (Worker.dispatch P' bs').map (Option.map Worker.D.site) := by
  rcases dispatch_cases P bs with ⟨h1, h2⟩ | ⟨x, h1, h2⟩ <;>
    rcases dispatch_cases P' bs' with ⟨h3, h4⟩ | ⟨x', h3, h4⟩
  · rw [h2, h4]
  · rw [h1, h3] at h; cases h
  · rw [h1, h3] at h; cases h
  · rw [h1, h3] at h
    have hx : x = x' := BitVec.eq_of_toNat_eq (Option.some.inj h)
    subst hx
    rw [h2, h4]
    rfl

/-- **A worker at the load of its role byte has made one or four barrier-1 events.** -/
theorem ldRole_b1N (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (hRR : RoleReads L X) {g a : Nat}
    {P : Loader.Pro} (ha : a ≤ (X.tr g).length)
    (hσ : St Q L X g a = some (some (.w (.worker ⟨.ldRole, P⟩)))) :
    b1N X g a = 1 ∨ b1N X g a = 4 := by
  obtain ⟨-, t, -, h2, -, -, -, h6⟩ := phase_inv hpre hX hS hRR a _ ha hσ
  rw [h2]
  simp only [tPh, Ledger.wPh]
  omega

/-- **Two lanes of a warp at their `n`-th synchronizing states, both at the load of the role
byte, take the same role.** -/
theorem ldRole_agree (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hRR : RoleReads L X) {n : Nat}
    (hL : ∀ m, m ≤ n → Lock (kernelSkel Q L) X m) {g h a b : Nat} {P P' : Loader.Pro}
    {e e' : Event} (hw : SameWarp L g h) (he : (X.tr g)[a]? = some e)
    (he' : (X.tr h)[b]? = some e')
    (hsa : St Q L X g a = some (some (.w (.worker ⟨.ldRole, P⟩))))
    (hsb : St Q L X h b = some (some (.w (.worker ⟨.ldRole, P'⟩))))
    (hna : syN (kernelSkel Q L) X g a = n) (hnb : syN (kernelSkel Q L) X h b = n) :
    roleIdx L g ⟨.ldRole, P⟩ e = roleIdx L h ⟨.ldRole, P'⟩ e' := by
  have hg : g < L.threads := hw.1.1
  have hh : h < L.threads := hw.1.2.1
  have ha : a ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  have hb : b ≤ (X.tr h).length := (List.getElem?_eq_some_iff.mp he').1.le
  have hsy : (kernelSkel Q L).sy (.w (.worker ⟨.ldRole, P⟩)) := by
    show PTX.Kernels.InklingRelDecode.Proof.Lk.wSy (.worker ⟨.ldRole, P⟩) = true
    simp [PTX.Kernels.InklingRelDecode.Proof.Lk.wSy, PTX.Kernels.InklingRelDecode.Proof.Lk.isLdRole]
  have hsy' : (kernelSkel Q L).sy (.w (.worker ⟨.ldRole, P'⟩)) := by
    show PTX.Kernels.InklingRelDecode.Proof.Lk.wSy (.worker ⟨.ldRole, P'⟩) = true
    simp [PTX.Kernels.InklingRelDecode.Proof.Lk.wSy, PTX.Kernels.InklingRelDecode.Proof.Lk.isLdRole]
  have hcnt := b1N_lock hpre hX hf.sound hf.tracked n (fun m hm => hL m (by omega)) hw ha hb hsa
    hsb hsy hsy' hna hnb
  have hcnt' : b1N X g a = b1N X h b := hcnt
  -- the events are reads of the role byte
  have hshape : ∀ {g' k' : Nat} {P0 : Loader.Pro} {e0 : Event}, g' < L.threads →
      (X.tr g')[k']? = some e0 → St Q L X g' k' = some (some (.w (.worker ⟨.ldRole, P0⟩))) →
      ∃ ac bs, e0 = ⟨Worker.Site.ldRole.pc, .rd ac bs⟩ := by
    intro g' k' P0 e0 hg' he0 hσ0
    obtain ⟨u, hF⟩ := fired_cont hX hf hg' (show X.get (g', k') = some e0 from he0) hσ0
      (by simp [ExitState])
    obtain ⟨t', hgd, hfire⟩ := hF
    have hF' : (WComp.code L g' Q).toMachine.Fired (some (.worker ⟨.ldRole, P0⟩)) e0 (some u) :=
      ⟨t', ⟨hgd.1, hgd.2.2⟩, hfire⟩
    have h256 : g' % L.block < 256 := by
      have := hpre.block
      rw [this]
      exact Nat.mod_lt _ (by omega)
    obtain ⟨ac, bs, he2, -, -⟩ := Worker.shape_ldRole hpre (w := ⟨.ldRole, P0⟩) h256 rfl hF'
    exact ⟨ac, bs, he2⟩
  obtain ⟨ac, bs, rfl⟩ := hshape hg he hsa
  obtain ⟨ac', bs', rfl⟩ := hshape hh he' hsb
  have h128 : ∀ {g' k' : Nat} {s : TSt}, k' ≤ (X.tr g').length →
      St Q L X g' k' = some (some s) → ¬ s.isD → 128 ≤ g' % L.block := by
    intro g' k' s hk hσ hnd
    have := (cls_inv k' s hk hσ).not.mp hnd
    omega
  have hg128 := h128 ha hsa (fun h => h)
  have hh128 := h128 hb hsb (fun h => h)
  have hget : X.get (g, a) = some ⟨Worker.Site.ldRole.pc, .rd ac bs⟩ := he
  have hget' : X.get (h, b) = some ⟨Worker.Site.ldRole.pc, .rd ac' bs'⟩ := he'
  have hwarp : Worker.warpOf L g = Worker.warpOf L h := hw.2
  have hids : Ledger.roleIdx bs = Ledger.roleIdx bs' := by
    rcases ldRole_b1N hpre hX hf.sound hRR ha hsa with h1 | h4
    · have h1' : b1N X h b = 1 := by omega
      rw [(hRR g a ac bs hg hg128 hget).2.2 h1, (hRR h b ac' bs' hh hh128 hget').2.2 h1']
      unfold Worker.warpOf at hwarp
      rw [hwarp]
    · have h4' : 4 ≤ b1N X h b := by omega
      rw [(hRR g a ac bs hg hg128 hget).2.1 (by omega),
        (hRR h b ac' bs' hh hh128 hget').2.1 h4']
  have := dispatch_site_eq (P := P) (P' := P') hids
  simp only [roleIdx, Worker.next]
  exact this

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
