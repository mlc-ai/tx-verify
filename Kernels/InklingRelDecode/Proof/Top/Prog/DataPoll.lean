-- SPDX-License-Identifier: Apache-2.0
module

import Kernels.InklingRelDecode.Proof.Top.Prog.WaitStep
public import Kernels.InklingRelDecode.Proof.Top.Prog.Classes
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues
import Kernels.InklingRelDecode.Proof.Protocol.S.Credit
import Kernels.InklingRelDecode.Proof.Protocol.ODone.Credit

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX Protocol Scalar

private theorem data_step {Q L m X g} (hp : Pre Q L m)
    (followed : ∀ Y, Consistent L kernel Assumptions.all m Y → Follow Q L Y)
    (base : Object) (kind : (∃ s,base=.score s) ∨ base=.done)
    (credit : (∀ Y, Consistent L kernel Assumptions.all m Y → MbarRows Q L Y) →
      Mbar.InitRows L X → RoleBytes L X → ¬Race L X →
      (∀ l, ∀ r ∈ X.objects l, r.fault=none) → ∀ n, Credit L m X (base.atRound n))
    (hs : SafeGoal kernel Assumptions.all L m) (hm : Maximal L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hg : Frame.Pending L X g)
    (hr : Step.Released L X g) (failed : FailsAt L m X g base.pc) :
    Sched.Steps (schedule Q L) m X (.thread g) := by
  obtain ⟨l,q,sc,hn⟩ := failed
  have hu := Sched.safe_noUb (hs.2 X hm.1)
  have rows := fun Y (hY : Consistent L kernel Assumptions.all m Y) =>
    mbarRows_of hp hY (followed Y hY)
  obtain ⟨Y,hY,pre,get⟩ := id hn
  have loc := wait_pc (rows Y hY) hg.1 base get
  simp only [MbarRow.roundAt,pre] at loc
  subst l
  let r := pollRound base.pc (X.tr g)
  let o := base.atRound r
  have pc : o.pc=base.pc := by cases base <;> rfl
  have cm : (∃ s,o=.score s) ∨ o=.done := by
    rcases kind with ⟨s,rfl⟩|rfl
    · exact .inl ⟨_,rfl⟩
    · exact .inr rfl
  have site : base.pc=1257 ∨ base.pc=2239 := by rcases kind with ⟨s,rfl⟩|rfl <;> simp [Object.pc]
  apply Export.softmax_wait_step hp hm hu hf hg hr site hn
  have free : ∀ l, ∀ r ∈ X.objects l, r.fault=none := by
    intro l rec mem
    cases eq : rec.fault with
    | none => rfl
    | some f =>
      have bad : TmaUnsafe L m X := .inl ⟨_,rec,mem,by simp [eq]⟩
      exact (hs.2 X hm.1 (by simp [Unsafe,bad])).elim
  have safe : ¬Race L X := fun race => hs.2 X hm.1 (by simp [Unsafe,race])
  have init := initRows_of hp hm.1 hf
  have words : RoleBytes L X := fun he => Shared.role_bytes hp hm.1 he
  exact notify_blocker (sc := sc) hp hm.1 hf hu rows init words o cm
    (credit rows init words safe free r) (fun rec mem => free _ rec mem) (by rw [pc]; exact hn)

theorem Prog.score {Q L m X g} (hp : Pre Q L m)
    (followed : ∀ Y, Consistent L kernel Assumptions.all m Y → Follow Q L Y)
    (hs : SafeGoal kernel Assumptions.all L m)
    (hm : Maximal L kernel Assumptions.all m X) (hf : Follow Q L X) (hg : Frame.Pending L X g)
    (hr : Step.Released L X g) (failed : FailsAt L m X g 1257) :
    Sched.Steps (schedule Q L) m X (.thread g) :=
  data_step hp followed (.score 0) (.inl ⟨_,rfl⟩)
    (fun rows init words safe free n =>
      S.score_credit hp hm.1 followed rows init words safe free (MbarRow.slot2 n))
    hs hm hf hg hr failed

theorem Prog.done {Q L m X g} (hp : Pre Q L m)
    (followed : ∀ Y, Consistent L kernel Assumptions.all m Y → Follow Q L Y)
    (hs : SafeGoal kernel Assumptions.all L m)
    (hm : Maximal L kernel Assumptions.all m X) (hf : Follow Q L X) (hg : Frame.Pending L X g)
    (hr : Step.Released L X g) (failed : FailsAt L m X g 2239) :
    Sched.Steps (schedule Q L) m X (.thread g) :=
  data_step hp followed .done (.inr rfl)
    (fun rows init words safe free _ =>
      ODone.done_credit hp hm.1 followed rows init words safe free)
    hs hm hf hg hr failed

end PTX.Kernels.InklingRelDecode.Proof.Top
