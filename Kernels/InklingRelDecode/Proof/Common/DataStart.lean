-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.ReferenceInduction
public import Kernels.InklingRelDecode.Proof.Common.Table
public import Kernels.InklingRelDecode.Proof.Startup.BarrierLedger

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow

structure LaunchCounts (n : Cls → Nat) (bars : Nat) : Prop where
  visit : ∀ p, 27≤p → n (.atPc p)=0
  arrival : ∀ l, n (.arrivalTo l)=0
  copy : ∀ l, n (.issueTo l)=0
  poll : ∀ p, 27≤p → n (.poll p)=0
  first : n (.bar 0)=bars
  second : n (.bar 1)=0

theorem launch_counts_init {L g} :
    LaunchCounts (fun _ => 0) (Startup.barriers (Startup.init L g).site) := by
  refine ⟨by simp,by simp,by simp,by simp,?_,rfl⟩
  unfold Startup.init
  split <;> rfl

theorem launch_counts_step {L g d dn n ev} (prev : LaunchCounts n (Startup.barriers d.site))
    (shape : Startup.Ev L g d ev) (move : Startup.succ L g d ev=some (some dn)) :
    LaunchCounts (Code.bump cls n ev) (Startup.barriers dn.site) := by
  obtain ⟨⟨pc,arr,copy,one⟩,phase⟩ := Startup.startup_ledger shape move
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro p h
    simp [Code.bump,cls,prev.visit p h,show ev.pc≠p by omega]
  · intro l
    simp [Code.bump,cls,prev.arrival,arr]
  · intro l
    simp [Code.bump,cls,prev.copy,copy]
  · intro p h
    have off : okPollAt p ev=false := by
      have ne : ev.pc≠p := by omega
      cases ev with | mk pc kd =>
        cases kd <;> try rfl
        rename_i yes _ _
        cases yes <;> simp_all [okPollAt]
    simp [Code.bump,cls,prev.poll p h,off]
  · change n (.bar 0)+(if Execution.isBarId 0 ev then 1 else 0)=_
    rw [prev.first,phase]
    cases Execution.isBarId 0 ev <;> rfl
  · change n (.bar 1)+(if Execution.isBarId 1 ev then 1 else 0)=_
    simp [prev.second,one]

theorem pro_history_start {Q L g n} (start : LaunchCounts n 2) :
    Prologue.History Q L g {} (proCounts L g n) := by
  refine ⟨⟨?_,?_⟩,Prologue.known_init ..,?_,?_,?_,?_,?_⟩
  · intro p lo _; exact (start.visit p (by omega)).le.trans (by decide)
  · intro p lo _ _; exact start.visit p (by omega)
  · intro _ h; cases h
  · intro _ h; cases h
  · intro b; exact (start.arrival _).le.trans (Nat.zero_le _)
  · intro b; exact (start.copy _).le.trans (Nat.zero_le _)
  · exact fun _ => ⟨start.first,start.second⟩

theorem pro_count_bump {L g n ev} :
    proCounts L g (Code.bump cls n ev) = (proCounts L g n).bump L g ev := by
  have bump (c) : Code.bump cls n ev c=n c+(cls c ev).toNat := by
    unfold Code.bump
    cases cls c ev <;> rfl
  simp only [proCounts,Prologue.Counts.bump,bump]
  rfl

end PTX.Kernels.InklingRelDecode.Proof
