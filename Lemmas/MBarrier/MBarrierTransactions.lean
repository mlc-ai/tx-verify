-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.MBarrier.MBarrierRound

@[expose] public section

/-! Transaction conservation of actual fault-aware mbarrier histories. Expected
bytes and completion notifications are counted only when their operation succeeds.
The counter is signed: a completion may precede the corresponding expectation.
No particular kernel, phase count, transaction size or notification source is assumed. -/
namespace PTX.MBarrier

/-- Successfully expected transaction bytes of one actual object operation. -/
def Record.expectedTxBytes (r : Record ι) : Nat :=
  match r.action, r.fault with
  | .arrive _ bytes, none => bytes
  | _, _ => 0

/-- Successfully completed transaction bytes of one actual object operation. -/
def Record.completedTxBytes (r : Record ι) : Nat :=
  match r.action, r.fault with
  | .completeTx bytes, none => bytes
  | _, _ => 0

def expectedTxBytes : List (Record ι) → Nat
  | [] => 0
  | r::rest => r.expectedTxBytes+expectedTxBytes rest

def completedTxBytes : List (Record ι) → Nat
  | [] => 0
  | r::rest => r.completedTxBytes+completedTxBytes rest

/-- The cumulative signed transaction effect, including explicit fault records. -/
def transactionSum : List (Record ι) → Int
  | [] => 0
  | r::rest => r.txDelta+transactionSum rest

theorem Record.txDelta_eq_bytes (r : Record ι) :
    r.txDelta=(r.expectedTxBytes:Int)-r.completedTxBytes := by
  cases ha : r.action <;> cases hf : r.fault <;>
    simp [Record.txDelta,Action.txDelta,Record.expectedTxBytes,Record.completedTxBytes,ha,hf]

theorem transactionSum_eq_bytes (log : List (Record ι)) :
    transactionSum log=(expectedTxBytes log:Int)-completedTxBytes log := by
  induction log with
  | nil => rfl
  | cons r rest ih =>
    simp only [transactionSum,expectedTxBytes,completedTxBytes,Int.natCast_add,
      Record.txDelta_eq_bytes,ih]
    omega

/-- Before initialization the balance is zero; after initialization it is exactly
this object's signed transaction counter. Faults keep the same object state. -/
def TransactionAccounted (s : Option State) (balance : Int) : Prop :=
  (s=none → balance=0) ∧ ∀ st, s=some st → st.tx=balance

private theorem perform_some_tx_balance {s : State} {a : Action} {rep : Reply}
    (hp : perform (some s) a=.ok rep) (hni : a ≠ .inval) :
    ∃ st, rep.state=some st ∧ st.tx=s.tx+a.txDelta := by
  obtain ⟨st,hs,hcase⟩ := perform_some_tx hp hni
  refine ⟨st,hs,?_⟩
  rcases hcase with ⟨_,h⟩ | ⟨_,hz,hsum⟩
  · exact h
  · omega

/-- Conservation for one checked operation, including initialization and faults.
Reinitialization needs no extra exclusion: its failed operation contributes zero. -/
theorem transaction_accounted_step {s : Option State} {balance : Int} {r : Record ι}
    (hb : TransactionAccounted s balance) (hr : RecordOk s r) (hni : r.action ≠ .inval) :
    TransactionAccounted r.reply.state (balance+r.txDelta) := by
  unfold RecordOk at hr
  split at hr
  · rename_i rep hp
    obtain ⟨hrep,hfault⟩ := hr
    have hd : r.txDelta=r.action.txDelta := by simp [Record.txDelta,hfault]
    rw [hrep,hd]
    cases s with
    | none =>
      have hzero := hb.1 rfl
      cases ha : r.action <;> rw [ha] at hp <;>
        simp [perform,bind,Except.bind,pure,Except.pure,throw,throwThe,
          MonadExceptOf.throw] at hp
      split_ifs at hp
      simp at hp
      subst hp
      refine ⟨by simp,fun st hst => ?_⟩
      cases hst
      simp [Action.txDelta,hzero]
    | some before =>
      have hbalance := hb.2 before rfl
      obtain ⟨after,hafter,htx⟩ := perform_some_tx_balance hp hni
      rw [hafter]
      refine ⟨by simp,fun st hst => ?_⟩
      cases hst
      omega
  · obtain ⟨hrep,hfault⟩ := hr
    have hd : r.txDelta=0 := by simp [Record.txDelta,hfault]
    simpa only [hrep,hd,add_zero] using hb

/-- Conservation through any actual checked history, starting at any state with
an already established balance. The signed sum counts only successful updates. -/
theorem transaction_accounted_history {s t : Option State} {log : List (Record ι)}
    {balance : Int} (hh : RecordedHistory s log t) (hni : NoInval log)
    (hb : TransactionAccounted s balance) :
    TransactionAccounted t (balance+transactionSum log) := by
  induction hh generalizing balance with
  | nil => simpa only [transactionSum,add_zero] using hb
  | @cons s r rest t hr _ ih =>
    simpa only [transactionSum,←add_assoc] using
      ih (fun q hq => hni q (List.mem_cons_of_mem _ hq))
        (transaction_accounted_step hb hr (hni r List.mem_cons_self))

/-- The state before any position is the cumulative signed expected/completed
balance of that actual history prefix, including its explicit fault records. -/
theorem CheckedLog.transaction_accounted {log : List (Record ι)} (h : CheckedLog log)
    (hni : NoInval log) {j : Nat} (hj : j≤log.length) :
    TransactionAccounted (stateBefore log j) (transactionSum (log.take j)) := by
  have hb : TransactionAccounted none 0 := ⟨fun _ => rfl,fun _ h => by cases h⟩
  simpa only [zero_add] using
    transaction_accounted_history (h.prefix hj) (fun q hq => hni q (List.mem_of_mem_take hq)) hb

theorem CheckedLog.tx_balance {log : List (Record ι)} (h : CheckedLog log) (hni : NoInval log)
    {j : Nat} {s : State} (hj : j≤log.length) (hs : stateBefore log j=some s) :
    s.tx=(expectedTxBytes (log.take j):Int)-completedTxBytes (log.take j) := by
  have hh := (h.transaction_accounted hni hj).2 s hs
  rwa [transactionSum_eq_bytes] at hh

/-- At a zero counter the cumulative successful byte amounts agree. This is a
necessary ledger fact, not a claim that each particular copy has completed. -/
theorem CheckedLog.tx_bytes_eq_of_zero {log : List (Record ι)} (h : CheckedLog log)
    (hni : NoInval log)
    {j : Nat} {s : State} (hj : j≤log.length) (hs : stateBefore log j=some s)
    (hz : s.tx=0) : expectedTxBytes (log.take j)=completedTxBytes (log.take j) := by
  have hb := h.tx_balance hni hj hs
  omega

/-- Any real phase advance leaves a zero transaction counter, including advances
triggered by the final arrival rather than by a transaction notification. -/
theorem RecordOk.phase_advance_tx_zero {before after : State} {r : Record ι}
    (hr : RecordOk (some before) r) (hs : r.reply.state=some after)
    (hphase : before.phase<after.phase) : after.tx=0 := by
  unfold RecordOk at hr
  split at hr
  · rename_i rep hp
    rw [hr.1] at hs
    have hni : r.action ≠ .inval := by
      intro hinv
      rw [hinv] at hp
      cases hp
      cases hs
    obtain ⟨st,hst,hcase⟩ := perform_some_tx hp hni
    rw [hst] at hs
    cases hs
    rcases hcase with ⟨hphase',_⟩ | ⟨_,hz,_⟩
    · omega
    · exact hz
  · rw [hr.1] at hs
    cases hs
    omega

/-- The prefix through a real phase advance has completed exactly its cumulative
successful expected bytes. Faulting operations never contribute to either sum. -/
theorem CheckedLog.phase_advance_transaction_bytes {log : List (Record ι)}
    (h : CheckedLog log) (hni : NoInval log) {j : Nat} {r : Record ι} {before after : State}
    (hj : log[j]?=some r) (hbefore : stateBefore log j=some before)
    (hafter : stateBefore log (j+1)=some after) (hphase : before.phase<after.phase) :
    expectedTxBytes (log.take (j+1))=completedTxBytes (log.take (j+1)) := by
  have hok := h.at hj
  rw [hbefore] at hok
  have ha := hafter
  rw [stateBefore_succ hj] at ha
  have hz := RecordOk.phase_advance_tx_zero hok ha hphase
  have hlt := (List.getElem?_eq_some_iff.mp hj).1
  exact h.tx_bytes_eq_of_zero hni (by omega) hafter hz

/-- Number of successful completion notifications in an object history prefix. -/
def completedTxCount (log : List (Record ι)) : Nat :=
  log.countP fun r => match r.action,r.fault with | .completeTx _,none => true | _,_ => false

/-- Uniformity is a premise about actual notification byte operands, supplied by
instruction/source provenance. The object rules do not choose a transaction size. -/
def UniformCompletedTx (log : List (Record ι)) (unit : Nat) : Prop :=
  ∀ r ∈ log, r.fault=none → ∀ bytes, r.action=.completeTx bytes → bytes=unit

theorem completedTxBytes_eq_unit_mul_count {log : List (Record ι)} {unit : Nat}
    (hu : UniformCompletedTx log unit) :
    completedTxBytes log=unit*completedTxCount log := by
  induction log with
  | nil => simp [completedTxBytes,completedTxCount]
  | cons r rest ih =>
    have hrest : UniformCompletedTx rest unit :=
      fun q hq => hu q (List.mem_cons_of_mem r hq)
    have hi := ih hrest
    simp only [completedTxCount] at hi
    have hhead := hu r (List.mem_cons_self ..)
    cases ha : r.action <;> cases hf : r.fault <;>
      simp only [completedTxBytes,Record.completedTxBytes,completedTxCount,List.countP_cons,
        ha,hf,Bool.false_eq_true,↓reduceIte,Nat.add_zero,Nat.zero_add,
        Nat.mul_add,Nat.mul_one]
    all_goals first | exact hi | (have hb := hhead hf _ ha; omega)

end PTX.MBarrier
