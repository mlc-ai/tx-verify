-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Mma.Ledger
public import Lemmas.Flow.PollRounds
public import Lemmas.Flow.ElectLead
import Lemmas.Flow.Step.ShapeRegs
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow PTX.Proof

/-- The QK half's sites. -/
def qkS : Site → Bool
  | .qkBar | .kvWait | .qkShfl | .qkBar2 | .qkElect | .qk _ | .qkCommit => true
  | _ => false

/-- The PV half's sites up to its first commit. -/
def pvS : Site → Bool
  | .pvBar | .pWait | .pvShfl | .pvBar2 | .pvElect | .pv _ | .pvCommit1 => true
  | _ => false

/-- The QK steps done of the current iteration. -/
def kd : Site → Nat
  | .qk j => j.val
  | .qkCommit | .pvBar | .pWait | .pvShfl | .pvBar2 | .pvElect | .pv _ | .pvCommit1
  | .pvCommit2 => 8
  | _ => 0

/-- The PV steps done of the current iteration. -/
def vd : Site → Nat
  | .pv j => j.val
  | .pvCommit1 => 8
  | _ => 0

/-- The sites of the final notification. -/
def finS : Site → Bool
  | .finBar | .finElect | .finCommit => true
  | _ => false

/-- The lane issued QK step `j` at a position below `k`, as its `t`-th ready poll's block. -/
def QKE (X : Execution) (g t : Nat) (j : Fin 8) (k : Nat) : Prop :=
  ∃ kR < k, ∃ dst sp acc mask, X.get (g,kR) = some ⟨qkPc j,.tc (.mma dst sp acc mask)⟩ ∧
    pollRound 2462 ((X.tr g).take kR) = t ∧ pollRound 2510 ((X.tr g).take kR) = t-2

/-- The lane issued PV step `j` at a position below `k`, after `t` PV polls. -/
def PVE (X : Execution) (g t : Nat) (j : Fin 8) (k : Nat) : Prop :=
  ∃ kR < k, ∃ dst sp acc mask, X.get (g,kR) = some ⟨pvPc j,.tc (.mma dst sp acc mask)⟩ ∧
    pollRound 2510 ((X.tr g).take kR) = t

theorem QKE.mono {X g t j k k'} (h : QKE X g t j k) (le : k ≤ k') : QKE X g t j k' := by
  obtain ⟨kR,lt,rest⟩ := h
  exact ⟨kR,by omega,rest⟩

theorem PVE.mono {X g t j k k'} (h : PVE X g t j k) (le : k ≤ k') : PVE X g t j k' := by
  obtain ⟨kR,lt,rest⟩ := h
  exact ⟨kR,by omega,rest⟩

/-- **The history of the lane at a state**: the QK steps of the previous iteration, of the
current one and the PV steps of the current one that precede position `k`. No half is skipped. -/
def Hist (X : Execution) (g : Nat) (d : D) (k : Nat) : Prop :=
  d.site ≠ .qkSkip ∧ d.site ≠ .pvSkip ∧
  ((qkS d.site = true ∨ pvS d.site = true) → 1 ≤ d.i → ∀ j, QKE X g d.i j k) ∧
  (∀ j : Fin 8, j.val < kd d.site → (qkS d.site = true ∨ d.i < d.limit) →
    QKE X g (d.i+1) j k) ∧
  (∀ j : Fin 8, j.val < vd d.site → PVE X g d.i j k) ∧
  ((qkS d.site = true ∨ pvS d.site = true) → 2 ≤ d.i → PVE X g (d.i-1) 7 k) ∧
  (d.site = .pvCommit2 → PVE X g d.i 7 k) ∧
  (finS d.site = true → (1 ≤ d.i → PVE X g (d.i-1) 7 k) ∧
    (d.i = 0 → d.limit = 0 ∨ 2147483646 < d.limit))

theorem Hist.nq {X g d k} (h : Hist X g d k) : d.site ≠ .qkSkip := by
  obtain ⟨x,_,_,_,_,_,_,_⟩ := h
  exact x

theorem Hist.np {X g d k} (h : Hist X g d k) : d.site ≠ .pvSkip := by
  obtain ⟨_,x,_,_,_,_,_,_⟩ := h
  exact x

theorem Hist.prev {X g d k} (h : Hist X g d k) :
    (qkS d.site = true ∨ pvS d.site = true) → 1 ≤ d.i → ∀ j, QKE X g d.i j k := by
  obtain ⟨_,_,x,_,_,_,_,_⟩ := h
  exact x

theorem Hist.cur {X g d k} (h : Hist X g d k) :
    ∀ j : Fin 8, j.val < kd d.site → (qkS d.site = true ∨ d.i < d.limit) →
      QKE X g (d.i+1) j k := by
  obtain ⟨_,_,_,x,_,_,_,_⟩ := h
  exact x

theorem Hist.done {X g d k} (h : Hist X g d k) :
    ∀ j : Fin 8, j.val < vd d.site → PVE X g d.i j k := by
  obtain ⟨_,_,_,_,x,_,_,_⟩ := h
  exact x

theorem Hist.last {X g d k} (h : Hist X g d k) :
    (qkS d.site = true ∨ pvS d.site = true) → 2 ≤ d.i → PVE X g (d.i-1) 7 k := by
  obtain ⟨_,_,_,_,_,x,_,_⟩ := h
  exact x

theorem Hist.commit2 {X g d k} (h : Hist X g d k) :
    d.site = .pvCommit2 → PVE X g d.i 7 k := by
  obtain ⟨_,_,_,_,_,_,x,_⟩ := h
  exact x

theorem Hist.fin {X g d k} (h : Hist X g d k) :
    finS d.site = true → (1 ≤ d.i → PVE X g (d.i-1) 7 k) ∧
      (d.i = 0 → d.limit = 0 ∨ 2147483646 < d.limit) := by
  obtain ⟨_,_,_,_,_,_,_,x⟩ := h
  exact x

theorem Hist.mono {X g d k k'} (h : Hist X g d k) (le : k ≤ k') : Hist X g d k' :=
  ⟨h.nq,h.np,fun a b j => (h.prev a b j).mono le,fun j a b => (h.cur j a b).mono le,
    fun j a => (h.done j a).mono le,fun a b => (h.last a b).mono le,
    fun a => (h.commit2 a).mono le,fun a => ⟨fun b => ((h.fin a).1 b).mono le,(h.fin a).2⟩⟩

theorem hist_init {X g k} : Hist X g {} k := by
  refine ⟨by decide,by decide,fun h => ?_,fun j h => ?_,fun j h => ?_,fun h => ?_,fun h => ?_,
    fun h => ?_⟩
  · change (qkS .setMaxReg = true ∨ pvS .setMaxReg = true) at h
    simp [qkS,pvS] at h
  · simp [kd] at h
  · simp [vd] at h
  · change (qkS .setMaxReg = true ∨ pvS .setMaxReg = true) at h
    simp [qkS,pvS] at h
  · cases h
  · cases h

variable {L : Launch} {g : Nat} {X : Execution}

theorem hist_quiet {X g s i w k} (n1 : qkS s = false) (n2 : pvS s = false) (n3 : kd s = 0)
    (n4 : vd s = 0) (n5 : s ≠ .qkSkip) (n6 : s ≠ .pvSkip)
    (n7 : s ≠ .pvCommit2 := by decide) (n8 : finS s = false := by decide) :
    Hist X g ⟨s,i,w⟩ k := by
  refine ⟨n5,n6,fun h => ?_,fun j h => ?_,fun j h => ?_,fun h => ?_,fun h => ?_,
    fun h => ?_⟩
  · simp [n1,n2] at h
  · simp [n3] at h
  · simp [n4] at h
  · simp [n1,n2] at h
  · exact absurd h n7
  · rw [n8] at h
    cases h

theorem hist_fin {X g s i w k} (hs : finS s = true)
    (h : (1 ≤ i → PVE X g (i-1) 7 k) ∧
      (i = 0 → D.limit ⟨s,i,w⟩ = 0 ∨ 2147483646 < D.limit ⟨s,i,w⟩)) :
    Hist X g ⟨s,i,w⟩ k := by
  have n1 : qkS s = false := by cases s <;> simp_all [finS,qkS]
  have n2 : pvS s = false := by cases s <;> simp_all [finS,pvS]
  have n3 : kd s = 0 := by cases s <;> simp_all [finS,kd]
  have n4 : vd s = 0 := by cases s <;> simp_all [finS,vd]
  refine ⟨by cases s <;> simp_all [finS],by cases s <;> simp_all [finS],fun h => ?_,fun j h => ?_,
    fun j h => ?_,fun h => ?_,fun h => ?_,fun _ => h⟩
  · simp [n1,n2] at h
  · simp [n3] at h
  · simp [n4] at h
  · simp [n1,n2] at h
  · cases s <;> simp_all [finS]

private theorem mma_code (j : Fin 8) :
    (∃ i m, kernel.code[qkPc j]? = some ⟨i,.tcMma m⟩) ∧
    (∃ i m, kernel.code[pvPc j]? = some ⟨i,.tcMma m⟩) := by
  fin_cases j
  · exact ⟨⟨_,_,Flow.code_mma_0⟩,⟨_,_,Flow.code_mma_8⟩⟩
  · exact ⟨⟨_,_,Flow.code_mma_1⟩,⟨_,_,Flow.code_mma_9⟩⟩
  · exact ⟨⟨_,_,Flow.code_mma_2⟩,⟨_,_,Flow.code_mma_10⟩⟩
  · exact ⟨⟨_,_,Flow.code_mma_3⟩,⟨_,_,Flow.code_mma_11⟩⟩
  · exact ⟨⟨_,_,Flow.code_mma_4⟩,⟨_,_,Flow.code_mma_12⟩⟩
  · exact ⟨⟨_,_,Flow.code_mma_5⟩,⟨_,_,Flow.code_mma_13⟩⟩
  · exact ⟨⟨_,_,Flow.code_mma_6⟩,⟨_,_,Flow.code_mma_14⟩⟩
  · exact ⟨⟨_,_,Flow.code_mma_7⟩,⟨_,_,Flow.code_mma_15⟩⟩

private theorem mma_kind {pc : Nat} {e : Event} {t ins o}
    (hcode : ∃ i m, kernel.code[pc]? = some ⟨i,.tcMma m⟩) (hc : kernel.code[pc]? = some ins)
    (ff : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o)
    (clean : ∀ f, e.kind ≠ .ub f) (hpc : e.pc = pc) :
    ∃ dst sp acc mask, e = ⟨pc,.tc (.mma dst sp acc mask)⟩ := by
  obtain ⟨i,m,hm⟩ := hcode
  obtain rfl := Option.some.inj (hc.symm.trans hm)
  rcases fires_tcMma_kind ff with ⟨dst,sp,acc,mask,kind⟩ | ⟨f,kind⟩
  · obtain ⟨epc,ekind⟩ := e
    change epc = pc at hpc
    change ekind = _ at kind
    subst hpc kind
    exact ⟨dst,sp,acc,mask,rfl⟩
  · exact (clean f kind).elim

set_option hygiene false in
local macro "hsame" : tactic => `(tactic| (
  simp only [Hist,kd,vd,qkS,pvS,finS,D.limit] at h ⊢
  simpa using h))

theorem hist_step {k d d' e} (hlead : ElectLead L g (X.tr g))
    (seven : ∀ k pc md a b c recv ok, X.get (g,k) = some ⟨pc,.shfl md a b c recv ok⟩ →
      (pc = 2464 ∨ pc = 2512) → recv = b32 7)
    (get : X.get (g,k) = some e) (clean : ∀ f, e.kind ≠ .ub f) (pc : e.pc = d.site.pc)
    (inv : Inv d)
    (q : pollRound 2462 ((X.tr g).take k) = (polls d).1)
    (p : pollRound 2510 ((X.tr g).take k) = (polls d).2)
    (fires : ∃ t ins o, kernel.code[d.site.pc]? = some ins ∧
      Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e o)
    (h : Hist X g d k) (move : next L g d e = some (some d')) : Hist X g d' (k+1) := by
  have h := h.mono (Nat.le_succ k)
  obtain ⟨t,ins,o,hc,ff⟩ := fires
  obtain ⟨s,i,v⟩ := d
  cases s with
  | setMaxReg =>
    simp only [next] at move
    obtain rfl := Option.some.inj (Option.some.inj move)
    exact hist_quiet rfl rfl rfl rfl (by decide) (by decide)
  | ldNum =>
    simp only [next] at move
    split at move
    · rename_i bs _
      cases hw : Except.toOption (rebuild 3 bs) with
      | none => simp only [hw] at move; exact absurd move (by simp)
      | some v' =>
        simp only [hw] at move
        obtain rfl := Option.some.inj (Option.some.inj move)
        exact hist_quiet rfl rfl rfl rfl (by simp) (by simp)
    · exact absurd move (by simp)
  | bar0 =>
    simp only [next] at move
    obtain rfl := Option.some.inj (Option.some.inj move)
    have i0 : i = 0 := inv
    subst i0
    simp only [startSite]
    split
    · rename_i hc
      exact hist_fin rfl ⟨fun h => absurd h (by omega),fun _ => hc⟩
    · refine ⟨by simp,by simp,fun _ h => by simp at h,fun j h => ?_,fun j h => ?_,
        fun _ h => by simp at h,fun h => by simp at h,fun h => by simp [finS] at h⟩
      · simp [kd] at h
      · simp [vd] at h
  | qkBar =>
    simp only [next] at move
    obtain rfl := Option.some.inj (Option.some.inj move)
    simp only [Hist,kd,vd,qkS,pvS,finS,D.limit] at h ⊢
    simpa using h
  | kvWait =>
    simp only [next] at move
    split at move
    · split at move
      · obtain rfl := Option.some.inj (Option.some.inj move)
        hsame
      · obtain rfl := Option.some.inj (Option.some.inj move)
        exact h
    · exact absurd move (by simp)
  | qkShfl =>
    simp only [next] at move
    split at move
    · rename_i md a b c recv ok heq
      have ev : e = ⟨e.pc,.shfl md a b c recv ok⟩ := by
        cases e; simp only at heq ⊢; rw [heq]
      rw [ev] at get
      have r7 := seven k e.pc md a b c recv ok get (.inl (pc.trans rfl))
      subst r7
      obtain rfl := Option.some.inj (Option.some.inj move)
      have : low (b32 7) = 7 := by decide
      simp only [this,↓reduceIte]
      hsame
    · exact absurd move (by simp)
  | qkBar2 =>
    simp only [next] at move
    obtain rfl := Option.some.inj (Option.some.inj move)
    hsame
  | qkSkip => exact absurd rfl h.nq
  | qkElect =>
    simp only [next] at move
    split at move
    · rename_i mask inst lead heq
      have win := hlead _ (List.mem_of_getElem? get) mask inst lead heq
      split at move
      · obtain rfl := Option.some.inj (Option.some.inj move)
        hsame
      · rename_i no
        exact absurd win.symm no
    · exact absurd move (by simp)
  | qk j =>
    have ev := (mma_kind (mma_code j).1 (hc : kernel.code[qkPc j]? = some ins) ff clean pc)
    obtain ⟨dst,sp,acc,mask,rfl⟩ := ev
    change pollRound 2462 _ = i+1 at q
    change pollRound 2510 _ = i-1 at p
    have new : QKE X g (i+1) j (k+1) := ⟨k,by omega,dst,sp,acc,mask,get,q,by omega⟩
    have old := h.cur
    have c1 := h.prev
    have c5 := h.last
    simp only [next,issueNext] at move
    have step : ∀ (s' : Site) (_ : s' ≠ .qkSkip) (_ : s' ≠ .pvSkip) (_ : qkS s' = true)
        (_ : kd s' = j.val+1) (_ : pvS s' = false), vd s' = 0 → finS s' = false →
        Hist X g ⟨s',i,v⟩ (k+1) := by
      intro s' n1 n2 hq hk hp hv hfn
      refine ⟨n1,n2,fun _ hi => c1 (.inl rfl) hi,fun j' hj' _ => ?_,fun j' hj' => ?_,
        fun _ hi => c5 (.inl rfl) hi,fun hs => by
          have hs : s' = .pvCommit2 := hs
          subst hs; simp [qkS] at hq,fun hf => by simp [hfn] at hf⟩
      · rw [hk] at hj'
        rcases Nat.lt_or_ge j'.val j.val with lt | ge
        · exact old j' lt (.inl rfl)
        · obtain rfl : j' = j := Fin.ext (by omega)
          exact new
      · simp [hv] at hj'
    split at move
    · obtain rfl := Option.some.inj (Option.some.inj move)
      exact step _ (by simp) (by simp) rfl (by simp [kd]) rfl rfl rfl
    · obtain rfl := Option.some.inj (Option.some.inj move)
      refine step _ (by simp) (by simp) rfl ?_ rfl rfl rfl
      simp only [kd]
      omega
  | qkCommit =>
    simp only [next,afterQk,iterNext] at move
    have inv' : i < low v ∧ low v ≤ 2147483646 := inv
    have c1 := h.prev
    have c2 := h.cur
    have c5 := h.last
    split at move
    · rename_i i0
      subst i0
      split at move
      · rename_i e0
        exfalso
        simp only [D.limit] at e0
        omega
      · rename_i ne
        split at move
        · obtain rfl := Option.some.inj (Option.some.inj move)
          refine ⟨by simp,by simp,fun _ _ j => c2 j (by simp [kd]) (.inl rfl),fun j hj => ?_,
            fun j hj => ?_,fun _ h => by simp at h,fun h => by simp at h,
            fun h => by simp [finS] at h⟩
          · simp [kd] at hj
          · simp [vd] at hj
        · rename_i big
          obtain rfl := Option.some.inj (Option.some.inj move)
          refine ⟨by simp,by simp,fun _ _ j => c2 j (by simp [kd]) (.inl rfl),fun j hj cond => ?_,
            fun j hj => ?_,fun _ h => by simp at h,fun h => by simp at h,
            fun h => by simp [finS] at h⟩
          · exfalso
            simp only [D.limit,qkS] at cond
            rcases cond with c|c
            · simp at c
            · exact big c
          · simp [vd] at hj
    · rename_i i0
      obtain rfl := Option.some.inj (Option.some.inj move)
      refine ⟨by simp,by simp,fun _ hi j => c1 (.inl rfl) hi j,fun j hj _ => ?_,fun j hj => ?_,
        fun _ hi => c5 (.inl rfl) hi,fun h => by simp at h,fun h => by simp [finS] at h⟩
      · exact c2 j (by simp [kd]) (.inl rfl)
      · simp [vd] at hj
  | pvBar =>
    simp only [next] at move
    obtain rfl := Option.some.inj (Option.some.inj move)
    hsame
  | pWait =>
    simp only [next] at move
    split at move
    · split at move
      · obtain rfl := Option.some.inj (Option.some.inj move)
        hsame
      · obtain rfl := Option.some.inj (Option.some.inj move)
        exact h
    · exact absurd move (by simp)
  | pvShfl =>
    simp only [next] at move
    split at move
    · rename_i md a b c recv ok heq
      have ev : e = ⟨e.pc,.shfl md a b c recv ok⟩ := by
        cases e; simp only at heq ⊢; rw [heq]
      rw [ev] at get
      have r7 := seven k e.pc md a b c recv ok get (.inr (pc.trans rfl))
      subst r7
      obtain rfl := Option.some.inj (Option.some.inj move)
      have : low (b32 7) = 7 := by decide
      simp only [this,↓reduceIte]
      hsame
    · exact absurd move (by simp)
  | pvBar2 =>
    simp only [next] at move
    obtain rfl := Option.some.inj (Option.some.inj move)
    hsame
  | pvSkip => exact absurd rfl h.np
  | pvElect =>
    simp only [next] at move
    split at move
    · rename_i mask inst lead heq
      have win := hlead _ (List.mem_of_getElem? get) mask inst lead heq
      split at move
      · obtain rfl := Option.some.inj (Option.some.inj move)
        hsame
      · rename_i no
        exact absurd win.symm no
    · exact absurd move (by simp)
  | pv j =>
    have ev := (mma_kind (mma_code j).2 (hc : kernel.code[pvPc j]? = some ins) ff clean pc)
    obtain ⟨dst,sp,acc,mask,rfl⟩ := ev
    change pollRound 2510 _ = i at p
    have new : PVE X g i j (k+1) := ⟨k,by omega,dst,sp,acc,mask,get,p⟩
    have c1 := h.prev
    have c2 := h.cur
    have c3 := h.done
    have c5 := h.last
    simp only [next,issueNext] at move
    have step : ∀ (s' : Site) (_ : s' ≠ .qkSkip) (_ : s' ≠ .pvSkip) (_ : pvS s' = true)
        (_ : qkS s' = false) (_ : kd s' = 8), vd s' = j.val+1 → finS s' = false →
        Hist X g ⟨s',i,v⟩ (k+1) := by
      intro s' n1 n2 hq hk hp hv hfn
      refine ⟨n1,n2,fun _ hi => c1 (.inr rfl) hi,fun j' hj' cond => ?_,fun j' hj' => ?_,
        fun _ hi => c5 (.inr rfl) hi,fun hs => by
          have hs : s' = .pvCommit2 := hs
          subst hs; simp [pvS] at hq,fun hf => by simp [hfn] at hf⟩
      · simp only [hk] at cond ⊢
        exact c2 j' (by simp [kd]) cond
      · rw [hv] at hj'
        rcases Nat.lt_or_ge j'.val j.val with lt | ge
        · exact c3 j' lt
        · obtain rfl : j' = j := Fin.ext (by omega)
          exact new
    split at move
    · obtain rfl := Option.some.inj (Option.some.inj move)
      exact step _ (by simp) (by simp) rfl rfl rfl (by simp [vd]) rfl
    · obtain rfl := Option.some.inj (Option.some.inj move)
      refine step _ (by simp) (by simp) rfl rfl rfl ?_ rfl
      simp only [vd]
      omega
  | pvCommit1 =>
    simp only [next] at move
    obtain rfl := Option.some.inj (Option.some.inj move)
    refine ⟨by simp,by simp,fun hh => by simp [qkS,pvS] at hh,fun j hj cond => ?_,
      fun j hj => by simp [vd] at hj,fun hh => by simp [qkS,pvS] at hh,
      fun _ => h.done 7 (by simp [vd]),fun hh => by simp [finS] at hh⟩
    exact h.cur j (by simp [kd]) (by
      simp only [qkS,D.limit,Bool.false_eq_true,false_or] at cond ⊢
      exact cond)
  | pvCommit2 =>
    simp only [next,iterNext] at move
    have inv' : 0 < i ∧ i ≤ low v ∧ low v ≤ 2147483646 := inv
    have c2 := h.cur
    have c6 := h.commit2 rfl
    split at move
    · obtain rfl := Option.some.inj (Option.some.inj move)
      exact hist_fin rfl ⟨fun _ => by simpa using c6,fun h => by omega⟩
    · rename_i ne
      have lt : i < low v := by
        have : i ≠ low v := ne
        omega
      split at move
      · obtain rfl := Option.some.inj (Option.some.inj move)
        refine ⟨by simp,by simp,fun _ _ j => c2 j (by simp [kd]) (by simp [qkS,D.limit,lt]),
          fun j hj => ?_,fun j hj => ?_,fun _ h => ?_,fun h => by simp at h,
          fun h => by simp [finS] at h⟩
        · simp [kd] at hj
        · simp [vd] at hj
        · simpa using c6
      · rename_i big
        obtain rfl := Option.some.inj (Option.some.inj move)
        refine ⟨by simp,by simp,fun _ _ j => c2 j (by simp [kd]) (by simp [qkS,D.limit,lt]),
          fun j hj cond => ?_,fun j hj => ?_,fun _ h => by simpa using c6,
          fun h => by simp at h,fun h => by simp [finS] at h⟩
        · exfalso
          simp only [D.limit,qkS] at cond
          rcases cond with c|c
          · simp at c
          · exact big c
        · simp [vd] at hj
  | finBar =>
    simp only [next] at move
    obtain rfl := Option.some.inj (Option.some.inj move)
    exact hist_fin rfl (h.fin rfl)
  | finElect =>
    simp only [next] at move
    split at move
    · split at move
      · obtain rfl := Option.some.inj (Option.some.inj move)
        exact hist_fin rfl (h.fin rfl)
      · obtain rfl := Option.some.inj (Option.some.inj move)
        exact hist_quiet rfl rfl rfl rfl (by simp) (by simp)
    · exact absurd move (by simp)
  | finCommit =>
    simp only [next] at move
    obtain rfl := Option.some.inj (Option.some.inj move)
    exact hist_quiet rfl rfl rfl rfl (by simp) (by simp)
  | bar1 =>
    simp only [next] at move
    obtain rfl := Option.some.inj (Option.some.inj move)
    exact hist_quiet rfl rfl rfl rfl (by simp) (by simp)
  | setMaxRegInc =>
    simp only [next] at move
    obtain rfl := Option.some.inj (Option.some.inj move)
    exact hist_quiet rfl rfl rfl rfl (by simp) (by simp)
  | dispatch =>
    simp only [next] at move
    exact absurd move (by simp)

end PTX.Kernels.InklingRelDecode.Proof.Mma
