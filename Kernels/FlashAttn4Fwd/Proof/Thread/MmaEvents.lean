-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaIssue
public import Kernels.FlashAttn4Fwd.Proof.Bars
public import Lemmas.Flow.Events
public import Lemmas.Flow.NotTcMma
public import Lemmas.Flow.NotCommit
public import Lemmas.Flow.RunInv
public import Lemmas.Flow.BitForms
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! # The MMA warp's events by site

The event of each site of the MMA warp (`Ev`), read off its instruction and the site's
register facts: the polls name their barrier in the thread's CTA and their parity (the Q-full
stage, the KV-full slot of the ring use, the P-ready barriers, the hand-off barrier); the
commits notify one barrier of both CTAs of the pair (`cSpec`, mask 3), named by the thread's
copy; the hand-off arrives on the peer CTA's `+320` barrier. An MMA site fires an MMA: its
registers hold decodable descriptors and an A address in range (`mma_event`, from
`MmaIssue.lean`). Every other site's event uses no mbarrier object and is no MMA. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-! ### Objects and events -/

/-- Barrier `b` of the thread's CTA. -/
abbrev bar (L : Launch) (g : Nat) (b : FBar) : Loc := b.loc L (g / L.block)

/-- The ring slot of use `u` of item `i`. -/
def slotOf (L : Launch) (i u : Nat) : Fin 6 := ⟨kvSlot L i u, Nat.mod_lt _ (by decide)⟩

/-- The ring use of the item that KV poll `k` of trip `t` waits for: the first K, a loop V, a
loop K, the last V (`t = n - 1` there). -/
def kvU : Fin 4 → Nat → Nat
  | 0, _ => 0
  | 1, t => 1 + 2 * t
  | 2, t => 2 + 2 * t
  | 3, t => 1 + 2 * t

/-- The stage of P-ready poll `k` (`+144`/`+152`, `+160`/`+168`). -/
def stOf (k : Fin 4) : Fin 2 := ⟨k.val % 2, Nat.mod_lt _ (by decide)⟩

/-- The barrier commit `c` notifies: S-full of stage 0 or 1, the KV-empty slot of the use it
releases, Q-empty, O-full. -/
def cBar (L : Launch) (d : D) : Fin 12 → FBar
  | 0 | 3 => .sFull 0
  | 1 | 5 => .sFull 1
  | 2 => .kvEmpty (slotOf L d.i 0)
  | 4 | 11 => .kvEmpty (slotOf L d.i (1 + 2 * d.t))
  | 6 => .kvEmpty (slotOf L d.i (2 + 2 * d.t))
  | 7 => .qEmpty 0
  | 8 => .qEmpty 1
  | 9 => .oFull 0
  | 10 => .oFull 1

/-- The commit specification on barrier `m` of the thread's CTA: mask 3, both CTAs of the
pair. -/
def cSpec (L : Launch) (g : Nat) (m : Loc) : TcCommit.Spec :=
  ⟨.two, m, 3, g / L.block / 2 * 2, 2⟩

/-- The event of a state's site. -/
def Ev (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  match d.site with
  | .qWait k => ∃ ok acq sc, e.kind = .wait (bar L g (.qFull k)) (d.i % 2) ok acq sc
  | .kvWait k => ∃ ok acq sc, e.kind =
      .wait (bar L g (.kvFull (slotOf L d.i (kvU k d.t)))) (kvPar L d.i (kvU k d.t)) ok acq sc
  | .pWait k => ∃ ok acq sc, e.kind = .wait (bar L g (.pReady (stOf k))) (pPar L d.i d.t) ok acq sc
  | .p2Wait k _ =>
    ∃ ok acq sc, e.kind = .wait (bar L g (.pReady2 (stOf k))) (pPar L d.i d.t) ok acq sc
  | .waitDealloc => ∃ ok acq sc, e.kind = .wait (bar L g .dealloc) 0 ok acq sc
  | .arrivePeer => ∃ rel sc, e.kind = .arrive (FBar.loc L (peer L g) .dealloc) 0 1 rel sc
  | .commit c => e.kind = .tc (.commit (cSpec L g (bar L g (cBar L d c))))
  | .mma _ _ => isMma e = true
  | _ => ¬ ObjectKind e.kind ∧ isMma e = false

/-! ### Operand evaluation -/

theorem par_b32 (x : Nat) : (truncBits 32 (BitVec.ofNat 64 x)).toNat % 2 = x % 2 := by
  simp only [truncBits, BitVec.toNat_ofNat]
  omega

theorem readBits_b32 {t : TState} {r x : Nat} (h : t.regs r = some (b32 x)) :
    readBits L g t 32 (.reg r) = .ok (truncBits 32 (BitVec.ofNat 64 x)) := by
  simp [readBits, readReg, h, b32, bind, Except.bind, pure, Except.pure]

theorem reg_of {d : D} {t : TState} {r : Nat} {v : Value} (h : Holds t.regs (facts L g d))
    (hl : r ∈ Flow.live d.site.pc) (hv : valueOf L g d r = v) : t.regs r = some v :=
  hv ▸ holds_mem h (Flow.mem_factsFrom hl)

/-- A poll at a barrier address and a parity of the site's facts. -/
theorem wait_of {d : D} {t : TState} {p base par pc : Nat} {acq : Bool} {sc : MbarScope}
    {e : Event} {o : Option TState} (a x : Nat) (h : Holds t.regs (facts L g d))
    (hb : base ∈ Flow.live d.site.pc) (hbv : valueOf L g d base = b32 a)
    (hp : par ∈ Flow.live d.site.pc) (hpv : valueOf L g d par = b32 x) (ha : a < 2 ^ 32)
    (h8 : a % 8 = 0)
    (hf : Fires pc (eventTmpl asms L g t (.mbarWait p base 0 (.reg par) acq sc)) e o) :
    ∃ ok acq' sc', e.kind = .wait ⟨.shared, g / L.block, a⟩ (x % 2) ok acq' sc' := by
  obtain ⟨ok, acq', sc', he, -⟩ :=
    fires_wait_at (mbarLoc_b32 (reg_of h hb hbv) ha h8) (readBits_b32 (reg_of h hp hpv)) hf
  exact ⟨ok, acq', sc', by rw [he, par_b32]⟩

/-- A commit at a barrier address of the site's facts plus an offset, with mask 3. -/
theorem commit_of {d : D} {t : TState} {base mk pc : Nat} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hg : g < L.threads) (a off : Nat) (h : Holds t.regs (facts L g d))
    (hb : base ∈ Flow.live d.site.pc) (hbv : valueOf L g d base = b32 a)
    (hm : mk ∈ Flow.live d.site.pc) (hmv : valueOf L g d mk = .bits 16 (BitVec.ofNat 64 3))
    (ha : a + off < 2 ^ 32) (h8 : (a + off) % 8 = 0)
    (hf : Fires pc (eventTmpl asms L g t (.tcCommit .two base (off : Int) (some (.reg mk)))) e
      o) :
    e.kind = .tc (.commit (cSpec L g ⟨.shared, g / L.block, a + off⟩)) := by
  have hcta : g / L.block < L.grid := by
    unfold Launch.threads at hg
    rw [hpre.block] at hg ⊢
    omega
  have hk : t.regs mk = some (.bits 16 (BitVec.ofNat 64 3)) := reg_of h hm hmv
  have he := (fires_tcCommit_at (s := cSpec L g ⟨.shared, g / L.block, a + off⟩) hg
    (mbarClusterLoc_off (reg_of h hb hbv) ha h8)
    (show readBits L g t 16 (.reg mk) = .ok (truncBits 16 (BitVec.ofNat 64 3)) by
      simp [readBits, readReg, hk, bind, Except.bind, pure, Except.pure]) ?_ hf).1
  · rw [he]
  · have hv := hpre.oneDimLaunch
    simp [TcCommit.resolve, cSpec, Launch.oneDim_clusterOfCta hv.1, Launch.oneDim_clusterStart hv.1,
      Launch.oneDim_clusterSizeOf hv.1, Launch.oneDimLaunch_clusterGridValid hv, hpre.cluster,
      hcta, truncBits]

/-! ### The events of the sites -/

/-- The sites whose instruction uses no mbarrier object and is no MMA. -/
def quietSites : List Site :=
  [.setMaxReg, .alloc, .allocWrite, .bar0, .ldBase, .shflQ, .relinquish, .bar1, .dealloc,
    .exit] ++ (List.finRange 14).map .shfl ++ (List.finRange 8).map .elM ++
    (List.finRange 12).map .elC

theorem quiet_ops : ∀ s ∈ quietSites,
    ((kernel.code[s.pc]?).map fun ins => objectOp ins.op || tcMmaOp ins.op) = some false := by
  decide +kernel

theorem quiet_event {s : Site} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hs : s ∈ quietSites) (hc : kernel.code[s.pc]? = some ins)
    (hf : Fires s.pc (eventTmpl asms L g t ins.op) e o) :
    ¬ ObjectKind e.kind ∧ isMma e = false := by
  have h := quiet_ops s hs
  rw [hc] at h
  simp only [Option.map_some, Option.some.injEq, Bool.or_eq_false_iff] at h
  refine ⟨notObject_of_op h.1 hf, ?_⟩
  cases hm : isMma e
  · rfl
  · exfalso
    unfold isMma at hm
    split at hm
    · rename_i heq
      have := fires_tcMma_op hf heq
      rw [h.2] at this
      cases this
    · cases hm

/-- The shared-memory bounds the event lemmas use. -/
theorem sb_bounds (hpre : Pre P L mem0) :
    L.sharedBase + 328 < 2 ^ 32 ∧ L.sharedBase % 8 = 0 := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hal := hpre.sharedAlignment
  omega

theorem kvSlot_lt (L : Launch) (i u : Nat) : kvSlot L i u < 6 := Nat.mod_lt _ (by decide)

theorem kvPar_mod (L : Launch) (i u : Nat) : kvPar L i u % 2 = kvPar L i u := by
  simp [kvPar]

theorem pPar_mod (L : Launch) (i t : Nat) : pPar L i t % 2 = pPar L i t := by
  simp [pPar]

/-- Closes the location equation of a barrier of the thread's CTA. -/
macro "loc_close" : tactic =>
  `(tactic| (simp [FBar.loc, FBar.off, slotOf, stOf, kvU, cSpec, cBar]; try omega))

theorem qWait_event {d : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (k : Fin 2) (hs : d.site = .qWait k) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e o) :
    ∃ ok acq sc, e.kind = .wait (bar L g (.qFull k)) (d.i % 2) ok acq sc := by
  obtain ⟨site, i, tt, base, pro⟩ := d
  simp only at hs h hc hf ⊢
  subst hs
  have hb := sb_bounds hpre
  fin_cases k <;> code_at hc <;> subst hc
  · obtain ⟨ok, acq, sc, he⟩ := wait_of (L.sharedBase) (i % 2) h (base := 337) (par := 3922)
      (by table_decide) (by mma_values) (by table_decide) (by mma_values) (by omega) (by omega) hf
    exact ⟨ok, acq, sc, by rw [he, Nat.mod_mod]; rfl⟩
  · obtain ⟨ok, acq, sc, he⟩ := wait_of (L.sharedBase + 8) (i % 2) h (base := 883)
      (par := 3922) (by table_decide) (by mma_values) (by table_decide) (by mma_values)
      (by omega) (by omega) hf
    exact ⟨ok, acq, sc, by rw [he, Nat.mod_mod]; rfl⟩

theorem kvWait_event {d : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (k : Fin 4) (hs : d.site = .kvWait k) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e o) :
    ∃ ok acq sc, e.kind = .wait (bar L g (.kvFull (slotOf L d.i (kvU k d.t))))
      (kvPar L d.i (kvU k d.t)) ok acq sc := by
  obtain ⟨site, i, tt, base, pro⟩ := d
  simp only at hs h hc hf ⊢
  subst hs
  have hb := sb_bounds hpre
  have h0 := kvSlot_lt L i 0
  have h1 := kvSlot_lt L i (1 + 2 * tt)
  have h2 := kvSlot_lt L i (2 + 2 * tt)
  fin_cases k <;> code_at hc <;> subst hc
  · obtain ⟨ok, acq, sc, he⟩ := wait_of (L.sharedBase + 8 * kvSlot L i 0 + 32) (kvPar L i 0) h
      (base := 873) (par := 3924) (by table_decide) (by mma_values) (by table_decide)
      (by mma_values) (by omega) (by omega) hf
    exact ⟨ok, acq, sc, by rw [he, kvPar_mod]; congr 1; loc_close⟩
  · obtain ⟨ok, acq, sc, he⟩ := wait_of (L.sharedBase + 8 * kvSlot L i (1 + 2 * tt) + 32)
      (kvPar L i (1 + 2 * tt)) h (base := 891) (par := 3921) (by table_decide) (by mma_values)
      (by table_decide) (by mma_values) (by omega) (by omega) hf
    exact ⟨ok, acq, sc, by rw [he, kvPar_mod]; congr 1; loc_close⟩
  · obtain ⟨ok, acq, sc, he⟩ := wait_of (L.sharedBase + 8 * kvSlot L i (2 + 2 * tt) + 32)
      (kvPar L i (2 + 2 * tt)) h (base := 894) (par := 895) (by table_decide) (by mma_values)
      (by table_decide) (by mma_values) (by omega) (by omega) hf
    exact ⟨ok, acq, sc, by rw [he, kvPar_mod]; congr 1; loc_close⟩
  · obtain ⟨ok, acq, sc, he⟩ := wait_of (L.sharedBase + 8 * kvSlot L i (1 + 2 * tt) + 32)
      (kvPar L i (1 + 2 * tt)) h (base := 931) (par := 3921) (by table_decide) (by mma_values)
      (by table_decide) (by mma_values) (by omega) (by omega) hf
    exact ⟨ok, acq, sc, by rw [he, kvPar_mod]; congr 1; loc_close⟩

theorem pWait_event {d : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (k : Fin 4) (hs : d.site = .pWait k) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e o) :
    ∃ ok acq sc, e.kind = .wait (bar L g (.pReady (stOf k))) (pPar L d.i d.t) ok acq sc := by
  obtain ⟨site, i, tt, base, pro⟩ := d
  simp only at hs h hc hf ⊢
  subst hs
  have hb := sb_bounds hpre
  fin_cases k <;> code_at hc <;> subst hc
  · obtain ⟨ok, acq, sc, he⟩ := wait_of (L.sharedBase + 144) (pPar L i tt) h (base := 932)
      (par := 3918) (by table_decide) (by mma_values) (by table_decide) (by mma_values)
      (by omega) (by omega) hf
    exact ⟨ok, acq, sc, by rw [he, pPar_mod]; rfl⟩
  · obtain ⟨ok, acq, sc, he⟩ := wait_of (L.sharedBase + 152) (pPar L i tt) h (base := 945)
      (par := 3918) (by table_decide) (by mma_values) (by table_decide) (by mma_values)
      (by omega) (by omega) hf
    exact ⟨ok, acq, sc, by rw [he, pPar_mod]; rfl⟩
  · obtain ⟨ok, acq, sc, he⟩ := wait_of (L.sharedBase + 144) (pPar L i tt) h (base := 932)
      (par := 3918) (by table_decide) (by mma_values) (by table_decide) (by mma_values)
      (by omega) (by omega) hf
    exact ⟨ok, acq, sc, by rw [he, pPar_mod]; rfl⟩
  · obtain ⟨ok, acq, sc, he⟩ := wait_of (L.sharedBase + 152) (pPar L i tt) h (base := 945)
      (par := 3918) (by table_decide) (by mma_values) (by table_decide) (by mma_values)
      (by omega) (by omega) hf
    exact ⟨ok, acq, sc, by rw [he, pPar_mod]; rfl⟩

/-- The second P-ready poll reads ordinary registers (the barrier and the parity), which the
live lists cover. -/
theorem p2Wait_event {d : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (k : Fin 4) (lead : Bool) (hs : d.site = .p2Wait k lead)
    (h : Holds t.regs (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e o) :
    ∃ ok acq sc, e.kind = .wait (bar L g (.pReady2 (stOf k))) (pPar L d.i d.t) ok acq sc := by
  obtain ⟨site, i, tt, base, pro⟩ := d
  simp only at hs h hc hf ⊢
  subst hs
  have hb := sb_bounds hpre
  fin_cases k <;> code_at hc <;> subst hc
  · obtain ⟨ok, acq, sc, he⟩ := wait_of (L.sharedBase + 160) (pPar L i tt) h (base := 935)
      (par := 3918) (by table_decide) (by mma_values) (by table_decide) (by mma_values)
      (by omega) (by omega) hf
    exact ⟨ok, acq, sc, by rw [he, pPar_mod]; rfl⟩
  · obtain ⟨ok, acq, sc, he⟩ := wait_of (L.sharedBase + 168) (pPar L i tt) h (base := 949)
      (par := 3918) (by table_decide) (by mma_values) (by table_decide) (by mma_values)
      (by omega) (by omega) hf
    exact ⟨ok, acq, sc, by rw [he, pPar_mod]; rfl⟩
  · obtain ⟨ok, acq, sc, he⟩ := wait_of (L.sharedBase + 160) (pPar L i tt) h (base := 935)
      (par := 3918) (by table_decide) (by mma_values) (by table_decide) (by mma_values)
      (by omega) (by omega) hf
    exact ⟨ok, acq, sc, by rw [he, pPar_mod]; rfl⟩
  · obtain ⟨ok, acq, sc, he⟩ := wait_of (L.sharedBase + 168) (pPar L i tt) h (base := 949)
      (par := 3918) (by table_decide) (by mma_values) (by table_decide) (by mma_values)
      (by omega) (by omega) hf
    exact ⟨ok, acq, sc, by rw [he, pPar_mod]; rfl⟩

theorem waitDealloc_event {d : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hs : d.site = .waitDealloc) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e o) :
    ∃ ok acq sc, e.kind = .wait (bar L g .dealloc) 0 ok acq sc := by
  obtain ⟨site, i, tt, base, pro⟩ := d
  simp only at hs h hc hf ⊢
  subst hs
  have hb := sb_bounds hpre
  code_at hc
  subst hc
  have hr : t.regs 956 = some (b32 (L.sharedBase + 320)) :=
    reg_of h (by table_decide) (by mma_values)
  obtain ⟨ok, acq, sc, he, -⟩ := fires_wait_at (mbarLoc_b32 hr (by omega) (by omega))
    (q := truncBits 32 0) (by simp [readBits]; rfl) hf
  exact ⟨ok, acq, sc, by rw [he]; rfl⟩

theorem arrivePeer_event {d : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hg : g < L.threads) (hs : d.site = .arrivePeer)
    (h : Holds t.regs (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e o) :
    ∃ rel sc, e.kind = .arrive (FBar.loc L (peer L g) .dealloc) 0 1 rel sc := by
  obtain ⟨site, i, tt, base, pro⟩ := d
  simp only at hs h hc hf ⊢
  subst hs
  have hb := sb_bounds hpre
  code_at hc
  subst hc
  have hr : t.regs 958 = some (peerPtr L g) := reg_of h (by table_decide) (by mma_values)
  have hn : t.regs 959 = some (b32 1) := reg_of h (by table_decide) (by mma_values)
  have hcta : g / L.block < L.grid := by
    unfold Launch.threads at hg
    rw [hpre.block] at hg ⊢
    omega
  have hgr := hpre.grid
  have hpe : peer L g = g / L.block / 2 * 2 + (1 - g / L.block % 2) := by
    simp only [peer, clusterOf, ctaOf, rank, Launch.oneDim_clusterOfCta hpre.oneDimLaunch.1,
      hpre.cluster]
  have hm := mbarClusterLoc_ptr (g := g) (base := 958) (a := L.sharedBase + 320) hr hg
    (by omega) (by simp only [Launch.oneDim_clusterOfCta hpre.oneDimLaunch.1, hpre.cluster]; omega)
    (by omega) (by omega)
  obtain ⟨rel, sc, he, -⟩ := fires_arrive_at (cluster := true) (bytes := truncBits 32 0) (n := 1)
    (by simpa using hm) (by simp [readBits]; rfl) (by simp [readBits, readReg, hn, b32, truncBits,
      bind, Except.bind, pure, Except.pure]) hf
  exact ⟨rel, sc, by rw [he]; rfl⟩

theorem commit_event {d : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hg : g < L.threads) (c : Fin 12) (hs : d.site = .commit c)
    (h : Holds t.regs (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e o) :
    e.kind = .tc (.commit (cSpec L g (bar L g (cBar L d c)))) := by
  obtain ⟨site, i, tt, base, pro⟩ := d
  simp only at hs h hc hf ⊢
  subst hs
  have hb := sb_bounds hpre
  have h0 := kvSlot_lt L i 0
  have h1 := kvSlot_lt L i (1 + 2 * tt)
  have h2 := kvSlot_lt L i (2 + 2 * tt)
  fin_cases c <;> code_at hc <;> subst hc
  · rw [commit_of hpre hg (L.sharedBase + 128) 0 h (base := 340) (mk := 323) (by table_decide)
      (by mma_values) (by table_decide) (by mma_values) (by omega) (by omega) hf]
    loc_close
  · rw [commit_of hpre hg (L.sharedBase + 136) 0 h (base := 380) (mk := 324) (by table_decide)
      (by mma_values) (by table_decide) (by mma_values) (by omega) (by omega) hf]
    loc_close
  · rw [commit_of hpre hg (L.sharedBase + 8 * kvSlot L i 0) 80 h (base := 385) (mk := 308)
      (by table_decide) (by mma_values) (by table_decide) (by mma_values) (by omega) (by omega)
      hf]
    loc_close
  · rw [commit_of hpre hg (L.sharedBase + 128) 0 h (base := 340) (mk := 325) (by table_decide)
      (by mma_values) (by table_decide) (by mma_values) (by omega) (by omega) hf]
    loc_close
  · rw [commit_of hpre hg (L.sharedBase + 8 * kvSlot L i (1 + 2 * tt)) 80 h (base := 386)
      (mk := 308) (by table_decide) (by mma_values) (by table_decide) (by mma_values)
      (by omega) (by omega) hf]
    loc_close
  · rw [commit_of hpre hg (L.sharedBase + 136) 0 h (base := 380) (mk := 326) (by table_decide)
      (by mma_values) (by table_decide) (by mma_values) (by omega) (by omega) hf]
    loc_close
  · rw [commit_of hpre hg (L.sharedBase + 8 * kvSlot L i (2 + 2 * tt)) 80 h (base := 388)
      (mk := 308) (by table_decide) (by mma_values) (by table_decide) (by mma_values)
      (by omega) (by omega) hf]
    loc_close
  · rw [commit_of hpre hg (L.sharedBase + 16) 0 h (base := 756) (mk := 308) (by table_decide)
      (by mma_values) (by table_decide) (by mma_values) (by omega) (by omega) hf]
    loc_close
  · rw [commit_of hpre hg (L.sharedBase + 24) 0 h (base := 383) (mk := 308) (by table_decide)
      (by mma_values) (by table_decide) (by mma_values) (by omega) (by omega) hf]
    loc_close
  · rw [commit_of hpre hg (L.sharedBase + 192) 0 h (base := 3250) (mk := 327) (by table_decide)
      (by mma_values) (by table_decide) (by mma_values) (by omega) (by omega) hf]
    loc_close
  · rw [commit_of hpre hg (L.sharedBase + 200) 0 h (base := 382) (mk := 328) (by table_decide)
      (by mma_values) (by table_decide) (by mma_values) (by omega) (by omega) hf]
    loc_close
  · rw [commit_of hpre hg (L.sharedBase + 8 * kvSlot L i (1 + 2 * tt)) 80 h (base := 389)
      (mk := 308) (by table_decide) (by mma_values) (by table_decide) (by mma_values)
      (by omega) (by omega) hf]
    loc_close

/-- A register's table value, up to evaluating the site's election and MMA index. -/
macro "mma_val" : tactic => `(tactic| (mma_values; try rfl))

/-- The low-word bounds of the descriptors (`Pre`'s shared-memory range). -/
macro "lo_ok" : tactic => `(tactic| first
  | omega
  | (simp only [qLo, kLo, vLo, ↓reduceIte, Bool.false_eq_true]; omega))

set_option maxHeartbeats 8000000 in
/-- **An MMA site issues an MMA**: its registers hold the table's values, from which the
instruction's template is an MMA event. -/
theorem mma_event (hpre : Pre P L mem0) (hg : g < L.threads) {b j : Fin 8} {i tt : Nat}
    {base : Value} {pro : Nat → Value} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (h : Holds t.regs (facts L g ⟨.mma b j, i, tt, base, pro⟩))
    (hc : kernel.code[(Site.mma b j).pc]? = some ins)
    (hf : Fires (Site.mma b j).pc (eventTmpl asms L g t ins.op) e o) : isMma e = true := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have h0 := kvSlot_lt L i 0
  have h1 := kvSlot_lt L i (1 + 2 * tt)
  have h2 := kvSlot_lt L i (2 + 2 * tt)
  fin_cases b <;> fin_cases j <;> code_at hc <;> subst hc
  · exact qk_isMma hpre hg (reg_of h (r := 5357) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5343) (v := desc (qLo L true + 0)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (r := 5363) (v := desc (kLo L (kvSlot L i 0) + 0)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val)) ⟨_, rfl⟩ hf
  · exact qk_isMma hpre hg (reg_of h (r := 5357) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5344) (v := desc (qLo L true + 2)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (r := 5364) (v := desc (kLo L (kvSlot L i 0) + 2)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val)) ⟨_, rfl⟩ hf
  · exact qk_isMma hpre hg (reg_of h (r := 5357) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5345) (v := desc (qLo L true + 4)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (r := 5365) (v := desc (kLo L (kvSlot L i 0) + 4)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val)) ⟨_, rfl⟩ hf
  · exact qk_isMma hpre hg (reg_of h (r := 5357) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5346) (v := desc (qLo L true + 6)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (r := 5366) (v := desc (kLo L (kvSlot L i 0) + 6)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val)) ⟨_, rfl⟩ hf
  · exact qk_isMma hpre hg (reg_of h (r := 5357) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5347) (v := desc (qLo L true + 1024)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (r := 5367) (v := desc (kLo L (kvSlot L i 0) + 512)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val)) ⟨_, rfl⟩ hf
  · exact qk_isMma hpre hg (reg_of h (r := 5357) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5348) (v := desc (qLo L true + 1026)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (r := 5368) (v := desc (kLo L (kvSlot L i 0) + 514)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val)) ⟨_, rfl⟩ hf
  · exact qk_isMma hpre hg (reg_of h (r := 5357) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5349) (v := desc (qLo L true + 1028)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (r := 5369) (v := desc (kLo L (kvSlot L i 0) + 516)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val)) ⟨_, rfl⟩ hf
  · exact qk_isMma hpre hg (reg_of h (r := 5357) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5350) (v := desc (qLo L true + 1030)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (r := 5370) (v := desc (kLo L (kvSlot L i 0) + 518)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val)) ⟨_, rfl⟩ hf
  · exact qk_isMma hpre hg (reg_of h (r := 5374) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5343) (v := desc (qLo L false + 0)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (r := 5380) (v := desc (kLo L (kvSlot L i 0) + 0)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val)) ⟨_, rfl⟩ hf
  · exact qk_isMma hpre hg (reg_of h (r := 5374) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5344) (v := desc (qLo L false + 2)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (r := 5381) (v := desc (kLo L (kvSlot L i 0) + 2)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val)) ⟨_, rfl⟩ hf
  · exact qk_isMma hpre hg (reg_of h (r := 5374) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5345) (v := desc (qLo L false + 4)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (r := 5382) (v := desc (kLo L (kvSlot L i 0) + 4)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val)) ⟨_, rfl⟩ hf
  · exact qk_isMma hpre hg (reg_of h (r := 5374) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5346) (v := desc (qLo L false + 6)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (r := 5383) (v := desc (kLo L (kvSlot L i 0) + 6)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val)) ⟨_, rfl⟩ hf
  · exact qk_isMma hpre hg (reg_of h (r := 5374) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5347) (v := desc (qLo L false + 1024)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (r := 5384) (v := desc (kLo L (kvSlot L i 0) + 512)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val)) ⟨_, rfl⟩ hf
  · exact qk_isMma hpre hg (reg_of h (r := 5374) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5348) (v := desc (qLo L false + 1026)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (r := 5385) (v := desc (kLo L (kvSlot L i 0) + 514)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val)) ⟨_, rfl⟩ hf
  · exact qk_isMma hpre hg (reg_of h (r := 5374) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5349) (v := desc (qLo L false + 1028)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (r := 5386) (v := desc (kLo L (kvSlot L i 0) + 516)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val)) ⟨_, rfl⟩ hf
  · exact qk_isMma hpre hg (reg_of h (r := 5374) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5350) (v := desc (qLo L false + 1030)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (r := 5387) (v := desc (kLo L (kvSlot L i 0) + 518)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val)) ⟨_, rfl⟩ hf
  · exact pv_isMma hpre hg (reg_of h (r := 5393) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5394) (by table_decide) (by mma_val)) (by decide)
      ⟨_, tmemOffset_of (a := 64) (off := 0) (by decide)⟩
      (reg_of h (r := 5398) (v := desc (vLo L (kvSlot L i (1 + 2 * tt)) + 0))
        (by table_decide) (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val))
      ⟨_, by simp [mmaEnable, readReg,
        reg_of h (r := 5391) (by table_decide) (by mma_val)]; rfl⟩
      hf
  · exact pv_isMma hpre hg (reg_of h (r := 5393) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5394) (by table_decide) (by mma_val)) (by decide)
      ⟨_, tmemOffset_of (a := 64) (off := 8) (by decide)⟩
      (reg_of h (r := 5398) (v := desc (vLo L (kvSlot L i (1 + 2 * tt)) + 128))
        (by table_decide) (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val))
      ⟨_, rfl⟩ hf
  · exact pv_isMma hpre hg (reg_of h (r := 5393) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5394) (by table_decide) (by mma_val)) (by decide)
      ⟨_, tmemOffset_of (a := 64) (off := 16) (by decide)⟩
      (reg_of h (r := 5398) (v := desc (vLo L (kvSlot L i (1 + 2 * tt)) + 256))
        (by table_decide) (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val))
      ⟨_, rfl⟩ hf
  · exact pv_isMma hpre hg (reg_of h (r := 5393) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5394) (by table_decide) (by mma_val)) (by decide)
      ⟨_, tmemOffset_of (a := 64) (off := 24) (by decide)⟩
      (reg_of h (r := 5398) (v := desc (vLo L (kvSlot L i (1 + 2 * tt)) + 384))
        (by table_decide) (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val))
      ⟨_, rfl⟩ hf
  · exact pv_isMma hpre hg (reg_of h (r := 5393) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5394) (by table_decide) (by mma_val)) (by decide)
      ⟨_, tmemOffset_of (a := 64) (off := 32) (by decide)⟩
      (reg_of h (r := 5398) (v := desc (vLo L (kvSlot L i (1 + 2 * tt)) + 512))
        (by table_decide) (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val))
      ⟨_, rfl⟩ hf
  · exact pv_isMma hpre hg (reg_of h (r := 5393) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5394) (by table_decide) (by mma_val)) (by decide)
      ⟨_, tmemOffset_of (a := 64) (off := 40) (by decide)⟩
      (reg_of h (r := 5398) (v := desc (vLo L (kvSlot L i (1 + 2 * tt)) + 640))
        (by table_decide) (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val))
      ⟨_, rfl⟩ hf
  · exact pv_isMma hpre hg (reg_of h (r := 5393) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5394) (by table_decide) (by mma_val)) (by decide)
      ⟨_, tmemOffset_of (a := 64) (off := 48) (by decide)⟩
      (reg_of h (r := 5398) (v := desc (vLo L (kvSlot L i (1 + 2 * tt)) + 768))
        (by table_decide) (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val))
      ⟨_, rfl⟩ hf
  · exact pv_isMma hpre hg (reg_of h (r := 5393) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5394) (by table_decide) (by mma_val)) (by decide)
      ⟨_, tmemOffset_of (a := 64) (off := 56) (by decide)⟩
      (reg_of h (r := 5398) (v := desc (vLo L (kvSlot L i (1 + 2 * tt)) + 896))
        (by table_decide) (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val))
      ⟨_, rfl⟩ hf
  · exact qk_isMma hpre hg (reg_of h (r := 5403) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5343) (v := desc (qLo L true + 0)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (r := 5409) (v := desc (kLo L (kvSlot L i (2 + 2 * tt)) + 0)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val)) ⟨_, rfl⟩ hf
  · exact qk_isMma hpre hg (reg_of h (r := 5403) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5344) (v := desc (qLo L true + 2)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (r := 5410) (v := desc (kLo L (kvSlot L i (2 + 2 * tt)) + 2)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val)) ⟨_, rfl⟩ hf
  · exact qk_isMma hpre hg (reg_of h (r := 5403) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5345) (v := desc (qLo L true + 4)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (r := 5411) (v := desc (kLo L (kvSlot L i (2 + 2 * tt)) + 4)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val)) ⟨_, rfl⟩ hf
  · exact qk_isMma hpre hg (reg_of h (r := 5403) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5346) (v := desc (qLo L true + 6)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (r := 5412) (v := desc (kLo L (kvSlot L i (2 + 2 * tt)) + 6)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val)) ⟨_, rfl⟩ hf
  · exact qk_isMma hpre hg (reg_of h (r := 5403) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5347) (v := desc (qLo L true + 1024)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (r := 5413) (v := desc (kLo L (kvSlot L i (2 + 2 * tt)) + 512)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val)) ⟨_, rfl⟩ hf
  · exact qk_isMma hpre hg (reg_of h (r := 5403) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5348) (v := desc (qLo L true + 1026)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (r := 5414) (v := desc (kLo L (kvSlot L i (2 + 2 * tt)) + 514)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val)) ⟨_, rfl⟩ hf
  · exact qk_isMma hpre hg (reg_of h (r := 5403) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5349) (v := desc (qLo L true + 1028)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (r := 5415) (v := desc (kLo L (kvSlot L i (2 + 2 * tt)) + 516)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val)) ⟨_, rfl⟩ hf
  · exact qk_isMma hpre hg (reg_of h (r := 5403) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5350) (v := desc (qLo L true + 1030)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (r := 5416) (v := desc (kLo L (kvSlot L i (2 + 2 * tt)) + 518)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val)) ⟨_, rfl⟩ hf
  · exact pv_isMma hpre hg (reg_of h (r := 5421) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5422) (by table_decide) (by mma_val)) (by decide)
      ⟨_, tmemOffset_of (a := 192) (off := 0) (by decide)⟩
      (reg_of h (r := 5426) (v := desc (vLo L (kvSlot L i (1 + 2 * tt)) + 0))
        (by table_decide) (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val))
      ⟨_, by simp [mmaEnable, readReg,
        reg_of h (r := 5419) (by table_decide) (by mma_val)]; rfl⟩
      hf
  · exact pv_isMma hpre hg (reg_of h (r := 5421) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5422) (by table_decide) (by mma_val)) (by decide)
      ⟨_, tmemOffset_of (a := 192) (off := 8) (by decide)⟩
      (reg_of h (r := 5426) (v := desc (vLo L (kvSlot L i (1 + 2 * tt)) + 128))
        (by table_decide) (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val))
      ⟨_, rfl⟩ hf
  · exact pv_isMma hpre hg (reg_of h (r := 5421) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5422) (by table_decide) (by mma_val)) (by decide)
      ⟨_, tmemOffset_of (a := 192) (off := 16) (by decide)⟩
      (reg_of h (r := 5426) (v := desc (vLo L (kvSlot L i (1 + 2 * tt)) + 256))
        (by table_decide) (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val))
      ⟨_, rfl⟩ hf
  · exact pv_isMma hpre hg (reg_of h (r := 5421) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5422) (by table_decide) (by mma_val)) (by decide)
      ⟨_, tmemOffset_of (a := 192) (off := 24) (by decide)⟩
      (reg_of h (r := 5426) (v := desc (vLo L (kvSlot L i (1 + 2 * tt)) + 384))
        (by table_decide) (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val))
      ⟨_, rfl⟩ hf
  · exact pv_isMma hpre hg (reg_of h (r := 5421) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5422) (by table_decide) (by mma_val)) (by decide)
      ⟨_, tmemOffset_of (a := 192) (off := 32) (by decide)⟩
      (reg_of h (r := 5426) (v := desc (vLo L (kvSlot L i (1 + 2 * tt)) + 512))
        (by table_decide) (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val))
      ⟨_, rfl⟩ hf
  · exact pv_isMma hpre hg (reg_of h (r := 5421) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5422) (by table_decide) (by mma_val)) (by decide)
      ⟨_, tmemOffset_of (a := 192) (off := 40) (by decide)⟩
      (reg_of h (r := 5426) (v := desc (vLo L (kvSlot L i (1 + 2 * tt)) + 640))
        (by table_decide) (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val))
      ⟨_, rfl⟩ hf
  · exact pv_isMma hpre hg (reg_of h (r := 5421) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5422) (by table_decide) (by mma_val)) (by decide)
      ⟨_, tmemOffset_of (a := 192) (off := 48) (by decide)⟩
      (reg_of h (r := 5426) (v := desc (vLo L (kvSlot L i (1 + 2 * tt)) + 768))
        (by table_decide) (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val))
      ⟨_, rfl⟩ hf
  · exact pv_isMma hpre hg (reg_of h (r := 5421) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5422) (by table_decide) (by mma_val)) (by decide)
      ⟨_, tmemOffset_of (a := 192) (off := 56) (by decide)⟩
      (reg_of h (r := 5426) (v := desc (vLo L (kvSlot L i (1 + 2 * tt)) + 896))
        (by table_decide) (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val))
      ⟨_, rfl⟩ hf
  · exact qk_isMma hpre hg (reg_of h (r := 5430) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5343) (v := desc (qLo L false + 0)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (r := 5436) (v := desc (kLo L (kvSlot L i (2 + 2 * tt)) + 0)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val)) ⟨_, rfl⟩ hf
  · exact qk_isMma hpre hg (reg_of h (r := 5430) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5344) (v := desc (qLo L false + 2)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (r := 5437) (v := desc (kLo L (kvSlot L i (2 + 2 * tt)) + 2)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val)) ⟨_, rfl⟩ hf
  · exact qk_isMma hpre hg (reg_of h (r := 5430) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5345) (v := desc (qLo L false + 4)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (r := 5438) (v := desc (kLo L (kvSlot L i (2 + 2 * tt)) + 4)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val)) ⟨_, rfl⟩ hf
  · exact qk_isMma hpre hg (reg_of h (r := 5430) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5346) (v := desc (qLo L false + 6)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (r := 5439) (v := desc (kLo L (kvSlot L i (2 + 2 * tt)) + 6)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val)) ⟨_, rfl⟩ hf
  · exact qk_isMma hpre hg (reg_of h (r := 5430) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5347) (v := desc (qLo L false + 1024)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (r := 5440) (v := desc (kLo L (kvSlot L i (2 + 2 * tt)) + 512)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val)) ⟨_, rfl⟩ hf
  · exact qk_isMma hpre hg (reg_of h (r := 5430) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5348) (v := desc (qLo L false + 1026)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (r := 5441) (v := desc (kLo L (kvSlot L i (2 + 2 * tt)) + 514)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val)) ⟨_, rfl⟩ hf
  · exact qk_isMma hpre hg (reg_of h (r := 5430) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5349) (v := desc (qLo L false + 1028)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (r := 5442) (v := desc (kLo L (kvSlot L i (2 + 2 * tt)) + 516)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val)) ⟨_, rfl⟩ hf
  · exact qk_isMma hpre hg (reg_of h (r := 5430) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5350) (v := desc (qLo L false + 1030)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (r := 5443) (v := desc (kLo L (kvSlot L i (2 + 2 * tt)) + 518)) (by table_decide)
        (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val)) ⟨_, rfl⟩ hf
  · exact pv_isMma hpre hg (reg_of h (r := 5449) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5450) (by table_decide) (by mma_val)) (by decide)
      ⟨_, tmemOffset_of (a := 64) (off := 0) (by decide)⟩
      (reg_of h (r := 5454) (v := desc (vLo L (kvSlot L i (1 + 2 * tt)) + 0))
        (by table_decide) (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val))
      ⟨_, by simp [mmaEnable, readReg,
        reg_of h (r := 5447) (by table_decide) (by mma_val)]; rfl⟩
      hf
  · exact pv_isMma hpre hg (reg_of h (r := 5449) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5450) (by table_decide) (by mma_val)) (by decide)
      ⟨_, tmemOffset_of (a := 64) (off := 8) (by decide)⟩
      (reg_of h (r := 5454) (v := desc (vLo L (kvSlot L i (1 + 2 * tt)) + 128))
        (by table_decide) (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val))
      ⟨_, rfl⟩ hf
  · exact pv_isMma hpre hg (reg_of h (r := 5449) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5450) (by table_decide) (by mma_val)) (by decide)
      ⟨_, tmemOffset_of (a := 64) (off := 16) (by decide)⟩
      (reg_of h (r := 5454) (v := desc (vLo L (kvSlot L i (1 + 2 * tt)) + 256))
        (by table_decide) (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val))
      ⟨_, rfl⟩ hf
  · exact pv_isMma hpre hg (reg_of h (r := 5449) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5450) (by table_decide) (by mma_val)) (by decide)
      ⟨_, tmemOffset_of (a := 64) (off := 24) (by decide)⟩
      (reg_of h (r := 5454) (v := desc (vLo L (kvSlot L i (1 + 2 * tt)) + 384))
        (by table_decide) (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val))
      ⟨_, rfl⟩ hf
  · exact pv_isMma hpre hg (reg_of h (r := 5449) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5450) (by table_decide) (by mma_val)) (by decide)
      ⟨_, tmemOffset_of (a := 64) (off := 32) (by decide)⟩
      (reg_of h (r := 5454) (v := desc (vLo L (kvSlot L i (1 + 2 * tt)) + 512))
        (by table_decide) (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val))
      ⟨_, rfl⟩ hf
  · exact pv_isMma hpre hg (reg_of h (r := 5449) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5450) (by table_decide) (by mma_val)) (by decide)
      ⟨_, tmemOffset_of (a := 64) (off := 40) (by decide)⟩
      (reg_of h (r := 5454) (v := desc (vLo L (kvSlot L i (1 + 2 * tt)) + 640))
        (by table_decide) (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val))
      ⟨_, rfl⟩ hf
  · exact pv_isMma hpre hg (reg_of h (r := 5449) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5450) (by table_decide) (by mma_val)) (by decide)
      ⟨_, tmemOffset_of (a := 64) (off := 48) (by decide)⟩
      (reg_of h (r := 5454) (v := desc (vLo L (kvSlot L i (1 + 2 * tt)) + 768))
        (by table_decide) (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val))
      ⟨_, rfl⟩ hf
  · exact pv_isMma hpre hg (reg_of h (r := 5449) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5450) (by table_decide) (by mma_val)) (by decide)
      ⟨_, tmemOffset_of (a := 64) (off := 56) (by decide)⟩
      (reg_of h (r := 5454) (v := desc (vLo L (kvSlot L i (1 + 2 * tt)) + 896))
        (by table_decide) (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val))
      ⟨_, rfl⟩ hf
  · exact pv_isMma hpre hg (reg_of h (r := 5460) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5461) (by table_decide) (by mma_val)) (by decide)
      ⟨_, tmemOffset_of (a := 192) (off := 0) (by decide)⟩
      (reg_of h (r := 5465) (v := desc (vLo L (kvSlot L i (1 + 2 * tt)) + 0))
        (by table_decide) (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val))
      ⟨_, by simp [mmaEnable, readReg,
        reg_of h (r := 5458) (by table_decide) (by mma_val)]; rfl⟩
      hf
  · exact pv_isMma hpre hg (reg_of h (r := 5460) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5461) (by table_decide) (by mma_val)) (by decide)
      ⟨_, tmemOffset_of (a := 192) (off := 8) (by decide)⟩
      (reg_of h (r := 5465) (v := desc (vLo L (kvSlot L i (1 + 2 * tt)) + 128))
        (by table_decide) (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val))
      ⟨_, rfl⟩ hf
  · exact pv_isMma hpre hg (reg_of h (r := 5460) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5461) (by table_decide) (by mma_val)) (by decide)
      ⟨_, tmemOffset_of (a := 192) (off := 16) (by decide)⟩
      (reg_of h (r := 5465) (v := desc (vLo L (kvSlot L i (1 + 2 * tt)) + 256))
        (by table_decide) (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val))
      ⟨_, rfl⟩ hf
  · exact pv_isMma hpre hg (reg_of h (r := 5460) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5461) (by table_decide) (by mma_val)) (by decide)
      ⟨_, tmemOffset_of (a := 192) (off := 24) (by decide)⟩
      (reg_of h (r := 5465) (v := desc (vLo L (kvSlot L i (1 + 2 * tt)) + 384))
        (by table_decide) (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val))
      ⟨_, rfl⟩ hf
  · exact pv_isMma hpre hg (reg_of h (r := 5460) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5461) (by table_decide) (by mma_val)) (by decide)
      ⟨_, tmemOffset_of (a := 192) (off := 32) (by decide)⟩
      (reg_of h (r := 5465) (v := desc (vLo L (kvSlot L i (1 + 2 * tt)) + 512))
        (by table_decide) (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val))
      ⟨_, rfl⟩ hf
  · exact pv_isMma hpre hg (reg_of h (r := 5460) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5461) (by table_decide) (by mma_val)) (by decide)
      ⟨_, tmemOffset_of (a := 192) (off := 40) (by decide)⟩
      (reg_of h (r := 5465) (v := desc (vLo L (kvSlot L i (1 + 2 * tt)) + 640))
        (by table_decide) (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val))
      ⟨_, rfl⟩ hf
  · exact pv_isMma hpre hg (reg_of h (r := 5460) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5461) (by table_decide) (by mma_val)) (by decide)
      ⟨_, tmemOffset_of (a := 192) (off := 48) (by decide)⟩
      (reg_of h (r := 5465) (v := desc (vLo L (kvSlot L i (1 + 2 * tt)) + 768))
        (by table_decide) (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val))
      ⟨_, rfl⟩ hf
  · exact pv_isMma hpre hg (reg_of h (r := 5460) (by table_decide) (by mma_val))
      (by decide) (reg_of h (r := 5461) (by table_decide) (by mma_val)) (by decide)
      ⟨_, tmemOffset_of (a := 192) (off := 56) (by decide)⟩
      (reg_of h (r := 5465) (v := desc (vLo L (kvSlot L i (1 + 2 * tt)) + 896))
        (by table_decide) (by mma_val)) (by lo_ok) (by lo_ok)
      (reg_of h (by table_decide) (by mma_val))
      ⟨_, rfl⟩ hf

/-- The event a state fires is the event of its site (`Ev`). -/
theorem site_event {d : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hg : g < L.threads) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e o) : Ev L g d e := by
  obtain ⟨site, i, tt, base, pro⟩ := d
  cases site with
  | qWait k => exact qWait_event hpre k rfl h hc hf
  | kvWait k => exact kvWait_event hpre k rfl h hc hf
  | pWait k => exact pWait_event hpre k rfl h hc hf
  | p2Wait k lead => exact p2Wait_event hpre k lead rfl h hc hf
  | waitDealloc => exact waitDealloc_event hpre rfl h hc hf
  | arrivePeer => exact arrivePeer_event hpre hg rfl h hc hf
  | commit c => exact commit_event hpre hg c rfl h hc hf
  | mma b j => exact mma_event hpre hg h hc hf
  | shfl k => exact quiet_event (by simp [quietSites]) hc hf
  | elM b => exact quiet_event (by simp [quietSites]) hc hf
  | elC c => exact quiet_event (by simp [quietSites]) hc hf
  | _ => exact quiet_event (by simp [quietSites]) hc hf

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Mma
