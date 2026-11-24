-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaCountsEv
public import Lemmas.Flow.TmemOperands
public import Lemmas.Flow.LoadShared
public import Lemmas.Flow.LoadSharedSize
public import Lemmas.Flow.ElectMask

@[expose] public section

/-! # The start and end events of the MMA warp

The events of the sites that `Ev` leaves as "no object, no MMA", read off their instructions
and register facts, for a continuing event (one with a successor state):

* the paired Tensor Memory operations are the allocation (`alloc_site`: 512 columns into the base
  word of the thread's CTA), the relinquishment and the deallocation (`dealloc_site`: of the
  column the carried address holds), and no other site makes one (`tmemOp_site`);
* the events on barrier 2 are the two `bar.sync 2, 416` (`bar2_site`);
* the allocation's address store writes the base word (`allocWrite_site`), the read-back reads
  it (`ldBase_site`), and no other site writes (`write_site`) or, before the read-back, reads
  (`read_site`);
* only the exit site exits (`exit_site`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState} {ins : Instr}
  {e : Event} {o : Option TState}

/-! ### The instructions of the sites -/

/-- The sites of the paired Tensor Memory instruction, of the two `bar.sync 2`, of the
allocation (whose second event stores), of `ret`. -/
def Site.res : Site → Bool
  | .alloc | .allocWrite | .relinquish | .dealloc => true
  | _ => false

def Site.isBar2 : Site → Bool
  | .bar0 | .bar1 => true
  | _ => false

def Site.isAlloc : Site → Bool
  | .alloc | .allocWrite => true
  | _ => false

def Site.isExit : Site → Bool
  | .exit => true
  | _ => false

/-- Whether an instruction is `ret` or `exit`. -/
def retOp : Op → Bool
  | .ret | .exit => true
  | _ => false

/-- The instructions of every site but those `p` selects make `f` false. -/
def OpsOff (p : Site → Bool) (f : Op → Bool) : Prop :=
  allSites.all (fun s => p s ||
    decide ((kernel.code[s.pc]?).map (fun ins => f ins.op) = some false))
    = true

theorem tmem_ops : OpsOff Site.res tmemOp := by
  unfold OpsOff
  decide +kernel

theorem bar_ops : OpsOff Site.isBar2 barOp := by
  unfold OpsOff
  decide +kernel

theorem write_ops : OpsOff Site.isAlloc writeOp := by
  unfold OpsOff
  decide +kernel

theorem ret_ops : OpsOff Site.isExit retOp := by
  unfold OpsOff
  decide +kernel

theorem OpsOff.op {p : Site → Bool} {f : Op → Bool} (h : OpsOff p f) {s : Site}
    (hp : p s = false) (hc : kernel.code[s.pc]? = some ins) : f ins.op = false := by
  unfold OpsOff at h
  have h := List.all_eq_true.mp h s (mem_allSites s)
  rw [hp, Bool.false_or, hc] at h
  simpa using h

theorem electSite_ops : OpsOff Site.isElect electOp := by
  unfold OpsOff
  decide +kernel

/-- A continuing event is no undefined behaviour. -/
theorem notUb_of_some {pc : Nat} {m : Tmpl} (hf : Fires pc m e (some u)) : ∀ f, e.kind ≠ .ub f := by
  intro f hk
  cases m <;> simp only [Fires] at hf
  all_goals first
    | (obtain ⟨-, h⟩ := hf; cases h; done)
    | (obtain ⟨_, rfl, -⟩ := hf; cases hk)
    | (obtain ⟨_, _, rfl, -⟩ := hf; cases hk)
    | (obtain ⟨_, _, _, rfl, -⟩ := hf; cases hk)
    | (obtain ⟨rfl, -⟩ := hf; cases hk)

/-! ### The events -/

theorem reg_b32 {r x : Nat} (h : Holds t.regs (facts L g d)) (hl : r ∈ Flow.live d.site.pc)
    (hv : valueOf L g d r = b32 x) : t.regs r = some (b32 x) := reg_of h hl hv

/-- **The allocation** requests 512 columns into the base word of the thread's CTA. -/
theorem alloc_site (hpre : Pre P L mem0) (hd : d.site = .alloc) (hs : t.sub = 0)
    (h : Holds t.regs (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    e.kind = .tc (.resource .two (some (baseAt L g)) (.alloc 512)) := by
  obtain ⟨site, i, tt, base, pro⟩ := d
  simp only at hd h hc hf ⊢
  subst hd
  have hb := sb_bounds hpre
  code_at hc
  subst hc
  have hr := reg_b32 (r := 337) (x := L.sharedBase) h (by table_decide) (by mma_values)
  have hn := reg_b32 (r := 861) (x := 512) h (by table_decide) (by mma_values)
  have he := fires_tcAlloc_at (effAddr_b32_off (off := 328) hr (by omega)) (readBits_b32 hn) hs hf
  rw [he]
  simp [baseAt, truncBits]

/-- **The address store** writes the four bytes of the base word of the thread's CTA. -/
theorem allocWrite_site (hpre : Pre P L mem0) (hd : d.site = .allocWrite) (hs : t.sub = 1)
    (h : Holds t.regs (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ a bs, e.kind = .wr a bs ∧ a.loc = baseAt L g ∧ a.size = 4 ∧ bs.length = 4 := by
  obtain ⟨site, i, tt, base, pro⟩ := d
  simp only at hd h hc hf ⊢
  subst hd
  have hb := sb_bounds hpre
  code_at hc
  subst hc
  have hr := reg_b32 (r := 337) (x := L.sharedBase) h (by table_decide) (by mma_values)
  exact fires_tcAllocStore_at (effAddr_b32_off (off := 328) hr (by omega)) hs hf
    (notUb_of_some hf)

/-- **The read-back** reads the four bytes of the base word of the thread's CTA. -/
theorem ldBase_site (hpre : Pre P L mem0) (hd : d.site = .ldBase) (hs : t.sub = 0)
    (h : Holds t.regs (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ a bs, e.kind = .rd a bs ∧ a.loc = baseAt L g ∧ a.size = 4 := by
  obtain ⟨site, i, tt, base, pro⟩ := d
  simp only at hd h hc hf ⊢
  subst hd
  have hb := sb_bounds hpre
  code_at hc
  subst hc
  have hr := reg_b32 (r := 337) (x := L.sharedBase) h (by table_decide) (by mma_values)
  obtain ⟨ac, bs, rfl, hl, -⟩ := fires_ld_shared (off := 328) hr (by omega) hs hf
  exact ⟨ac, bs, rfl, hl, fires_ld_shared_size (off := 328) hr (by omega) hs hf ac bs rfl⟩

/-- **The deallocation** frees 512 columns at the column the carried address holds. -/
theorem dealloc_site (hd : d.site = .dealloc) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ a, e.kind = .tc (.resource .two none (.dealloc a 512)) ∧
      ∀ col, d.base = b32 col → a = col % 2 ^ 32 := by
  obtain ⟨site, i, tt, base, pro⟩ := d
  simp only at hd h hc hf ⊢
  subst hd
  code_at hc
  subst hc
  obtain ⟨dst, act, hk⟩ := fires_tcDealloc_some hf
  have hn := reg_b32 (r := 960) (x := 512) h (by table_decide) (by mma_values)
  obtain ⟨-, rfl, n, a, hn', rfl⟩ := fires_tcDealloc_resource hf hk
  rw [readBits_b32 hn] at hn'
  obtain rfl := (Except.ok.inj hn').symm
  refine ⟨a, by rw [hk]; simp [truncBits], fun col hcol => ?_⟩
  subst hcol
  have ha := reg_b32 (r := 379) (x := col) h (by table_decide) (by mma_values)
  obtain ⟨-, -, hact⟩ := fires_tcDealloc_at (readBits_b32 ha) (readBits_b32 hn) hf hk
  simp only [Tmem.Request.dealloc.injEq] at hact
  rw [hact.1]
  simp [truncBits]
  omega

/-- **The paired Tensor Memory operations** are the allocation's, the relinquishment's and the
deallocation's. -/
theorem tmemOp_site (hpre : Pre P L mem0) (hs : t.sub = d.site.sub)
    (h : Holds t.regs (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    Tmem.Pair.isTmemOp e = tmemEv d.site (outcome L g e) := by
  have hoff : d.site.res = false → Tmem.Pair.isTmemOp e = false := fun hr => by
    have hop := tmem_ops.op hr hc
    unfold Tmem.Pair.isTmemOp
    split
    · rename_i grp dst act hk
      rw [fires_resource_op hf hk] at hop
      cases hop
    · rfl
  obtain ⟨site, i, tt, base, pro⟩ := d
  cases site
  case alloc => rw [Tmem.Pair.isTmemOp, alloc_site hpre rfl hs h hc hf]; rfl
  case allocWrite =>
    obtain ⟨a, bs, hk, -⟩ := allocWrite_site hpre rfl hs h hc hf
    simp [Tmem.Pair.isTmemOp, hk, tmemEv]
  case relinquish =>
    code_at hc
    subst hc
    rw [Tmem.Pair.isTmemOp, fires_tcRelinquish_some hf]
    rfl
  case dealloc =>
    obtain ⟨a, hk, -⟩ := dealloc_site rfl h hc hf
    simp [Tmem.Pair.isTmemOp, hk, tmemEv]
  all_goals rw [hoff rfl]; simp [tmemEv]

/-- **The events on barrier 2** are the two `bar.sync 2, 416`. -/
theorem bar2_site (hpre : Pre P L mem0) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e o) :
    Execution.isBarId 2 e = bar2Ev d.site (outcome L g e) ∧
      (Execution.isBarId 2 e = true → e.kind = .bar 2 (some 416) .sync) := by
  have hoff : d.site.isBar2 = false → Execution.isBarId 2 e = false := fun hr => by
    have hop := bar_ops.op hr hc
    unfold Execution.isBarId
    split
    · rename_i id' c m hk
      rw [fires_bar_op hf hk] at hop
      cases hop
    · rfl
  have hon : d.site.isBar2 = true → e.kind = .bar 2 (some 416) .sync := fun hr => by
    obtain ⟨site, i, tt, base, pro⟩ := d
    cases site <;> simp only [Site.isBar2, Bool.false_eq_true] at hr <;> code_at hc <;> subst hc <;>
      rw [fires_barSyncN_imm (id := 2) (n := 416) (by omega) (by omega) (by omega) (by omega)
        (by rw [hpre.block]; omega) hf]
  cases hb : d.site.isBar2
  · rw [hoff hb]
    refine ⟨?_, fun h => by cases h⟩
    obtain ⟨site, i, tt, base, pro⟩ := d
    cases site <;> simp_all [Site.isBar2, bar2Ev]
  · have hk := hon hb
    refine ⟨?_, fun _ => hk⟩
    obtain ⟨site, i, tt, base, pro⟩ := d
    cases site <;> simp_all [Site.isBar2, bar2Ev, Execution.isBarId]

/-- **Only the allocation's address store writes.** -/
theorem write_site (hpre : Pre P L mem0) (hs : t.sub = d.site.sub)
    (h : Holds t.regs (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) {a : Acc} {bs : List Byte}
    (hk : e.kind = .wr a bs) : d.site = .allocWrite := by
  cases ha : d.site.isAlloc
  · have hop := write_ops.op ha hc
    rw [fires_write_op hf hk] at hop
    cases hop
  · obtain ⟨site, i, tt, base, pro⟩ := d
    cases site <;> simp only [Site.isAlloc, Bool.false_eq_true] at ha
    · rw [alloc_site hpre rfl hs h hc hf] at hk
      cases hk
    · rfl

/-- **Only the election sites elect.** -/
theorem notElect_site (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e o) (hs : d.site.isElect = false) :
    isElectE e = false := by
  unfold isElectE
  split
  · rename_i mask inst l hk
    exact absurd hk (fires_notElect (eventTmpl_notElect (electSite_ops.op hs hc)) hf mask inst l)
  · rfl

/-- **Only the exit site exits.** -/
theorem exit_site (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e o) (hk : e.kind = .exit) :
    d.site = .exit := by
  cases hx : d.site.isExit
  · have hop := ret_ops.op hx hc
    rcases fires_exit_op hf hk with h | h <;> rw [h] at hop <;> cases hop
  · obtain ⟨site, i, tt, base, pro⟩ := d
    cases site <;> simp_all [Site.isExit]

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Mma
