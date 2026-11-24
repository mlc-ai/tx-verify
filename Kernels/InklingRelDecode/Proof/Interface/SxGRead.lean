-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.ScRead
public import Kernels.InklingRelDecode.Proof.Interface.SvTrace
public import Kernels.InklingRelDecode.Proof.Interface.ClassCopyPage

@[expose] public section

/-!
# The reads of a tracked thread outside shared memory are input reads

The program's instructions that may read outside shared memory (`nonSharedLoadOp`: a load that
names a space other than shared memory, or a load through a dynamic address) are at the 203
global loads and at the seven shared loads (`kernel_nonShared_load_pcs`, `decide +kernel` over
the decoded program, stated through the machines' site accessors):

* the prologue's three request words (`ProA.Site.ldCu0`, `ldCu1`, `ldSk`), its six block-table
  words (`ProA.lbSite k`) and its 64 query loads (`ProA.ldqSite k`);
* the softmax region's 128 bias loads (`Sm.Site.pre j`, `Sm.Site.nxt j`);
* the loader's two block-table words (`Loader.Site.ldb0`, `ldb1`);
* the seven shared loads of `ScRead.lean`, whose footprints are in shared memory.

`thread_read_input`: a read event outside shared memory of a launched thread is a global read
of input bytes (`Params.reads`). The addresses are the closed forms of the thread layer
(`ProA.shape_cu`, `ProA.lb_addr` with the gate of `ClassCopyPage`, `ProA.ldq_reads`,
`Sm.biasAddr_spec`, `EvW.ldBtAddr_spec` with `LoaderPage`); the guards that skip a load give the
bounds (`tok < qLen`, a block below `num_iters`). The loader's half needs `NumWordRead`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Mbar (wordsSo_all)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The positions of the global loads: the prologue's request words, block-table words and query
loads, the softmax region's bias loads and the loader's block-table words. -/
def globalLoadPcs : List Nat :=
  [ProA.Site.ldCu0.pc, ProA.Site.ldCu1.pc, ProA.Site.ldSk.pc] ++ ProA.lbSites.map ProA.Site.pc ++
    ProA.ldqSites.map ProA.Site.pc ++ (List.finRange 64).map (fun j => (Sm.Site.pre j).pc) ++
    (List.finRange 64).map (fun j => (Sm.Site.nxt j).pc) ++
    [Loader.Site.ldb0.pc, Loader.Site.ldb1.pc]

/-- The positions of the instructions that may read outside shared memory. -/
def nonSharedLoadPcs : List Nat := globalLoadPcs ++ sharedLoadPcs

/-- Instructions that load from a space other than shared memory, or through a dynamic
address. -/
def nonSharedLoadOp (op : Op) : Bool :=
  (loadSpace op != none && loadSpace op != some .shared) || (dynamicAccess op && readOp op)

/-- **The reads of the program outside shared memory are at the positions above.** -/
theorem kernel_nonShared_load_pcs :
    OpPcsFast kernel.code nonSharedLoadOp nonSharedLoadPcs = true := by
  decide +kernel

/-- **A read event outside shared memory is fired at one of those positions.** -/
theorem read_pc_nonShared {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {ins : Instr} {pc : Nat} {e : Event} {o : Option TState} {a : Acc}
    {bs : List (Option Byte)} (hc : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl A L g t ins.op) e o) (hk : e.kind = .rd a bs)
    (hsp : a.loc.space ≠ .shared) : pc ∈ nonSharedLoadPcs := by
  refine OpPcsFast.mem kernel_nonShared_load_pcs hc ?_
  rcases fires_read_loc hf hk with ⟨h, -⟩ | h
  · simp [nonSharedLoadOp, h, hsp]
  · simp [nonSharedLoadOp, h, fires_read_op hf hk]

/-! ### The sites of each machine at those positions -/

theorem pro_pc_gload (s : ProA.Site) (h : s.pc ∈ nonSharedLoadPcs) :
    s ∈ ProA.wordLoadSites ∨ s ∈ ProA.ldqSites := by
  revert h
  cases s
  all_goals first
    | (intro _; decide)
    | (intro h; exfalso; revert h; decide +kernel)

theorem dstart_pc_gload (s : DStart.Site) (h : s.pc ∈ nonSharedLoadPcs) : s = .ld0 := by
  revert h
  cases s
  all_goals first
    | (intro _; rfl)
    | (intro h; exfalso; revert h; decide +kernel)

theorem sm_pc_gload (s : Sm.Site) (h : s.pc ∈ nonSharedLoadPcs) :
    s = .ldL ∨ (∃ j, s = .pre j) ∨ ∃ j, s = .nxt j := by
  revert h
  cases s
  all_goals first
    | (intro _; left; rfl)
    | (intro _; right; left; exact ⟨_, rfl⟩)
    | (intro _; right; right; exact ⟨_, rfl⟩)
    | (intro h; exfalso; revert h; decide +kernel)

theorem epi_pc_notGload (s : Epi.Site) : s.pc ∉ nonSharedLoadPcs := by
  cases s
  all_goals try (rename_i j; revert j)
  all_goals decide +kernel

theorem worker_pc_gload (s : Worker.Site) (h : s.pc ∈ nonSharedLoadPcs) :
    s = .ld0 ∨ s = .ldRole := by
  revert h
  cases s
  all_goals first
    | (intro _; left; rfl)
    | (intro _; right; rfl)
    | (intro h; exfalso; revert h; decide +kernel)

theorem idle_pc_notGload (s : Worker.Idle.Site) : s.pc ∉ nonSharedLoadPcs := by
  cases s
  all_goals decide +kernel

theorem loader_pc_gload (s : Loader.Site) (h : s.pc ∈ nonSharedLoadPcs) :
    s = .ld0 ∨ s = .ld1 ∨ s = .ldb0 ∨ s = .ldb1 := by
  revert h
  cases s
  all_goals first
    | (intro _; left; rfl)
    | (intro _; right; left; rfl)
    | (intro _; right; right; left; rfl)
    | (intro _; right; right; right; rfl)
    | (intro h; exfalso; revert h; decide +kernel)

theorem mma_pc_gload (s : Mma.Site) (h : s.pc ∈ nonSharedLoadPcs) : s = .ldNum := by
  revert h
  cases s
  all_goals try (rename_i j; revert j)
  all_goals first
    | (intro _; rfl)
    | (intro h; exfalso; revert h; decide +kernel)
    | (intro j h; exfalso; revert j h; decide +kernel)

theorem exit_pc_notGload (s : WComp.ExitSite) : s.pc ∉ nonSharedLoadPcs := by
  cases s
  all_goals decide +kernel

/-! ### The input bytes of each global load -/

/-- The conclusion: a global footprint of input bytes. -/
def InputAcc (Q : Params) (a : Acc) : Prop :=
  a.loc.space = .global ∧ a.loc.cta = 0 ∧ ∀ j < a.size, Q.reads (a.loc.addr + j)

theorem ldqSite_of_mem {s : ProA.Site} (h : s ∈ ProA.ldqSites) :
    ∃ k < 64, s = ProA.ldqSite k := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem h
  rw [ProA.ldqSites_length] at hk
  exact ⟨k, hk, by simp [ProA.ldqSite, List.getD_eq_getElem?_getD, hk, ProA.ldqSites_length]⟩

/-- **A word at a global address that does not wrap, of four input bytes.** -/
theorem inputAcc_word {A : Nat} (h : ∀ j < 4, Q.reads (A + j)) :
    InputAcc Q (EvD.wordAcc ⟨.global, 0, A⟩) :=
  ⟨rfl, rfl, fun j hj => h j hj⟩

/-- **The prologue's global loads read input bytes.** -/
theorem pro_read_input (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k pc : Nat} {a : Acc} {bs : List (Option Byte)}
    {d : ProA.D} {u : TState} (hg : g < L.threads)
    (hσ : St Q L X g k = some (some (.d (.pro d))))
    (hF : (threadCode L g Q).toMachine.Fired (some (.d (.pro d))) ⟨pc, .rd a bs⟩ (some u))
    (hs : d.site ∈ ProA.wordLoadSites ∨ d.site ∈ ProA.ldqSites) : InputAcc Q a := by
  have hF' := fired_pro hF
  obtain ⟨t, ins, h, hinv, hc, hfi⟩ := ProA.fired_unpack hF'
  obtain ⟨hx, hy, hz⟩ := ProA.cta_lt hpre hg
  have hb := hpre.bRange
  obtain ⟨sd, dt⟩ := d
  simp only at hs
  rcases hs with hw | hq
  · by_cases hcu : sd = .ldCu0 ∨ sd = .ldCu1 ∨ sd = .ldSk
    · obtain ⟨bs', -, hev⟩ := ProA.shape_cu hpre hg hF' hcu
      simp only [Event.mk.injEq, Kind.rd.injEq] at hev
      obtain ⟨-, rfl, -⟩ := hev
      rcases hcu with rfl | rfl | rfl
      · have hr := hpre.readsRange (Q.cuBase + 4 * ProA.cta L g .z + 3)
          (Mbar.reads_cu (by omega) (by omega))
        simp only [ite_true]
        rw [Nat.mod_eq_of_lt (by omega)]
        exact inputAcc_word fun j hj => Mbar.reads_cu (by omega) hj
      · have hr := hpre.readsRange (Q.cuBase + 4 * (ProA.cta L g .z + 1) + 3)
          (Mbar.reads_cu (by omega) (by omega))
        simp only [reduceCtorEq, ite_false, ite_true]
        rw [Nat.mod_eq_of_lt (by omega)]
        exact inputAcc_word fun j hj => Mbar.reads_cu (by omega) hj
      · have hr := hpre.readsRange (Q.seqBase + 4 * ProA.cta L g .z + 3)
          (Mbar.reads_seq hz (by omega))
        simp only [reduceCtorEq, ite_false]
        rw [Nat.mod_eq_of_lt (by omega)]
        exact inputAcc_word fun j hj => Mbar.reads_seq hz hj
    · have hlb : sd ∈ ProA.lbSites := by
        simp only [ProA.wordLoadSites, List.mem_append, List.mem_cons, List.not_mem_nil,
          or_false] at hw
        rcases hw with (h1 | h1 | h1) | h1
        · exact absurd (.inl h1) hcu
        · exact absurd (.inr (.inl h1)) hcu
        · exact absurd (.inr (.inr h1)) hcu
        · exact h1
      obtain ⟨kk, hk, rfl⟩ := lbSite_of_mem hlb
      obtain ⟨bs', -, hev⟩ := ProA.shape_ld32 hF' hw
      simp only [Event.mk.injEq, Kind.rd.injEq] at hev
      obtain ⟨-, rfl, -⟩ := hev
      -- the gate: the block exists
      obtain ⟨hG, -⟩ := pgSo_all hpre hX hf k _ hσ
      have hj := block_exists hpre hX hf (d := ⟨ProA.lbSite kk, dt⟩) hσ (lbSite_afterSk hk) hG
        (lbSite_blk hk) hg
      obtain ⟨hdef, tm, htm, hpro⟩ := hf.reach hg hσ
      have hspl := hpre.splitsRange
      have hsc := hpre.scalarsRange
      obtain ⟨hI1, hI2⟩ := blk_index hpre hg hj
      have hS : dt.pro.w67 = Q.strideBt := by
        rw [hpro]; exact Nat.mod_eq_of_lt (by omega)
      have hN : dt.pro.w71 = Q.splits := by
        rw [hpro]; exact Nat.mod_eq_of_lt (by omega)
      have hB : dt.pro.btB = Q.btBase := by rw [hpro]; rfl
      have hs2 : 2 * (ProA.cta L g .x + kk / 2 * Q.splits) + kk % 2 <
          2 * Q.blocks (ProA.cta L g .z) := by
        omega
      have hbt' := hpre.btIndexRange _ hz _ hs2
      have hrr0 := hpre.readsRange (Q.btBase + 4 * (ProA.cta L g .z * Q.strideBt +
        (2 * (ProA.cta L g .x + kk / 2 * Q.splits) + kk % 2)) + 3) (reads_bt hz hs2 (by omega))
      have haddr := ProA.lb_addr L g dt hk (by omega)
        (by rw [hS, hN]; rw [Nat.mul_comm] at hbt'; omega) (by rw [hN]; omega)
      rw [hS, hN, hB] at haddr
      have hA : ProA.loadAddr L g dt (ProA.lbSite kk) = Q.btBase + 4 * (ProA.cta L g .z *
          Q.strideBt + (2 * (ProA.cta L g .x + kk / 2 * Q.splits) + kk % 2)) := by
        rw [haddr, Nat.mod_eq_of_lt (by rw [Nat.mul_comm Q.strideBt]; omega)]
        rw [Nat.mul_comm Q.strideBt]
        congr 1
        omega
      rw [hA]
      exact inputAcc_word fun j hj => reads_bt hz hs2 hj
  · obtain ⟨kk, hk, rfl⟩ := ldqSite_of_mem hq
    obtain ⟨bs', -, hev⟩ := ProA.shape_ldq hk hF' rfl
    simp only [Event.mk.injEq, Kind.rd.injEq] at hev
    obtain ⟨-, rfl, -⟩ := hev
    have hG : ProA.guardVal L g dt (ProA.ldqSite kk) = true := hinv.guard
    obtain ⟨h0, h1, h2⟩ := wordsSo_all hpre hX hf k _ hσ
    have hsk : (ProA.ldqSite kk).afterSk = true := ldq_afterSk hk
    have hne : ProA.ldqSite kk ≠ .sMax ∧ ProA.ldqSite kk ≠ .ldCu0 := by
      constructor <;> (intro h'; rw [h'] at hsk; simp [ProA.Site.afterSk] at hsk)
    have hm : ProA.WordsMatch Q (ProA.cta L g .z) dt :=
      ⟨h0 hne.1 hne.2, h1 (Or.inl hsk), h2 hsk⟩
    exact ⟨rfl, rfl, fun j hj => ProA.ldq_reads hpre hg hinv.args hm hk hG j hj⟩

/-- **The softmax region's bias loads read input bytes.** -/
theorem sm_read_input (hpre : Pre Q L mem0)
    (hf : ThreadFacts Q L mem0 X) {g k pc : Nat} {a : Acc} {bs : List (Option Byte)}
    {d : Sm.D} {u : TState} (hg : g < L.threads)
    (hσ : St Q L X g k = some (some (.d (.sm d))))
    (hF : (threadCode L g Q).toMachine.Fired (some (.d (.sm d))) ⟨pc, .rd a bs⟩ (some u))
    (hs : (∃ j, d.site = .pre j) ∨ ∃ j, d.site = .nxt j) : InputAcc Q a := by
  obtain ⟨-, hm⟩ := hf.reach hg hσ
  obtain ⟨hx, hy, hz⟩ := ProA.cta_lt hpre hg
  have hI : Sm.Inv L g d := by
    obtain ⟨t, ⟨-, hi⟩, -⟩ := hF
    exact hi.2
  rcases hs with ⟨j, hs⟩ | ⟨j, hs⟩
  · obtain ⟨bs', hl, hev⟩ := Sm.shape_pre_spec hpre hm.ent hz hy (fired_sm hF) hs
    obtain ⟨hn, hrv, hit, hnb⟩ := Sm.pre_block hm.ent hI hs
    have hbl : ProA.cta L g .x < Q.blocks (ProA.cta L g .z) := by
      have := Sm.lt_blocks_of_iters (r := ProA.cta L g .z) (s := ProA.cta L g .x) (i := 0)
        hpre.splitsPos hit
      simpa using this
    obtain ⟨htok, hh, hc, -⟩ := Sm.biasAddr_spec hpre hm.ent hz hy hI.tid hrv j.isLt hbl hnb
    simp only [Event.mk.injEq, Kind.rd.injEq] at hev
    obtain ⟨-, rfl, -⟩ := hev
    refine ⟨rfl, rfl, fun b hb => ?_⟩
    exact Or.inr (Or.inl ⟨_, hz, _, htok, _, hh, _, hc, b, hb, by simp [Sm.relAddr]⟩)
  · obtain ⟨bs', hl, hev⟩ := Sm.shape_nxt_spec hpre hm.ent hz hy (fired_sm hF) hs
    obtain ⟨hn, hrv, hit, hnb⟩ := Sm.nxt_block hm.ent hI hs
    have hbl := Sm.lt_blocks_of_iters hpre.splitsPos hit
    obtain ⟨htok, hh, hc, -⟩ := Sm.biasAddr_spec hpre hm.ent hz hy hI.tid hrv j.isLt hbl hnb
    simp only [Event.mk.injEq, Kind.rd.injEq] at hev
    obtain ⟨-, rfl, -⟩ := hev
    refine ⟨rfl, rfl, fun b hb => ?_⟩
    exact Or.inr (Or.inl ⟨_, hz, _, htok, _, hh, _, hc, b, hb, by simp [Sm.relAddr]⟩)

/-- **The loader's block-table loads read input bytes**, given `NumWordRead`. -/
theorem loader_read_input (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hn : NumWordRead Q L X) {g k pc : Nat} {a : Acc}
    {bs : List (Option Byte)} {d : Loader.D} {P : Loader.Pro} {u : TState} (hg : g < L.threads)
    (hσ : St Q L X g k = some (some (.w (.loader d P))))
    (hF : (threadCode L g Q).toMachine.Fired (some (.w (.loader d P))) ⟨pc, .rd a bs⟩ (some u))
    {slab : Nat}
    (hs : (slab = 0 ∧ d.site = .ldb0) ∨ (slab = 1 ∧ d.site = .ldb1)) : InputAcc Q a := by
  obtain ⟨t, hgd, hfire⟩ := hF
  have hinv := hgd.2
  have hr := hf.reach hg hσ
  have hinv' : Loader.Inv L g d ∧ Loader.ProEq L g P d ∧ Worker.Rest L g P ∧
      4 ≤ WComp.warpOf L g ∧ g % L.block < 256 := hinv.2
  have hsh := EvW.loader_shape hpre hr.2 (hf.ldRng hg hσ) (g := g) (d := d) (P := P) (u := u)
    ⟨t, ⟨hgd.1, hgd.2.2⟩, hfire⟩
  have hm : EvW.Words Q P := hr.1
  have hlp : LoaderPage Q L g d := page_inv hpre hX hf hn k _ hσ
  have hsite : d.site = .ldb0 ∨ d.site = .ldb1 := by
    rcases hs with ⟨-, h⟩ | ⟨-, h⟩
    · exact .inl h
    · exact .inr h
  have hnN := hlp.1 (by rcases hsite with h | h <;> rw [h] <;> rfl)
  have hi : d.i < Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) := by
    rw [← hnN]; exact (hf.ldRng hg hσ).loop (by rcases hsite with h | h <;> rw [h] <;> rfl)
  obtain ⟨hx, hy, hz⟩ := ProA.cta_lt hpre hg
  have hblk := Result.Mma.blk_lt hpre.splitsPos hi
  have hsb := hpre.seqRange _ hz
  have hbl : Q.blocks (ProA.cta L g .z) < 2 ^ 24 := by
    unfold Params.blocks; omega
  have hsl : slab ≤ 1 := by omega
  have hi31 : d.i < 2 ^ 31 :=
    (hf.ldRng hg hσ).bndI (by rcases hsite with h | h <;> rw [h] <;> rfl)
  have hidx : ProA.cta L g .z * Q.strideBt + (2 * (ProA.cta L g .x + d.i * Q.splits) + slab) <
      2 ^ 31 := hpre.btIndexRange _ hz _ (by omega)
  have haddr := EvW.ldBtAddr_spec hpre hg hm hinv'.2.1 slab hsl (by omega) (by omega)
  have hsr : 2 * (ProA.cta L g .x + d.i * Q.splits) + slab < 2 * Q.blocks (ProA.cta L g .z) := by
    omega
  have hrd : ∀ j < 4, Q.reads (Q.btBase + 4 * (ProA.cta L g .z * Q.strideBt +
      (2 * (ProA.cta L g .x + d.i * Q.splits) + slab)) + j) :=
    fun j hj => reads_bt hz hsr hj
  have hnw := hpre.readsRange _ (hrd 3 (by omega))
  have hsh' : ∃ ac bs', (⟨pc, .rd a bs⟩ : Event) = ⟨d.site.pc, .rd ac bs'⟩ ∧
      ac.loc = ⟨.global, 0, EvW.ldBtAddr L g d slab⟩ ∧ ac.size = 4 := by
    unfold EvW.LdShape at hsh
    rcases hs with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> rw [h] at hsh <;> rw [h] <;> exact hsh
  obtain ⟨ac, bs', he2, hloc, hsz⟩ := hsh'
  simp only [Event.mk.injEq, Kind.rd.injEq] at he2
  obtain ⟨-, rfl, -⟩ := he2
  unfold InputAcc
  rw [hloc, haddr, Nat.mod_eq_of_lt (by omega)]
  refine ⟨rfl, rfl, fun j hj => ?_⟩
  rw [hsz] at hj
  dsimp only
  convert hrd j hj using 2
  omega

/-! ### The classification -/

theorem shared_absurd {a : Acc} {c x : Nat} (hl : a.loc = ⟨.shared, c, x⟩)
    (hsp : a.loc.space ≠ .shared) : False := by
  rw [hl] at hsp
  exact hsp rfl

/-- **A read outside shared memory fired from a state of a launched thread's machine reads input
bytes**: it is a global read whose bytes are in `Params.reads`. The state is the machine's
state before the thread's `k`-th event; the read need not be an event of the execution. -/
theorem fired_read_input (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hn : NumWordRead Q L X) {g k pc : Nat} {a : Acc}
    {bs : List (Option Byte)} {s : TSt} {u : TState} (hg : g < L.threads)
    (hσ : St Q L X g k = some (some s))
    (hFs : (threadCode L g Q).toMachine.Fired (some s) ⟨pc, .rd a bs⟩ (some u))
    (hsp : a.loc.space ≠ .shared) : InputAcc Q a := by
  have hk : (⟨pc, .rd a bs⟩ : Event).kind = .rd a bs := rfl
  obtain ⟨t, ins, hat, hinv, hc, hfi⟩ := Frame.fired_site_of hf.sound hg hFs
  have hpw : TSt.pc s ∈ nonSharedLoadPcs := read_pc_nonShared hc hfi hk hsp
  have hSh := ProA.sharedOk_of_pre hpre
  cases s with
  | w s =>
    cases s with
    | worker w =>
      obtain ⟨site, P⟩ := w
      have hF := hFs
      obtain ⟨t', hgd, hfire⟩ := hF
      have hF' : (WComp.code L g Q).toMachine.Fired (some (.worker ⟨site, P⟩)) ⟨pc, .rd a bs⟩
          (some u) := ⟨t', ⟨hgd.1, hgd.2.2⟩, hfire⟩
      exfalso
      rcases worker_pc_gload site hpw with hs | hs
      · subst hs
        obtain ⟨pc', ac, bs', he2, hl, -⟩ := worker_ld0_shape hpre (g := g)
          (w := ⟨.ld0, P⟩) rfl hF'
        simp only [Event.mk.injEq, Kind.rd.injEq] at he2
        obtain ⟨-, rfl, -⟩ := he2
        exact shared_absurd hl hsp
      · subst hs
        have hg256 : g % L.block < 256 := by
          rw [hpre.block]
          exact Nat.mod_lt _ (by omega)
        obtain ⟨ac, bs', he2, hl, -⟩ := Worker.shape_ldRole hpre (w := ⟨.ldRole, P⟩) hg256 rfl
          hF'
        simp only [Event.mk.injEq, Kind.rd.injEq] at he2
        obtain ⟨-, rfl, -⟩ := he2
        exact shared_absurd hl hsp
    | idle d => exact absurd hpw (idle_pc_notGload d.site)
    | loader d P =>
      rcases loader_pc_gload d.site hpw with hs | hs | hs | hs
      · exfalso
        have hF := hFs
        obtain ⟨t', hgd, hfire⟩ := hF
        have hsh := EvW.loader_shape hpre (hf.reach hg hσ).2
          (hf.ldRng hg hσ) (g := g) (d := d) (P := P) (u := u)
          ⟨t', ⟨hgd.1, hgd.2.2⟩, hfire⟩
        unfold EvW.LdShape at hsh
        rw [hs] at hsh
        obtain ⟨ac, bs', he2, hl, -⟩ := hsh
        simp only [Event.mk.injEq, Kind.rd.injEq] at he2
        obtain ⟨-, rfl, -⟩ := he2
        exact shared_absurd hl hsp
      · exfalso
        have hF := hFs
        obtain ⟨t', hgd, hfire⟩ := hF
        have hsh := EvW.loader_shape hpre (hf.reach hg hσ).2
          (hf.ldRng hg hσ) (g := g) (d := d) (P := P) (u := u)
          ⟨t', ⟨hgd.1, hgd.2.2⟩, hfire⟩
        unfold EvW.LdShape at hsh
        rw [hs] at hsh
        obtain ⟨ac, bs', he2, hl, -⟩ := hsh
        simp only [Event.mk.injEq, Kind.rd.injEq] at he2
        obtain ⟨-, rfl, -⟩ := he2
        exact shared_absurd hl hsp
      · exact loader_read_input hpre hX hf hn hg hσ hFs (slab := 0) (.inl ⟨rfl, hs⟩)
      · exact loader_read_input hpre hX hf hn hg hσ hFs (slab := 1) (.inr ⟨rfl, hs⟩)
    | mma d P =>
      exfalso
      have hF := hFs
      obtain ⟨t', hgd, hfire⟩ := hF
      have hF' : (WComp.code L g Q).toMachine.Fired (some (.mma d P)) ⟨pc, .rd a bs⟩
          (some u) := ⟨t', ⟨hgd.1, hgd.2.2⟩, hfire⟩
      have hsh := EvW.mma_shape hpre hg (d := d) (P := P) hF'
      unfold EvW.MmShape at hsh
      rw [mma_pc_gload d.site hpw] at hsh
      obtain ⟨ac, bs', he2, hl, -⟩ := hsh
      simp only [Event.mk.injEq, Kind.rd.injEq] at he2
      obtain ⟨-, rfl, -⟩ := he2
      exact shared_absurd hl hsp
    | exit x => exact absurd hpw (exit_pc_notGload x.site)
  | d s =>
    cases s with
    | dstart d =>
      exfalso
      have hF := hFs
      obtain ⟨ac, bs', he2, hl, -⟩ :=
        DStart.shape_ld0 hSh (fired_dstart hF) (dstart_pc_gload d.site hpw)
      simp only [Event.mk.injEq, Kind.rd.injEq] at he2
      obtain ⟨-, rfl, -⟩ := he2
      exact shared_absurd hl hsp
    | pro d => exact pro_read_input hpre hX hf hg hσ hFs (pro_pc_gload d.site hpw)
    | sm d =>
      rcases sm_pc_gload d.site hpw with hs | hs
      · exfalso
        have hF := hFs
        obtain ⟨ac, bs', he2, hl, -⟩ := Sm.shape_ldL_foot hSh (fired_sm hF) hs
        simp only [Event.mk.injEq, Kind.rd.injEq] at he2
        obtain ⟨-, rfl, -⟩ := he2
        exact shared_absurd hl hsp
      · exact sm_read_input hpre hf hg hσ hFs hs
    | epi d => exact absurd hpw (epi_pc_notGload d.site)

/-- **A read event outside shared memory of a launched thread reads input bytes**: it is a
global read whose bytes are in `Params.reads`. -/
theorem thread_read_input (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hn : NumWordRead Q L X) {g k pc : Nat} {a : Acc}
    {bs : List (Option Byte)} (hg : g < L.threads) (he : X.get (g, k) = some ⟨pc, .rd a bs⟩)
    (hsp : a.loc.space ≠ .shared) : InputAcc Q a := by
  obtain ⟨s, hσ⟩ := Frame.event_state hf.sound hX hf.tracked he (by intro pc f h; cases h)
  by_cases hx : ExitState s
  · exfalso
    obtain ⟨t, ins, o, -, -, hc, hfi⟩ := Frame.fired_site hf.sound hX he hσ
    have hpw : TSt.pc s ∈ nonSharedLoadPcs := read_pc_nonShared hc hfi rfl hsp
    cases s with
    | d s =>
      cases s with
      | epi d => exact epi_pc_notGload d.site hpw
      | _ => exact hx
    | w s =>
      cases s with
      | exit x => exact exit_pc_notGload x.site hpw
      | _ => exact hx
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ hx
  exact fired_read_input hpre hX hf hn hg hσ hF hsp

/-! ### The writes outside shared memory -/

/-- Instructions that store to a space other than shared memory, or through a dynamic address. -/
def nonSharedStoreOp (op : Op) : Bool :=
  (storeSpace op != none && storeSpace op != some .shared) || (dynamicAccess op && writeOp op)

/-- **The writes of the program outside shared memory are at the write positions**
(`writePcs`, `Writes.lean`). -/
theorem kernel_nonShared_store_pcs : OpPcsFast kernel.code nonSharedStoreOp writePcs = true := by
  decide +kernel

/-- **A write event outside shared memory is fired at a write position.** -/
theorem write_pc_nonShared {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {ins : Instr} {pc : Nat} {e : Event} {o : Option TState} {a : Acc} {bs : List Byte}
    (hc : kernel.code[pc]? = some ins) (hf : Fires pc (eventTmpl A L g t ins.op) e o)
    (hk : e.kind = .wr a bs) (hsp : a.loc.space ≠ .shared) : pc ∈ writePcs := by
  refine OpPcsFast.mem kernel_nonShared_store_pcs hc ?_
  have hw := fires_write_op hf hk
  rcases fires_write_space hf hk with h | h
  · simp [nonSharedStoreOp, h, hsp]
  · simp [nonSharedStoreOp, h, hw]

/-- **A write event of a launched thread outside shared memory is a global write**: the only
writes at the write positions outside shared memory are the epilogue's output stores. -/
theorem thread_write_global (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k pc : Nat} {a : Acc} {bs : List Byte}
    (hg : g < L.threads) (he : X.get (g, k) = some ⟨pc, .wr a bs⟩)
    (hsp : a.loc.space ≠ .shared) : a.loc.space = .global := by
  have hk : (⟨pc, .wr a bs⟩ : Event).kind = .wr a bs := rfl
  obtain ⟨s, hσ⟩ := Frame.event_state hf.sound hX hf.tracked he (by intro pc f h; cases h)
  obtain ⟨t, ins, o, hat, hinv, hc, hfi⟩ := Frame.fired_site hf.sound hX he hσ
  have hpw : TSt.pc s ∈ writePcs := write_pc_nonShared hc hfi hk hsp
  have he' : (X.tr g)[k]? = some ⟨pc, .wr a bs⟩ := he
  obtain ⟨o', hF⟩ := (Frame.trace hf.sound hX hg).fired_at he' hσ
  obtain ⟨u, rfl⟩ := fired_some hF hk
  have hr := hf.reach hg hσ
  rcases write_state hpw with ⟨d, rfl, hsite⟩ | ⟨d, rfl, hsite⟩
  · have hFe := fired_epi hF
    have hm : Epi.Means Q L g d.pr := hr.2
    rcases hsite with hs | hs | ⟨j, hs⟩
    · obtain ⟨v, hv, he2⟩ := Epi.shape_stLse_loc hpre hg hm hFe hs
      simp only [Event.mk.injEq, Kind.wr.injEq] at he2
      obtain ⟨-, h2, -⟩ := he2
      rw [h2]
      rfl
    · obtain ⟨v, hv, he2⟩ := Epi.shape_stTab hFe hs
      simp only [Event.mk.injEq, Kind.wr.injEq] at he2
      obtain ⟨-, h2, -⟩ := he2
      rw [h2] at hsp
      exact absurd rfl hsp
    · obtain ⟨v, hv, he2⟩ := Epi.shape_stO_loc hpre hg hm hFe hs
      simp only [Event.mk.injEq, Kind.wr.injEq] at he2
      obtain ⟨-, h2, -⟩ := he2
      rw [h2]
      rfl
  · have hFp := fired_pro hF
    exfalso
    rcases hsite with hs | hs | hs
    · obtain ⟨v, hv, he2⟩ := ProA.shape_st8 hFp hs
      simp only [Event.mk.injEq, Kind.wr.injEq] at he2
      obtain ⟨-, h2, -⟩ := he2
      rw [h2] at hsp
      exact hsp rfl
    · obtain ⟨v, hv, he2⟩ := ProA.shape_st9_0 hFp hs
      simp only [Event.mk.injEq, Kind.wr.injEq] at he2
      obtain ⟨-, h2, -⟩ := he2
      rw [h2] at hsp
      exact hsp rfl
    · obtain ⟨v, hv, he2⟩ := ProA.shape_st9_1 hFp hs
      simp only [Event.mk.injEq, Kind.wr.injEq] at he2
      obtain ⟨-, h2, -⟩ := he2
      rw [h2] at hsp
      exact hsp rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
