-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.Box
public import Kernels.InklingRelDecode.Proof.Thread.ClassQAddr

@[expose] public section

/-! # The global reads on the role table

`global_reads : Safety.GlobalReads Q X`: every byte outside shared memory that an access reads is
an input byte. A thread's read outside shared memory is at a global load position
(`kernel_gload_pcs`, decided on the code): the prologue's request words, block-table words and
query loads (`pro_read_input`, from the prologue's reference: its parameter words, request words
and gate), the softmax region's bias loads (`sm_read_input`, from the entry numbers' meaning) or
the loader's block-table loads (`ld_read_input`, from `ld_page`, `ww_inv`, `ld_rng`). A tensor
copy's source bytes are input bytes of its slab (`copy_form`, `kvCopy_readLoc_input`). -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame
open PTX.Kernels.InklingRelDecode.Proof.Interface (LoaderPage)
open PTX.Kernels.InklingRelDecode.Proof.Safety (InInput GlobalReads)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-! ### The positions of the loads outside shared memory -/

/-- The global load positions and the shared ones. -/
def gloadPcs : List Nat :=
  [Proof.ProA.Site.ldCu0.pc, Proof.ProA.Site.ldCu1.pc, Proof.ProA.Site.ldSk.pc] ++
    Proof.ProA.lbSites.map Proof.ProA.Site.pc ++ Proof.ProA.ldqSites.map Proof.ProA.Site.pc ++
    (List.finRange 64).map (fun j => (Proof.Sm.Site.pre j).pc) ++
    (List.finRange 64).map (fun j => (Proof.Sm.Site.nxt j).pc) ++
    [Proof.Loader.Site.ldb0.pc, Proof.Loader.Site.ldb1.pc] ++ rdPcs

/-- Instructions that load from a space other than shared memory, or through a dynamic
address. -/
def gloadOp (op : Op) : Bool :=
  (loadSpace op != none && loadSpace op != some .shared) || (dynamicAccess op && readOp op)

theorem kernel_gload_pcs : OpPcsFast kernel.code gloadOp gloadPcs = true := by decide +kernel

theorem gload_pc {t : TState} {ins : Instr} {pc : Nat} {e : Event} {o : Option TState} {a : Acc}
    {bs : List (Option Byte)} (hc : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o) (hk : e.kind = .rd a bs)
    (hsp : a.loc.space ≠ .shared) : pc ∈ gloadPcs := by
  refine OpPcsFast.mem kernel_gload_pcs hc ?_
  rcases fires_read_loc hf hk with ⟨h, -⟩ | h
  · simp [gloadOp, h, hsp]
  · simp [gloadOp, h, fires_read_op hf hk]

local macro "site_none" : tactic =>
  `(tactic| (intro s h; revert h; cases s <;> (try (rename_i j; revert j)) <;> decide +kernel))

theorem startup_gl : ∀ s : Startup.Site, s.pc ∈ gloadPcs → s = .ld0 := by
  intro s h; revert h
  cases s with
  | ld0 => intro _; rfl
  | enter r => cases r <;> decide
  | _ => decide

theorem pro_gl (s : Proof.ProA.Site) (h : s.pc ∈ gloadPcs) :
    s ∈ Proof.ProA.wordLoadSites ∨ s ∈ Proof.ProA.ldqSites := by
  revert h
  cases s
  all_goals first
    | (intro _; decide)
    | (intro h; exfalso; revert h; decide +kernel)

theorem sm_gl (s : Proof.Sm.Site) (h : s.pc ∈ gloadPcs) :
    s = .ldL ∨ (∃ j, s = .pre j) ∨ ∃ j, s = .nxt j := by
  revert h
  cases s
  all_goals first
    | (intro _; left; rfl)
    | (intro _; right; left; exact ⟨_, rfl⟩)
    | (intro _; right; right; exact ⟨_, rfl⟩)
    | (intro h; exfalso; revert h; decide +kernel)

theorem epi_gl : ∀ s : Proof.Epi.Site, s.pc ∈ gloadPcs → False := by site_none
theorem idle_gl : ∀ s : Proof.Worker.Idle.Site, s.pc ∈ gloadPcs → False := by site_none
theorem exitsite_gl : ∀ s : Proof.WComp.ExitSite, s.pc ∈ gloadPcs → False := by site_none

theorem worker_gl (s : Proof.Worker.Site) (h : s.pc ∈ gloadPcs) : s = .ld0 ∨ s = .ldRole := by
  revert h
  cases s
  all_goals first
    | (intro _; left; rfl)
    | (intro _; right; rfl)
    | (intro h; exfalso; revert h; decide +kernel)

theorem loader_gl (s : Proof.Loader.Site) (h : s.pc ∈ gloadPcs) :
    s = .ld0 ∨ s = .ld1 ∨ s = .ldb0 ∨ s = .ldb1 := by
  revert h
  cases s
  all_goals first
    | (intro _; left; rfl)
    | (intro _; right; left; rfl)
    | (intro _; right; right; left; rfl)
    | (intro _; right; right; right; rfl)
    | (intro h; exfalso; revert h; decide +kernel)

theorem mma_gl (s : Proof.Mma.Site) (h : s.pc ∈ gloadPcs) : s = .ldNum := by
  revert h
  cases s
  all_goals try (rename_i j; revert j)
  all_goals first
    | (intro _; rfl)
    | (intro h; exfalso; revert h; decide +kernel)
    | (intro j h; exfalso; revert j h; decide +kernel)

/-! ### The input bytes of each global load -/

/-- A global footprint of input bytes. -/
def InputAcc (Q : Params) (a : Acc) : Prop :=
  a.loc.space = .global ∧ a.loc.cta = 0 ∧ ∀ j < a.size, Q.reads (a.loc.addr + j)

theorem inputAcc_word {A : Nat} (h : ∀ j < 4, Q.reads (A + j)) :
    InputAcc Q (Proof.EvD.wordAcc ⟨.global, 0, A⟩) :=
  ⟨rfl, rfl, fun j hj => h j hj⟩

theorem ldqSite_of_mem {s : Proof.ProA.Site} (h : s ∈ Proof.ProA.ldqSites) :
    ∃ k < 64, s = Proof.ProA.ldqSite k := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem h
  rw [Proof.ProA.ldqSites_length] at hk
  exact ⟨k, hk, by simp [Proof.ProA.ldqSite, List.getD_eq_getElem?_getD, hk,
    Proof.ProA.ldqSites_length]⟩

theorem lbSite_blk {k : Nat} (hk : k < 6) :
    Proof.ProA.lbSite k ∈ Proof.ProA.blkSites (k / 2) := by
  interval_cases k <;> decide

/-- **The prologue's global loads read input bytes.** -/
theorem pro_read_input (hp : Pre Q L m) (hg : g < L.threads) {tm : Nat} {bw : Value}
    {d : ProA.D} {pc : Nat} {a : Acc} {bs : List (Option Byte)} {u : TState}
    (hR : ProA.PRef Q L g tm bw d) (hF : Proof.ProA.Fired L g d.old ⟨pc, .rd a bs⟩ (some u))
    (hs : d.site.old ∈ Proof.ProA.wordLoadSites ∨ d.site.old ∈ Proof.ProA.ldqSites) :
    InputAcc Q a := by
  obtain ⟨t, ins, h, hinv, hc, hfi⟩ := Proof.ProA.fired_unpack hF
  obtain ⟨hx, hy, hz⟩ := Proof.ProA.cta_lt hp hg
  have hb := hp.bRange
  have ha : Proof.ProA.ArgsOk L g d.dt.pro := hinv.args
  have hspl := hp.splitsRange
  have hsc := hp.scalarsRange
  have hN : d.dt.pro.w71 = Q.splits := by rw [hR.pro]; exact Nat.mod_eq_of_lt (by omega)
  have hS : d.dt.pro.w67 = Q.strideBt := by rw [hR.pro]; exact Nat.mod_eq_of_lt (by omega)
  have hB : d.dt.pro.btB = Q.btBase := by rw [hR.pro]; rfl
  obtain ⟨w0, w1, w2⟩ := hR.words
  have hG := hR.gate
  have hgv := hinv.guard
  obtain ⟨site, dt⟩ := d
  simp only [ProA.D.old] at w0 w1 w2 hG hN hS hB ha hgv hs
  change Proof.ProA.Fired L g ⟨site.old, dt⟩ _ _ at hF
  generalize site.old = sd at hs w0 w1 w2 hG hF hgv
  rcases hs with hw | hq
  · by_cases hcu : sd = .ldCu0 ∨ sd = .ldCu1 ∨ sd = .ldSk
    · obtain ⟨bs', -, hev⟩ := Proof.ProA.shape_cu hp hg hF hcu
      simp only [Event.mk.injEq, Kind.rd.injEq] at hev
      obtain ⟨-, rfl, -⟩ := hev
      rcases hcu with rfl | rfl | rfl
      · have hr := hp.readsRange (Q.cuBase + 4 * Proof.ProA.cta L g .z + 3)
          (.inr (.inr (.inr (.inl ⟨_, hz.le, 3, by omega, rfl⟩))))
        simp only [ite_true]
        rw [Nat.mod_eq_of_lt (by omega)]
        exact inputAcc_word fun j hj => .inr (.inr (.inr (.inl ⟨_, hz.le, j, hj, rfl⟩)))
      · have hr := hp.readsRange (Q.cuBase + 4 * (Proof.ProA.cta L g .z + 1) + 3)
          (.inr (.inr (.inr (.inl ⟨_, hz, 3, by omega, rfl⟩))))
        simp only [reduceCtorEq, ite_false, ite_true]
        rw [Nat.mod_eq_of_lt (by omega)]
        exact inputAcc_word fun j hj => .inr (.inr (.inr (.inl ⟨_, hz, j, hj, rfl⟩)))
      · have hr := hp.readsRange (Q.seqBase + 4 * Proof.ProA.cta L g .z + 3)
          (.inr (.inr (.inr (.inr (.inl ⟨_, hz, 3, by omega, rfl⟩)))))
        simp only [reduceCtorEq, ite_false]
        rw [Nat.mod_eq_of_lt (by omega)]
        exact inputAcc_word fun j hj => .inr (.inr (.inr (.inr (.inl ⟨_, hz, j, hj, rfl⟩))))
    · have hlb : sd ∈ Proof.ProA.lbSites := by
        simp only [Proof.ProA.wordLoadSites, List.mem_append, List.mem_cons, List.not_mem_nil,
          or_false] at hw
        rcases hw with (h1 | h1 | h1) | h1
        · exact absurd (.inl h1) hcu
        · exact absurd (.inr (.inl h1)) hcu
        · exact absurd (.inr (.inr h1)) hcu
        · exact h1
      obtain ⟨kk, hk, rfl⟩ := lbSite_of_mem hlb
      obtain ⟨bs', -, hev⟩ := Proof.ProA.shape_ld32 hF hw
      simp only [Event.mk.injEq, Kind.rd.injEq] at hev
      obtain ⟨-, rfl, -⟩ := hev
      have hafter : (Proof.ProA.lbSite kk).afterSk = true := by interval_cases kk <;> decide
      have hne : Proof.ProA.lbSite kk ≠ .sMax ∧ Proof.ProA.lbSite kk ≠ .ldCu0 := by
        constructor <;> (intro h; rw [h] at hafter; simp [Proof.ProA.Site.afterSk] at hafter)
      have hm : Proof.ProA.WordsMatch Q (Proof.ProA.cta L g .z) dt :=
        ⟨w0 hne.1 hne.2, w1 (.inl hafter), w2 hafter⟩
      obtain ⟨c0, c1, c2⟩ := Proof.ProA.gate_iters hp hg ha hN hm
      obtain ⟨g0, g1, g2⟩ := hG
      have hblk := lbSite_blk hk
      have hj : kk / 2 < Q.numIters (Proof.ProA.cta L g .z) (Proof.ProA.cta L g .x) := by
        rcases (by omega : kk / 2 = 0 ∨ kk / 2 = 1 ∨ kk / 2 = 2) with h | h | h <;>
          rw [h] at hblk ⊢
        · exact c0 (g0 hblk)
        · exact c1 (g1 hblk).1 (g1 hblk).2
        · exact c2 (g2 hblk).1 (g2 hblk).2.1 (g2 hblk).2.2
      obtain ⟨hI1, hI2⟩ := blk_index hp hg hj
      have hs2 : 2 * (Proof.ProA.cta L g .x + kk / 2 * Q.splits) + kk % 2 <
          2 * Q.blocks (Proof.ProA.cta L g .z) := by omega
      have hbt' := hp.btIndexRange _ hz _ hs2
      have hrd : ∀ j < 4, Q.reads (Q.btBase + 4 * (Proof.ProA.cta L g .z * Q.strideBt +
          (2 * (Proof.ProA.cta L g .x + kk / 2 * Q.splits) + kk % 2)) + j) := fun j hj =>
        .inr (.inr (.inr (.inr (.inr ⟨_, hz, _, hs2, j, hj, rfl⟩))))
      have hrr0 := hp.readsRange _ (hrd 3 (by omega))
      have haddr := Proof.ProA.lb_addr L g dt hk (by omega)
        (by rw [hS, hN]; rw [Nat.mul_comm] at hbt'; omega) (by rw [hN]; omega)
      rw [hS, hN, hB] at haddr
      have hA : Proof.ProA.loadAddr L g dt (Proof.ProA.lbSite kk) = Q.btBase +
          4 * (Proof.ProA.cta L g .z * Q.strideBt +
            (2 * (Proof.ProA.cta L g .x + kk / 2 * Q.splits) + kk % 2)) := by
        rw [haddr, Nat.mod_eq_of_lt (by rw [Nat.mul_comm Q.strideBt]; omega)]
        rw [Nat.mul_comm Q.strideBt]
        congr 1
        omega
      rw [hA]
      exact inputAcc_word hrd
  · obtain ⟨kk, hk, rfl⟩ := ldqSite_of_mem hq
    obtain ⟨bs', -, hev⟩ := Proof.ProA.shape_ldq hk hF rfl
    simp only [Event.mk.injEq, Kind.rd.injEq] at hev
    obtain ⟨-, rfl, -⟩ := hev
    have hGv : Proof.ProA.guardVal L g dt (Proof.ProA.ldqSite kk) = true := hgv
    have hsk : (Proof.ProA.ldqSite kk).afterSk = true := by interval_cases kk <;> rfl
    have hne : Proof.ProA.ldqSite kk ≠ .sMax ∧ Proof.ProA.ldqSite kk ≠ .ldCu0 := by
      constructor <;> (intro h'; rw [h'] at hsk; simp [Proof.ProA.Site.afterSk] at hsk)
    have hm : Proof.ProA.WordsMatch Q (Proof.ProA.cta L g .z) dt :=
      ⟨w0 hne.1 hne.2, w1 (.inl hsk), w2 hsk⟩
    exact ⟨rfl, rfl, fun j hj => Proof.ProA.ldq_reads hp hg ha hm hk hGv j hj⟩


/-- **The softmax region's bias loads read input bytes.** -/
theorem sm_read_input (hp : Pre Q L m) (hg : g < L.threads) {d : Proof.Sm.D}
    {u : TState} {pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (hm : SmRef Q L g d) (hI : Proof.Sm.Inv L g d)
    (hF : Proof.Sm.Fired L g d ⟨pc, .rd a bs⟩ (some u))
    (hs : (∃ j, d.site = .pre j) ∨ ∃ j, d.site = .nxt j) : InputAcc Q a := by
  obtain ⟨hx, hy, hz⟩ := Proof.ProA.cta_lt hp hg
  rcases hs with ⟨j, hs⟩ | ⟨j, hs⟩
  · obtain ⟨bs', hl, hev⟩ := Proof.Sm.shape_pre_spec hp hm hz hy hF hs
    obtain ⟨hn, hrv, hit, hnb⟩ := Proof.Sm.pre_block hm hI hs
    have hbl : Proof.ProA.cta L g .x < Q.blocks (Proof.ProA.cta L g .z) := by
      have := Proof.Sm.lt_blocks_of_iters (r := Proof.ProA.cta L g .z)
        (s := Proof.ProA.cta L g .x) (i := 0) hp.splitsPos hit
      simpa using this
    obtain ⟨htok, hh, hc, -⟩ := Proof.Sm.biasAddr_spec hp hm hz hy hI.tid hrv j.isLt hbl hnb
    simp only [Event.mk.injEq, Kind.rd.injEq] at hev
    obtain ⟨-, rfl, -⟩ := hev
    refine ⟨rfl, rfl, fun b hb => ?_⟩
    exact Or.inr (Or.inl ⟨_, hz, _, htok, _, hh, _, hc, b, hb, by simp [Proof.Sm.relAddr]⟩)
  · obtain ⟨bs', hl, hev⟩ := Proof.Sm.shape_nxt_spec hp hm hz hy hF hs
    obtain ⟨hn, hrv, hit, hnb⟩ := Proof.Sm.nxt_block hm hI hs
    have hbl := Proof.Sm.lt_blocks_of_iters hp.splitsPos hit
    obtain ⟨htok, hh, hc, -⟩ := Proof.Sm.biasAddr_spec hp hm hz hy hI.tid hrv j.isLt hbl hnb
    simp only [Event.mk.injEq, Kind.rd.injEq] at hev
    obtain ⟨-, rfl, -⟩ := hev
    refine ⟨rfl, rfl, fun b hb => ?_⟩
    exact Or.inr (Or.inl ⟨_, hz, _, htok, _, hh, _, hc, b, hb, by simp [Proof.Sm.relAddr]⟩)

/-- **The loader's block-table loads read input bytes.** -/
theorem ld_read_input (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨pc, .rd a bs⟩) {tm : Value} {d : Proof.Loader.D}
    {P : Proof.Loader.Pro} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.worker tm), .loader d P⟩, n)))
    (hs : d.site = .ldb0 ∨ d.site = .ldb1) : InputAcc Q a := by
  have hg := Frame.lt_of_get hX he
  have hlen : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ :=
    Frame.fired_site (fun g hg => thread_sound hp hg) hX he hσ
  have hpro : Proof.Loader.ProEq L g P d := (hinv : Proof.WComp.Inv L g (.loader d P)).2.1
  have hm : Proof.EvW.Words Q P := ww_inv hp hX hg k hlen.le _ hσ
  have hsh := ld_shape hp hX he (by simp [Ends]) hσ
  have hrg : Proof.Loader.Rng d := ld_rng hp hX hg k hlen _ hσ
  have hlp : LoaderPage Q L g d := ld_page hp hX hg k hlen _ hσ
  have hnN := hlp.1 (by rcases hs with h | h <;> rw [h] <;> rfl)
  have hi : d.i < Q.numIters (Proof.ProA.cta L g .z) (Proof.ProA.cta L g .x) := by
    rw [← hnN]; exact hrg.loop (by rcases hs with h | h <;> rw [h] <;> rfl)
  obtain ⟨hx, hy, hz⟩ := Proof.ProA.cta_lt hp hg
  have hblk := Proof.Result.Mma.blk_lt hp.splitsPos hi
  have hsb := hp.seqRange _ hz
  have hbl : Q.blocks (Proof.ProA.cta L g .z) < 2 ^ 24 := by
    unfold Params.blocks; omega
  obtain ⟨slab, hsl, hsite⟩ : ∃ slab, slab ≤ 1 ∧
      ((slab = 0 ∧ d.site = .ldb0) ∨ (slab = 1 ∧ d.site = .ldb1)) := by
    rcases hs with h | h
    · exact ⟨0, by norm_num, .inl ⟨rfl, h⟩⟩
    · exact ⟨1, le_refl _, .inr ⟨rfl, h⟩⟩
  have hidx : Proof.ProA.cta L g .z * Q.strideBt +
      (2 * (Proof.ProA.cta L g .x + d.i * Q.splits) + slab) < 2 ^ 31 :=
    hp.btIndexRange _ hz _ (by omega)
  have haddr := Proof.EvW.ldBtAddr_spec hp hg hm hpro slab hsl (by omega) (by omega)
  have hsr : 2 * (Proof.ProA.cta L g .x + d.i * Q.splits) + slab <
      2 * Q.blocks (Proof.ProA.cta L g .z) := by omega
  have hrd : ∀ j < 4, Q.reads (Q.btBase + 4 * (Proof.ProA.cta L g .z * Q.strideBt +
      (2 * (Proof.ProA.cta L g .x + d.i * Q.splits) + slab)) + j) :=
    fun j hj => .inr (.inr (.inr (.inr (.inr ⟨_, hz, _, hsr, j, hj, rfl⟩))))
  have hnw := hp.readsRange _ (hrd 3 (by omega))
  have hsh' : ∃ ac bs', (⟨pc, .rd a bs⟩ : Event) = ⟨d.site.pc, .rd ac bs'⟩ ∧
      ac.loc = ⟨.global, 0, Proof.EvW.ldBtAddr L g d slab⟩ ∧ ac.size = 4 := by
    unfold Proof.EvW.LdShape at hsh
    rcases hsite with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> rw [h] at hsh <;> rw [h] <;> exact hsh
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

theorem shared_absurd {a : Acc} {c x : Nat} (hl : a.loc = ⟨.shared, c, x⟩)
    (hsp : a.loc.space ≠ .shared) : False := by
  rw [hl] at hsp
  exact hsp rfl

/-- **A thread's read outside shared memory reads input bytes.** -/
theorem thread_read_input (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨pc, .rd a bs⟩) (hsp : a.loc.space ≠ .shared) : InputAcc Q a := by
  have hb : L.block = 256 := hp.block
  have hg := Frame.lt_of_get hX he
  obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
  cases o with
  | none => exact absurd (fires_none_ends hf) (by simp [Ends])
  | some u =>
    have hev := frag_ev hp hg hJ hat hi hc hf
    have hpc := gload_pc hc hf rfl hsp
    obtain ⟨x, n⟩ := σ
    rcases x with st | ⟨_ | r, d⟩
    · exfalso
      have hs := startup_gl st.site hpc
      have h' : Startup.Ev L g st ⟨pc, .rd a bs⟩ := hev
      simp only [Startup.Ev, hs] at h'
      obtain ⟨ac, bs', h', hl, -, -⟩ := h'
      simp only [Event.mk.injEq, Kind.rd.injEq] at h'
      obtain ⟨-, rfl, rfl⟩ := h'
      exact shared_absurd hl hsp
    · rename_i i
      cases i with
      | dp tm bw =>
        rcases d with d | ⟨_ | _, τ⟩
        · have hx : d.site ≠ .exit := fun h => by
            have := hi.2; simp [Code.gatedExit, ProA.exitOf, h] at this
          have hF := ProA.fired_old (P := Startup.inh L g Q tm) hx hat hi.1 hc hf
          obtain ⟨-, -, hR, -⟩ := (hJ : ProRef Q L g tm bw d n)
          have hpc0 : d.site.pc ∈ gloadPcs := hpc
          have hpc' : d.site.old.pc ∈ gloadPcs := by rw [← ProA.pc_old _ hx]; exact hpc0
          exact pro_read_input hp hg hR hF (pro_gl _ hpc')
        · cases τ with
          | sm d =>
            obtain ⟨-, -, hm⟩ := (hJ : TailRef Q L g tm (.sm d) n)
            have hI : Proof.Sm.Inv L g d := hi
            have hF := sm_fired hat hi hc hf
            rcases sm_gl d.site hpc with hs | hs
            · exfalso
              obtain ⟨ac, bs', he2, hl, -⟩ := Proof.Sm.shape_ldL_foot
                (Proof.ProA.sharedOk_of_pre hp) hF hs
              simp only [Event.mk.injEq, Kind.rd.injEq] at he2
              obtain ⟨-, rfl, -⟩ := he2
              exact shared_absurd hl hsp
            · exact sm_read_input hp hg hm hI hF hs
          | epi d => exact (epi_gl d.site hpc).elim
        · exact hJ.elim
      | worker w =>
        cases d with
        | worker w =>
          exfalso
          have hs : w.site = .ldRole := by
            rcases worker_gl w.site hpc with h | h
            · have hW := hJ.2.2.1.1
              rw [h] at hW
              simp at hW
            · exact h
          have hF : (Proof.WComp.code L g Q).toMachine.Fired (some (.worker w))
              ⟨pc, .rd a bs⟩ (some u) := by
            refine ⟨t, ⟨hat, hi⟩, ?_⟩
            have hc' : kernel.code[(Proof.WComp.code L g Q).pc (.worker w)]? = some ins := hc
            show Fires t.pc ((Proof.WComp.code L g Q).tmpl (some (.worker w)) t) _ (some u)
            simp only [Code.tmpl]
            rw [hc', hat.1]
            exact hf
          obtain ⟨ac, bs', he', hl, -⟩ := Proof.Worker.shape_ldRole hp
            (by rw [hb]; exact Nat.mod_lt _ (by omega)) hs hF
          simp only [Event.mk.injEq, Kind.rd.injEq] at he'
          obtain ⟨-, rfl, -⟩ := he'
          exact shared_absurd hl hsp
        | idle d => exact (idle_gl d.site hpc).elim
        | loader d P =>
          rcases loader_gl d.site hpc with hs | hs | hs | hs
          · exfalso
            have hsh := ld_shape hp hX he (by simp [Ends]) hσ
            unfold Proof.EvW.LdShape at hsh
            rw [hs] at hsh
            obtain ⟨ac, bs', he2, hl, -⟩ := hsh
            simp only [Event.mk.injEq, Kind.rd.injEq] at he2
            obtain ⟨-, rfl, -⟩ := he2
            exact shared_absurd hl hsp
          · exfalso
            have hsh := ld_shape hp hX he (by simp [Ends]) hσ
            unfold Proof.EvW.LdShape at hsh
            rw [hs] at hsh
            obtain ⟨ac, bs', he2, hl, -⟩ := hsh
            simp only [Event.mk.injEq, Kind.rd.injEq] at he2
            obtain ⟨-, rfl, -⟩ := he2
            exact shared_absurd hl hsp
          · exact ld_read_input hp hX he hσ (.inl hs)
          · exact ld_read_input hp hX he hσ (.inr hs)
        | mma d P =>
          exfalso
          have h' : Proof.EvW.MmShape L g d ⟨pc, .rd a bs⟩ := hev
          unfold Proof.EvW.MmShape at h'
          rw [mma_gl d.site hpc] at h'
          obtain ⟨ac, bs', he2, hl, -⟩ := h'
          simp only [Event.mk.injEq, Kind.rd.injEq] at he2
          obtain ⟨-, rfl, -⟩ := he2
          exact shared_absurd hl hsp
        | exit x => exact (exitsite_gl x.site hpc).elim
    · exact hJ.elim

theorem inInput_of_covers {a : Acc} {l : Loc} (h : InputAcc Q a) (hc : a.Covers l) :
    InInput Q l := by
  obtain ⟨hs, hct, hr⟩ := h
  obtain ⟨h1, h2, hlo, hhi⟩ := hc
  refine ⟨h1.trans hs, h2.trans hct, ?_⟩
  have := hr (l.addr - a.loc.addr) (by omega)
  rwa [show a.loc.addr + (l.addr - a.loc.addr) = l.addr by omega] at this

/-- **Global reads of every access of a consistent execution.** -/
theorem global_reads (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) :
    GlobalReads Q X := by
  intro e a l hI hc hsp
  have hsa : a.loc.space ≠ .shared := fun h => hsp (hc.1.trans h)
  rcases e with ⟨g, k⟩ | ⟨i, p⟩
  · rcases hI with ⟨bs, ⟨pc, he⟩, -⟩ | ⟨bs, -, hw⟩ | ⟨old, new, pc, he⟩
    · exact inInput_of_covers (thread_read_input hp hX he hsa) hc
    · cases hw
    · exact absurd he (no_rmw hX)
  · obtain ⟨hw, hfp⟩ := hI
    cases p with
    | mmaRead isB index =>
      obtain ⟨hsz, hmf⟩ := hfp
      rcases hmf with ⟨d, s, acc, mask, ⟨pc, he⟩, hb⟩ | ⟨c, k, cta, hcp, -⟩
      · obtain ⟨tm, dd, P, n, -, hsh⟩ := mma_ev_state hp hX he
        obtain ⟨hB, hA⟩ := Proof.Safety.mma_foot hp hsh
        cases isB
        · exact absurd (hA _ _ hb).1 hsa
        · exact absurd (hB _ _ hb).1 hsa
      · exact absurd hcp (no_cp hX _ _)
    | readLoad x y k =>
      obtain ⟨s, addr, ⟨pc, hget⟩, hloc, hsz⟩ := hfp
      obtain ⟨g, k'⟩ := i
      obtain ⟨r, sl, kvh, isV, hh, dst, bar, hr, hs, hkvh, hV, hH, rfl⟩ := copy_form hp hX hget
      obtain ⟨h1, h2, h3⟩ := Proof.Interface.kvCopy_readLoc_input hp hr hs hkvh hV hH hloc
      obtain ⟨c1, c2, clo, chi⟩ := hc
      rw [hsz] at chi
      have hl : l.addr = a.loc.addr := by omega
      exact ⟨c1.trans h1, c2.trans h2, hl ▸ h3⟩
    | readCopy =>
      rcases hfp with ⟨s, ⟨pc, he⟩, -⟩ | ⟨pc, he⟩
      · exact absurd he (no_copy hX)
      · exact absurd he (no_bulkPrefetch hX)
    | readStore x y k =>
      obtain ⟨s, addr, ⟨pc, he⟩, -⟩ := hfp
      exact absurd he (no_tensorStore hX)
    | readPrefetch x y k =>
      obtain ⟨s, addr, ⟨pc, he⟩, -⟩ := hfp
      exact absurd he (no_tensorPrefetch hX)
    | writeLoad x y k => cases hw
    | writeStore x y k => cases hw
    | writeCta c => cases hw
    | writeCopy => cases hw
    | writeElem j => cases hw
    | oldStore x y k =>
      obtain ⟨s, r, ⟨pc, he⟩, -⟩ := hfp
      exact absurd he (no_tensorStore hX)
    | oldElem j =>
      obtain ⟨s, r, ⟨pc, he⟩, -⟩ := hfp
      exact absurd he (no_copy hX)
    | readCta c => exact hfp.elim
    | readElem j => exact hfp.elim
    | writePrefetch x y k => cases hw
    | oldCopy => exact hfp.elim
    | oldLoad x y k => exact hfp.elim
    | oldCta c => exact hfp.elim
    | oldPrefetch x y k => exact hfp.elim
    | notifyCopy => exact hfp.elim
    | notifyLoad => exact hfp.elim
    | notifyCta c => exact hfp.elim
    | readsDone => exact hfp.elim
    | fullDone => exact hfp.elim
    | resolve => exact hfp.elim
    | tcNotify r => exact hfp.elim
    | mmaDone => exact hfp.elim
    | arriveOn => exact hfp.elim
end
end PTX.Kernels.InklingRelDecode.Proof2
