-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderCounts
public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderCoords
public import Lemmas.Flow.Ledger
public import Lemmas.Flow.NotObject
public import Lemmas.Flow.TensorLoadFacts
public import Lemmas.Flow.TensorCoords
public import Lemmas.Flow.TmplOkSync

@[expose] public section

/-! # The loader's events by site

The event a loader state fires is the event of its site (`Ev`, proved for every firing by
`site_event`), read off its instruction and the state's register values once:

* a poll of the empty barrier its address register names (the KV slot of the ring registers,
  moved by the drain's steps, or a Q stage), with the parity its parity register holds;
* an arrival of one unit on the full barrier its address register names, expecting the
  transaction bytes its byte register holds;
* a tensor copy whose operands are those of the copy `CopyIs` of the site's use, item and trip
  once the ring registers are those of the use (`copy_ev`; the map's rank and box bytes from
  `Pre`, `map_bytes`, and the barrier's copy bytes, `bar_copyBytes`);
* an election, the rank broadcast, the register request and the exit.

None of these is undefined behaviour: the copy's map is the launch's valid map, its box is
aligned in the CTA's window and it completes on the even CTA's barrier of the pair (`copy_ok`),
the polls and arrivals read their operands (`fires_wait_at`, `fires_arrive_kind`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow Work

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t : TState} {e : Event}
  {o : Option TState}

/-! ### Registers and barrier addresses -/

/-- A register's value at a loader state. -/
theorem reg_of {d : D} {pc r : Nat} (h : At t pc (factsAt L g pc d))
    (hr : r ∈ Flow.live pc) : t.regs r = some (valueOf L g d r) :=
  holds_mem h.2.2.2.2 (Flow.mem_factsFrom hr)

/-- A register's value at a loader state, by the table. -/
macro "reg_val " h:term : tactic =>
  `(tactic| (rw [reg_of $h (by live_dec)]; simp only [valueOf, table, Prologue.valueOf,
    Prologue.values, PTX.Flow.lookupLit, Option.getD_some, Option.getD_none, kRow]))

/-- A poll or arrival through a register holding `sb + k`: the thread's CTA's barrier. -/
theorem loc_b32 (hpre : Pre P L mem0) {r k : Nat} (hk : k < 512) (h8 : k % 8 = 0)
    (hr : t.regs r = some (Prologue.sb L k)) :
    mbarLoc L g t r 0 = .ok ⟨.shared, ctaOf L g, L.sharedBase + k⟩ := by
  have hb := hpre.sharedRange
  have ha := hpre.sharedAlignment
  unfold sharedBytes at hb
  exact mbarLoc_b32 hr (by omega) (by omega)

/-- A barrier addressed by a register holding `sb + k` plus an offset `o`. -/
theorem loc_off (hpre : Pre P L mem0) {r k o : Nat} (hk : k + o < 512) (h8 : (k + o) % 8 = 0)
    (hr : t.regs r = some (Prologue.sb L k)) :
    mbarLoc L g t r (o : Int) = .ok ⟨.shared, ctaOf L g, L.sharedBase + (k + o)⟩ := by
  have hb := hpre.sharedRange
  have ha := hpre.sharedAlignment
  unfold sharedBytes at hb
  have hv : (truncBits 32 (truncBits 32 (BitVec.ofNat 64 (L.sharedBase + k)) +
      BitVec.ofInt 64 (o : Int))).toNat = L.sharedBase + (k + o) := by
    nf_simp
    omega
  have h8' : (L.sharedBase + (k + o)) % 8 = 0 := by omega
  simp only [mbarLoc, effAddr, sharedEffAddr, readReg, hr, Prologue.sb, b32, readBits, hv, h8',
    bind, Except.bind, pure, Except.pure, ↓reduceIte, ctaOf]

/-- A copy's barrier through a register holding `peerV L g k`: the even CTA's barrier. -/
theorem loc_peer (hpre : Pre P L mem0) (hg : g < L.threads) {r k : Nat} (hk : k < 512)
    (h8 : k % 8 = 0) (hr : t.regs r = some (peerV L g k)) :
    mbarClusterLoc L g t r 0 = .ok ⟨.shared, evenCta L g, L.sharedBase + k⟩ := by
  have hb := hpre.sharedRange
  have ha := hpre.sharedAlignment
  have hcta := cta_lt hg
  have hgr := hpre.grid
  have hcl := hpre.cluster
  unfold sharedBytes at hb
  unfold ctaOf at hcta
  refine mbarClusterLoc_ptr hr hg ?_ ?_ (by omega) (by omega)
  · unfold evenCta ctaOf; omega
  · simp only [Launch.oneDim_clusterOfCta hpre.oneDimLaunch.1, hcl, evenCta, ctaOf]; omega

/-- The item's head register holds the head of its work item. -/
theorem reg_head (hpre : Pre P L mem0) {d : D} {i : Nat} (hd : d.i = i)
    (hr : t.regs 3910 = some (valueOf L g d 3910)) (hw : workOf L g i < 2 ^ 32) :
    t.regs 3910 = some (b32 (coordsOf L (workOf L g i)).2.1) := by
  subst hd
  rw [hr]
  simp only [valueOf, table, Prologue.valueOf, Prologue.values, PTX.Flow.lookupLit,
    Option.getD_some, Option.getD_none, Work.Dm.headW_eq hpre hw]
  rfl

theorem reg_batch (hpre : Pre P L mem0) {d : D} {i : Nat} (hd : d.i = i)
    (hr : t.regs 3909 = some (valueOf L g d 3909)) (hw : workOf L g i < 2 ^ 32) :
    t.regs 3909 = some (b32 (coordsOf L (workOf L g i)).1) := by
  subst hd
  rw [hr]
  simp only [valueOf, table, Prologue.valueOf, Prologue.values, PTX.Flow.lookupLit,
    Option.getD_some, Option.getD_none, Work.Dm.batchW_eq hpre hw]
  rfl

theorem reg_qrow0 (hpre : Pre P L mem0) {d : D} {i : Nat} (hd : d.i = i)
    (hr : t.regs 364 = some (valueOf L g d 364)) (hw : workOf L g i < 2 ^ 32)
    (hm : 512 * (coordsOf L (workOf L g i)).2.2 + 512 < 2 ^ 31) :
    t.regs 364 = some (b32 (512 * (coordsOf L (workOf L g i)).2.2 + 128 * rank L g +
      256 * 0)) := by
  subst hd
  rw [hr]
  simp only [valueOf, table, Prologue.valueOf, Prologue.values, PTX.Flow.lookupLit,
    Option.getD_some, Option.getD_none, Work.Dm.qRowW_eq hpre hw hm]
  rw [show 128 * rank L g + 512 * (coordsOf L (workOf L g d.i)).2.2 =
    512 * (coordsOf L (workOf L g d.i)).2.2 + 128 * rank L g + 256 * 0 by omega]
  rfl

theorem reg_qrow1 (hpre : Pre P L mem0) {d : D} {i : Nat} (hd : d.i = i)
    (hr : t.regs 370 = some (valueOf L g d 370)) (hw : workOf L g i < 2 ^ 32)
    (hm : 512 * (coordsOf L (workOf L g i)).2.2 + 512 < 2 ^ 31) :
    t.regs 370 = some (b32 (512 * (coordsOf L (workOf L g i)).2.2 + 128 * rank L g +
      256 * 1)) := by
  subst hd
  rw [hr]
  simp only [valueOf, table, Prologue.valueOf, Prologue.values, PTX.Flow.lookupLit,
    Option.getD_some, Option.getD_none, Work.Dm.qRowW_eq' hpre hw hm]
  rw [show 128 * rank L g + 512 * (coordsOf L (workOf L g d.i)).2.2 + 256 =
    512 * (coordsOf L (workOf L g d.i)).2.2 + 128 * rank L g + 256 * 1 by omega]
  rfl

/-! ### The ring registers -/

theorem ring_next {s ph B : Nat} (hs : s = B % 6) (hp : ph = (B / 6 + 1) % 2) :
    snext s = (B + 1) % 6 ∧ pnext s ph = ((B + 1) / 6 + 1) % 2 := by
  subst hs hp
  unfold snext pnext
  split_ifs <;> omega

theorem ring_after {s ph B : Nat} (hs : s = B % 6) (hp : ph = (B / 6 + 1) % 2) :
    ∀ k, sAfter k s = (B + k) % 6 ∧ pAfter k s ph = ((B + k) / 6 + 1) % 2
  | 0 => ⟨hs, hp⟩
  | k + 1 => by
    obtain ⟨h1, h2⟩ := ring_after hs hp k
    obtain ⟨h3, h4⟩ := ring_next h1 h2
    exact ⟨h3, h4⟩

/-! ### The copies' maps and bytes -/

theorem bytes_encodeTiled (base rows heads batch boxRows : Nat) (fill : TensorDescriptor.Fill)
    (cls : TensorDescriptor.AllocationClass) :
    TensorTransfer.bytes (encodeTiled base rows heads batch boxRows fill cls) =
      64 * boxRows * 2 := by
  simp [TensorTransfer.bytes, encodeTiled, TensorTile.count, TensorTile.step, TensorTile.rows,
    TensorTile.rowsOf, TensorDescriptor.Format.bytes]

/-- The bytes of one copy of a use's kind: a Q box, a K box (half the rows), a V box. -/
def CopyId.bytes (c : CopyId) : Nat :=
  match c.u with
  | .q0 | .q1 => 16384
  | .k0 | .k => 8192
  | .v0 | .v => 16384

/-- The barrier's copy bytes are those of the use's kind. -/
theorem bar_copyBytes (L : Launch) (c : CopyId) : (c.bar L).copyBytes = c.bytes := by
  obtain ⟨u, j, i, t⟩ := c
  have h2 : uB L i % 2 = 0 := uB_even L i
  cases u <;> simp only [CopyId.bar, CopyId.use, CopyId.bytes, FBar.copyBytes] <;> split_ifs <;>
    omega

/-- The map a copy reads has rank 4 and its box holds the copy's bytes. -/
theorem map_bytes (hpre : Pre P L mem0) {c : CopyId} {a outer : Nat}
    {d : TensorDescriptor.Descriptor outer}
    (hmap : ∃ decl, L.paramObjects c.map = some (decl, a))
    (hd : L.tensorMaps a = some ⟨outer, d⟩) : outer = 3 ∧ TensorTransfer.bytes d = c.bytes := by
  obtain ⟨decl, hdecl⟩ := hmap
  have key : ∀ {pa : Nat} {dd : TensorDescriptor.Descriptor 3},
      L.tensorMaps pa = some ⟨3, dd⟩ → pa = a → TensorTransfer.bytes dd = c.bytes →
      outer = 3 ∧ TensorTransfer.bytes d = c.bytes := by
    intro pa dd h1 h2 h3
    subst h2
    rw [h1] at hd
    have h4 := Option.some.inj hd
    exact ⟨(congrArg Sigma.fst h4).symm, by
      have := congrArg (fun p : (o : Nat) × TensorDescriptor.Descriptor o =>
        TensorTransfer.bytes p.2) h4
      simp only at this
      rw [← this]; exact h3⟩
  obtain ⟨u, j, i, t⟩ := c
  cases u <;> simp only [CopyId.map, CopyId.bytes] at hdecl ⊢
  · rw [hpre.paramK] at hdecl
    exact key hpre.mapK (Prod.mk.inj (Option.some.inj hdecl)).2
      (by rw [mapK, bytes_encodeTiled]; rfl)
  · rw [hpre.paramQ] at hdecl
    exact key hpre.mapQ (Prod.mk.inj (Option.some.inj hdecl)).2
      (by rw [mapQ, bytes_encodeTiled]; rfl)
  · rw [hpre.paramQ] at hdecl
    exact key hpre.mapQ (Prod.mk.inj (Option.some.inj hdecl)).2
      (by rw [mapQ, bytes_encodeTiled]; rfl)
  · rw [hpre.paramV] at hdecl
    exact key hpre.mapV (Prod.mk.inj (Option.some.inj hdecl)).2
      (by rw [mapV, bytes_encodeTiled]; rfl)
  · rw [hpre.paramK] at hdecl
    exact key hpre.mapK (Prod.mk.inj (Option.some.inj hdecl)).2
      (by rw [mapK, bytes_encodeTiled]; rfl)
  · rw [hpre.paramV] at hdecl
    exact key hpre.mapV (Prod.mk.inj (Option.some.inj hdecl)).2
      (by rw [mapV, bytes_encodeTiled]; rfl)

/-- The map of a copy, read through its parameter, is the launch's valid map, of half-precision
elements. -/
theorem map_ok (hpre : Pre P L mem0) {rm : Nat} {cs : List Opnd} {name : String}
    (hcs : cs.length = 4) (hr : t.regs rm = some (.ptr 64 true (.param name) 0))
    (hn : name = param "4" ∨ name = param "5" ∨ name = param "6") :
    ∃ a d, tensorMap L g t (.reg rm) cs .tile = .ok (a, ⟨3, d⟩) ∧ d.format = .f16 := by
  have hal := hpre.mapAlignment
  have hra := hpre.mapRange
  have hta := hpre.tensorAlignment
  have hsq := hpre.sqRange
  have hsk := hpre.skRange
  have hsqp := hpre.sqPos
  have hskp := hpre.skPos
  have hst := hpre.strideRange
  have hbr := hpre.batchRange
  have hbp := hpre.bPos
  have hhp := hpre.hPos
  rcases hn with rfl | rfl | rfl
  · have hv : TensorDescriptor.Valid (mapQ P.qBase P.sq P.h P.b P.qFill P.qClass) :=
      encodeTiled_valid hta.1 ⟨hsqp, by omega⟩ hhp ⟨hbp, hbr⟩ hst.1 ⟨by decide, by decide⟩
    exact ⟨P.qMap, mapQ P.qBase P.sq P.h P.b P.qFill P.qClass, by
      simp [tensorMap, tensorMapAddress, readValue, readReg, hr, hpre.paramQ, mapParam,
        ParamObjectDecl.bytes, hpre.mapQ, hv, hcs, TensorMode.coordinates, hal.1,
        show P.qMap ≤ 18446744073709551488 by omega, bind, Except.bind, pure, Except.pure], rfl⟩
  · have hv : TensorDescriptor.Valid (mapK P.kBase P.sk P.h P.b P.kFill P.kClass) :=
      encodeTiled_valid hta.2.1 ⟨hskp, by omega⟩ hhp ⟨hbp, hbr⟩ hst.2 ⟨by decide, by decide⟩
    exact ⟨P.kMap, mapK P.kBase P.sk P.h P.b P.kFill P.kClass, by
      simp [tensorMap, tensorMapAddress, readValue, readReg, hr, hpre.paramK, mapParam,
        ParamObjectDecl.bytes, hpre.mapK, hv, hcs, TensorMode.coordinates, hal.2.1,
        show P.kMap ≤ 18446744073709551488 by omega, bind, Except.bind, pure, Except.pure], rfl⟩
  · have hv : TensorDescriptor.Valid (mapV P.vBase P.sk P.h P.b P.vFill P.vClass) :=
      encodeTiled_valid hta.2.2.1 ⟨hskp, by omega⟩ hhp ⟨hbp, hbr⟩ hst.2 ⟨by decide, by decide⟩
    exact ⟨P.vMap, mapV P.vBase P.sk P.h P.b P.vFill P.vClass, by
      simp [tensorMap, tensorMapAddress, readValue, readReg, hr, hpre.paramV, mapParam,
        ParamObjectDecl.bytes, hpre.mapV, hv, hcs, TensorMode.coordinates, hal.2.2.1,
        show P.vMap ≤ 18446744073709551488 by omega, bind, Except.bind, pure, Except.pure], rfl⟩

/-! ### The events of the instructions -/

/-- A poll through registers holding the barrier at `sb + k` and the parity `v`. -/
theorem wait_ev (hpre : Pre P L mem0) {pc x base par k v : Nat} {acq : Bool} {sc : MbarScope}
    (hb : t.regs base = some (Prologue.sb L k)) (hk : k < 512) (h8 : k % 8 = 0)
    (hp : t.regs par = some (b32 v))
    (hf : Fires pc (eventTmpl asms L g t (.mbarWait x base 0 (.reg par) acq sc)) e o) :
    ∃ ok acq' sc', e.kind = .wait ⟨.shared, ctaOf L g, L.sharedBase + k⟩ (v % 2) ok acq' sc' := by
  obtain ⟨ok, acq', sc', he, -⟩ := fires_wait_at (loc_b32 hpre hk h8 hb) (readBits_b32' hp) hf
  refine ⟨ok, acq', sc', ?_⟩
  rw [he]
  simp only [truncBits, BitVec.toNat_ofNat]
  congr 1
  omega

/-- An arrival of one unit through a register holding `sb + k` plus `o`, with the byte count
`v`. -/
theorem arrive_ev (hpre : Pre P L mem0) {pc base k o k' tx v : Nat} {rel : Bool}
    {sc : MbarScope} {st : Option Nat} (hb : t.regs base = some (Prologue.sb L k))
    (hk : k + o < 512) (h8 : (k + o) % 8 = 0) (hko : k + o = k') (hp : t.regs tx = some (b32 v))
    (hv : v < 2 ^ 32)
    (hf : Fires pc (eventTmpl asms L g t (.mbarArrive base o (.reg tx) (.imm 1) false rel sc st))
      e o') :
    ∃ rel' sc', e.kind = .arrive ⟨.shared, ctaOf L g, L.sharedBase + k'⟩ v 1 rel' sc' := by
  subst hko
  obtain ⟨rel', sc', he⟩ := fires_arrive_kind (n := truncBits 32 (BitVec.ofInt 64 1))
    (loc_off hpre hk h8 hb) (readBits_b32' hp) (by simp only [readBits, pure, Except.pure]) hf
  refine ⟨rel', sc', ?_⟩
  rw [he]
  simp only [truncBits, BitVec.toNat_ofNat]
  congr 1
  omega

/-- An election with the full mask. -/
theorem elect_ev {pc : Nat} {dst : Option Nat} {p : Nat}
    (hf : Fires pc (eventTmpl asms L g t (.warp ⟨.elect, none, [dst, some p], [],
      some (.imm (-1))⟩)) e o) : ∃ mask inst ld, e.kind = .elect mask inst ld := by
  obtain ⟨u, rfl⟩ := fires_some_of_ok hf (fun f => elect_imm_ok f) ⟨nofun, nofun⟩
  obtain ⟨mk, inst, ld, rfl, -⟩ := fires_elect hf
  exact ⟨mk, inst, ld, rfl⟩

/-- **A loader copy is not undefined behaviour**, given its operand registers. -/
theorem copy_ok (hpre : Pre P L mem0) (hg : g < L.threads) {dst rm r0 r1 r2 r3 mb pr : Nat}
    {off : Int} {name : String} {kd o' k : Nat}
    (hm : t.regs rm = some (.ptr 64 true (.param name) 0))
    (hn : name = param "4" ∨ name = param "5" ∨ name = param "6")
    (hd : t.regs dst = some (win L g kd)) (ho : off = o') (hb : kd + o' ≤ 232448)
    (h128 : (kd + o') % 128 = 0) (hbar : t.regs mb = some (peerV L g k)) (hk : k < 512)
    (h8 : k % 8 = 0)
    (h0 : ∃ v, t.regs r0 = some (.bits 32 (BitVec.ofNat 64 v)) ∧ v < 2 ^ 31 ∧ v % 8 = 0)
    (h1 : ∃ v, t.regs r1 = some (.bits 32 v)) (h2 : ∃ v, t.regs r2 = some (.bits 32 v))
    (h3 : ∃ v, t.regs r3 = some (.bits 32 v)) (hp : t.regs pr = some zero64) (f : Fault) :
    eventTmpl asms L g t (.cpTensor true true dst off (.reg rm)
      [.reg r0, .reg r1, .reg r2, .reg r3] mb 0 none .tile (some (.reg pr))) ≠ .ub f := by
  have hsh := (shape hpre).1
  have hal := hpre.sharedAlignment
  have hcta := cta_lt hg
  have hgr := hpre.grid
  have hcl := hpre.cluster
  obtain ⟨a, d, hmap, hfmt⟩ :=
    map_ok hpre (cs := [.reg r0, .reg r1, .reg r2, .reg r3]) rfl hm hn
  obtain ⟨v0, h0, hv0, hv8⟩ := h0
  have hr0 : readBits L g t 32 (.reg r0) = .ok (BitVec.ofNat 64 v0) := readBits_b32 h0 (by omega)
  obtain ⟨v1, h1⟩ := h1
  obtain ⟨v2, h2⟩ := h2
  obtain ⟨v3, h3⟩ := h3
  have hdl := sharedEffAddr_ptr (a := L.sharedBase + kd) (o := o') hd hg hcta rfl (by omega) ho
  have hml := loc_peer hpre hg hk h8 hbar
  have hp' : cachePolicyRead L g t (some (.reg pr)) = .ok () := by
    simp [cachePolicyRead, readBits, readReg, hp, zero64, bind, Except.bind, pure, Except.pure]
  have hvs : [Opnd.reg r0, .reg r1, .reg r2, .reg r3].mapM (readBits L g t 32) =
      .ok [BitVec.ofNat 64 v0, truncBits 32 v1, truncBits 32 v2, truncBits 32 v3] := by
    simp only [List.mapM_cons, List.mapM_nil, hr0]
    simp [readBits, readReg, h1, h2, h3, bind, Except.bind, pure, Except.pure]
  have hbox : TensorDescriptor.BoxAligned d (fun axis => (BitVec.ofNat 32
      ([BitVec.ofNat 64 v0, truncBits 32 v1, truncBits 32 v2, truncBits 32 v3].getD axis.val
        0).toNat).toInt) := by
    -- the innermost coordinate is a multiple of 8 half-precision elements (16 bytes)
    simp only [TensorDescriptor.BoxAligned, hfmt, TensorDescriptor.Format.bytes, Fin.val_zero,
      List.getD_cons_zero, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), toInt_ofNat_lt32 hv0]
    omega
  have h128' : (L.sharedBase + kd + o') % 128 = 0 := by omega
  have hrt : TensorRoute L (g / L.block) true .two ⟨.shared, ctaOf L g, L.sharedBase + kd + o'⟩
      ⟨.shared, evenCta L g, L.sharedBase + k⟩ := by
    have h1d := hpre.oneDimLaunch.1
    unfold ctaOf at hcta
    refine ⟨Launch.oneDimLaunch_clusterGridValid hpre.oneDimLaunch, ?_⟩
    simp only [CtaInCluster, sameCtaGroup_iff, Launch.oneDim_clusterOfCta h1d,
      Launch.oneDim_rankOfCta h1d, hcl, hgr, CtaGroup.size, evenCta, ctaOf]
    and_intros <;> first | trivial | omega | (intro h; cases h)
  exact cpTensor_off_ok hp' hmap hdl h128' hml hvs hbox hrt f

/-- **A firing of a loader copy instruction** issues a tensor copy; it is the copy `CopyIs c` of
every copy `c` whose map, destination, barrier and coordinates are those its registers hold: the
map register holds the parameter pointer `c.map`, the destination register the CTA's window
pointer at `kd` with the immediate `o'` reaching `c.dst`, the barrier register the peer-bit
address of the copy's barrier, the four coordinate registers the 32-bit values of `c.coords`. -/
theorem copy_ev (hpre : Pre P L mem0) (hg : g < L.threads) {pc dst rm r0 r1 r2 r3 mb pr : Nat}
    {off : Int} {name : String} {kd o' k x0 x1 x2 x3 : Nat}
    (hf : Fires pc (eventTmpl asms L g t (.cpTensor true true dst off (.reg rm)
      [.reg r0, .reg r1, .reg r2, .reg r3] mb 0 none .tile (some (.reg pr)))) e o)
    (hm : t.regs rm = some (.ptr 64 true (.param name) 0))
    (hn : name = param "4" ∨ name = param "5" ∨ name = param "6")
    (hd : t.regs dst = some (win L g kd)) (ho : off = o') (hb : kd + o' ≤ 232448)
    (h128 : (kd + o') % 128 = 0) (hbar : t.regs mb = some (peerV L g k)) (hk : k < 512)
    (h8 : k % 8 = 0) (hr0 : t.regs r0 = some (b32 x0)) (hr1 : t.regs r1 = some (b32 x1))
    (hr2 : t.regs r2 = some (b32 x2)) (hr3 : t.regs r3 = some (b32 x3)) (hx0 : x0 < 2 ^ 31)
    (hx08 : x0 % 8 = 0) (hx1 : x1 < 2 ^ 31) (hx2 : x2 < 2 ^ 31) (hx3 : x3 < 2 ^ 31)
    (hp : t.regs pr = some zero64) :
    ∃ a sp, e.kind = .tensorIssue a sp ∧ ∀ c : CopyId, c.map = name → kd + o' = c.dst L →
      (c.bar L).off = k → c.coords L g = [x0, x1, x2, x3] → CopyIs L g c a sp := by
  obtain ⟨u, rfl⟩ := fires_some_of_ok hf (copy_ok hpre hg hm hn hd ho hb h128 hbar hk h8
    ⟨x0, hr0, hx0, hx08⟩ ⟨_, hr1⟩ ⟨_, hr2⟩ ⟨_, hr3⟩ hp) ⟨nofun, nofun⟩
  obtain ⟨a, sp, he, -, -⟩ := fires_cpTensor_issue hf
  refine ⟨a, sp, by rw [he], fun c hmap hdst hbar' hx => ?_⟩
  subst hmap hbar'
  have hk' : e.kind = .tensorIssue a sp := by rw [he]
  have hsh := (shape hpre).1
  have hcopy := fires_cpTensor_copy hf hk'
  obtain ⟨hma, hmb, dd, hdd, -, hdesc, hrows⟩ := tensorLoadCopy_ok hcopy
  obtain ⟨hsb, hca, hgrp⟩ := tensorLoadCopy_box hcopy
  simp only [↓reduceIte] at hmb
  obtain ⟨decl, hdecl⟩ := tensorMapAddress_param hm hma
  obtain ⟨hout, hby⟩ := map_bytes hpre ⟨decl, hdecl⟩ hdd
  have hcta := cta_lt hg
  rw [sharedEffAddr_ptr (a := L.sharedBase + kd) (o := o') hd hg hcta rfl (by omega) ho] at hsb
  rw [loc_peer hpre hg hk h8 hbar] at hmb
  have hor := tensorLoadCopy_origin_regs hcopy hr0 hr1 hr2 hr3 hx0 hx1 hx2 hx3
  simp only [TensorMode.transfer] at hdesc
  refine ⟨⟨decl, hdecl⟩, hout, fun i => ?_, ?_, ?_, ?_, by rw [hdesc]; exact hdd, hrows.mpr rfl,
    hca, by simpa using hgrp⟩
  · rw [hor i, hx]
  · rw [← Except.ok.inj hsb]
    simp only [Loc.mk.injEq, true_and]
    omega
  · rw [← Except.ok.inj hmb]
    rfl
  · rw [hdesc, hby, bar_copyBytes]

/-! ### The shape table -/

/-- A poll of the barrier at `sb + k` of the thread's CTA with the parity `p`. -/
def PollIs (L : Launch) (g k p : Nat) (e : Event) : Prop :=
  ∃ ok acq sc, e.kind = .wait ⟨.shared, ctaOf L g, L.sharedBase + k⟩ (p % 2) ok acq sc

/-- An arrival of one unit on the barrier at `sb + k` of the thread's CTA, expecting `tx`
bytes. -/
def ArriveIs (L : Launch) (g k tx : Nat) (e : Event) : Prop :=
  ∃ rel sc, e.kind = .arrive ⟨.shared, ctaOf L g, L.sharedBase + k⟩ tx 1 rel sc

/-- **The event of a loader state's site**, from its ring registers: the KV polls and
arrivals are on the slot `s` of the state's K use, or the next slot for a V use, the drain's
`k`-th poll on the slot `k` uses on; the Q polls and arrivals on the stage's barriers; a copy
is the copy `CopyIs` of its use, item and trip when the ring registers are those of its use. -/
def Ev (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  match d.site with
  | .setMaxReg => ∃ inc n inst, e.kind = .setMaxReg inc n inst
  | .head => ∃ m a b c recv ok, e.kind = .shfl m a b c recv ok
  | .wait .q0 => PollIs L g 16 d.qp e
  | .wait .q1 | .drainQ => PollIs L g 24 d.qp e
  | .wait .v0 | .wait .v => PollIs L g (80 + 8 * snext d.s) (pnext d.s d.ph) e
  | .wait _ => PollIs L g (80 + 8 * d.s) d.ph e
  | .drain k => PollIs L g (80 + 8 * sAfter k d.s) (pAfter k d.s d.ph) e
  | .elA _ | .elC _ _ | .elTail => ∃ mask inst ld, e.kind = .elect mask inst ld
  | .arrive .q0 => ArriveIs L g 0 65536 e
  | .arrive .q1 | .arriveTail => ArriveIs L g 8 65536 e
  | .arrive .v0 | .arrive .v => ArriveIs L g (32 + 8 * snext d.s) 32768 e
  | .arrive _ => ArriveIs L g (32 + 8 * d.s) 32768 e
  | .copy u j => ∃ a sp, e.kind = .tensorIssue a sp ∧
      (d.s = kvB L g d % 6 → CopyIs L g ⟨u, j, d.i, d.t⟩ a sp)
  | .exit => e.kind = .exit

/-- Close the side conditions of a copy: the slot of the ring registers, the window and the
coordinates. -/
syntax "copy_close" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| copy_close) => `(tactic| (
      first
        | rfl
        | (simp only [CopyId.map, CopyId.dst, CopyId.bar, CopyId.use, CopyId.coords,
            CopyId.block, CopyId.stage, FBar.off, kvB, Fin.isValue, Fin.val_zero, Fin.val_one,
            List.cons.injEq, and_true, reduceCtorEq, ↓reduceIte] at hR ⊢
           (try simp only [snext]) <;> (try split_ifs) <;> omega)))

set_option maxHeartbeats 4000000 in
/-- **The event a loader state fires is the event of its site.** -/
theorem site_event (hpre : Pre P L mem0) (hg : g < L.threads) : (code asms L g).Shape (Ev L g) :=
    by
  intro d t ins e o h hi hc hf
  replace h : At t d.site.pc (facts L g d) := h
  replace hi : Inv L g d := hi
  replace hc : kernel.code[d.site.pc]? = some ins := hc
  have hsh := shape hpre
  have hrk : rank L g < 2 := Nat.mod_lt _ (by decide)
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  have hs6 : s < 6 := hi.s
  have hsn := snext_lt hs6
  have hA := sAfter_lt hs6
  cases site with
  | setMaxReg =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_1)
    obtain ⟨u, rfl⟩ := fires_some_of_ok hf (plainOk_tmpl (by rw [hpre.block]) (by decide))
      ⟨nofun, nofun⟩
    simp only [eventTmpl, SetMaxNReg.tmpl] at hf
    split_ifs at hf
    · obtain ⟨inst, rfl, -⟩ := hf
      exact ⟨_, _, inst, rfl⟩
    · simp [Fires] at hf
  | head =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_4)
    obtain ⟨u, rfl⟩ := fires_some_of_ok hf (shfl_imm_ok (p := none) (.inr rfl)
      (by rw [hpre.block]) (by reg_val h; rfl)) ⟨nofun, nofun⟩
    obtain ⟨av, bv, cv, recv, ok, rfl, -⟩ := fires_shfl (p := none) hf
    exact ⟨_, _, _, _, _, _, rfl⟩
  | wait u =>
    cases u <;> simp only [Ev, PollIs]
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_0)
      exact wait_ev hpre (by reg_val h) (by omega) (by omega)
        (by reg_val h) hf
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_1)
      exact wait_ev hpre (by reg_val h) (by omega) (by omega)
        (by reg_val h) hf
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_2)
      exact wait_ev hpre (by reg_val h) (by omega) (by omega)
        (by reg_val h) hf
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_3)
      exact wait_ev hpre (by reg_val h) (by omega) (by omega)
        (by reg_val h) hf
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_4)
      exact wait_ev hpre (by reg_val h) (by omega) (by omega)
        (by reg_val h) hf
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_5)
      exact wait_ev hpre (by reg_val h) (by omega) (by omega)
        (by reg_val h) hf
  | drain k =>
    fin_cases k <;> simp only [Ev, PollIs]
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_6)
      simp only [sAfter, pAfter]
      exact wait_ev hpre (by reg_val h) (by have := hA 0; omega) (by omega)
        (by reg_val h) hf
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_7)
      exact wait_ev hpre (by reg_val h) (by have := hA 1; omega) (by omega)
        (by reg_val h) hf
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_8)
      exact wait_ev hpre (by reg_val h) (by have := hA 2; omega) (by omega)
        (by reg_val h) hf
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_9)
      exact wait_ev hpre (by reg_val h) (by have := hA 3; omega) (by omega)
        (by reg_val h) hf
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_10)
      exact wait_ev hpre (by reg_val h) (by have := hA 4; omega) (by omega)
        (by reg_val h) hf
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_11)
      exact wait_ev hpre (by reg_val h) (by have := hA 5; omega) (by omega)
        (by reg_val h) hf
  | drainQ =>
    simp only [Ev, PollIs]
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_12)
    exact wait_ev hpre (by reg_val h) (by omega) (by omega)
        (by reg_val h) hf
  | elA u =>
    cases u <;> simp only [Ev]
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_15)
      exact elect_ev hf
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_18)
      exact elect_ev hf
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_21)
      exact elect_ev hf
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_24)
      exact elect_ev hf
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_26)
      exact elect_ev hf
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_29)
      exact elect_ev hf
  | elC u j =>
    cases u <;> rcases Store.fin2_cases j with rfl | rfl <;> simp only [Ev]
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_16)
      exact elect_ev hf
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_17)
      exact elect_ev hf
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_19)
      exact elect_ev hf
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_20)
      exact elect_ev hf
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_22)
      exact elect_ev hf
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_23)
      exact elect_ev hf
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_25)
      exact elect_ev hf
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_25)
      exact elect_ev hf
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_27)
      exact elect_ev hf
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_28)
      exact elect_ev hf
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_30)
      exact elect_ev hf
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_30)
      exact elect_ev hf
  | elTail =>
    simp only [Ev]
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_31)
    exact elect_ev hf
  | arrive u =>
    cases u <;> simp only [Ev, ArriveIs]
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_0)
      exact arrive_ev hpre (k := 8 * s) (o := 32) (by reg_val h) (by omega) (by omega)
        (by omega) (by reg_val h) (by omega) hf
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_1)
      exact arrive_ev hpre (k := 0) (o := 0) (by reg_val h) (by omega) (by omega) (by omega)
        (by reg_val h) (by omega) hf
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_2)
      exact arrive_ev hpre (k := 8) (o := 0) (by reg_val h) (by omega) (by omega) (by omega)
        (by reg_val h) (by omega) hf
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_3)
      exact arrive_ev hpre (k := 8 * snext s) (o := 32) (by reg_val h) (by omega) (by omega)
        (by omega) (by reg_val h) (by omega) hf
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_4)
      exact arrive_ev hpre (k := 8 * s) (o := 32) (by reg_val h) (by omega) (by omega)
        (by omega) (by reg_val h) (by omega) hf
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_5)
      exact arrive_ev hpre (k := 8 * snext s) (o := 32) (by reg_val h) (by omega) (by omega)
        (by omega) (by reg_val h) (by omega) hf
  | arriveTail =>
    simp only [Ev, ArriveIs]
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_6)
    exact arrive_ev hpre (k := 8) (o := 0) (by reg_val h) (by omega) (by omega) (by omega)
      (by reg_val h) (by omega) hf
  | copy u j =>
    have hit : i < T L g := hi.item rfl
    obtain ⟨hw31, hb, hh, hm⟩ := Work.Dm.item_bounds hpre hit
    have hsq := hpre.sqRange
    have hev := uB_even L i
    have hone := hi.one u j (.inr rfl)
    cases u <;> rcases Store.fin2_cases j with rfl | rfl <;>
      simp only [UseK.copies, Fin.isValue, Fin.val_one, Fin.val_zero] at hone <;>
      (try omega) <;> simp only [Ev]
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_0)
      obtain ⟨a, sp, hk, hci⟩ := copy_ev hpre hg hf (kd := 16384 * s) (o' := 134144)
        (k := 32 + 8 * s) (x0 := 0) (x1 := 128 * (n L - 1) + 64 * rank L g)
        (by reg_val h; rfl) (by simp) (by reg_val h) rfl (by omega) (by omega) (by reg_val h)
        (by omega) (by omega) (by reg_val h) (by reg_val h)
        (reg_head (i := i) hpre rfl (reg_of h (by live_dec)) (by omega))
        (reg_batch (i := i) hpre rfl (reg_of h (by live_dec)) (by omega))
        (by omega) (by omega) (by omega) (by omega) (by omega) (by reg_val h)
      exact ⟨a, sp, hk, fun hR => hci _ rfl (by copy_close) (by copy_close) (by copy_close)⟩
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_1)
      obtain ⟨a, sp, hk, hci⟩ := copy_ev hpre hg hf (kd := 16384 * s) (o' := 142336)
        (k := 32 + 8 * s) (x0 := 64) (x1 := 128 * (n L - 1) + 64 * rank L g)
        (by reg_val h; rfl) (by simp) (by reg_val h) rfl (by omega) (by omega) (by reg_val h)
        (by omega) (by omega) (by reg_val h) (by reg_val h)
        (reg_head (i := i) hpre rfl (reg_of h (by live_dec)) (by omega))
        (reg_batch (i := i) hpre rfl (reg_of h (by live_dec)) (by omega))
        (by omega) (by omega) (by omega) (by omega) (by omega) (by reg_val h)
      exact ⟨a, sp, hk, fun hR => hci _ rfl (by copy_close) (by copy_close) (by copy_close)⟩
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_2)
      obtain ⟨a, sp, hk, hci⟩ := copy_ev hpre hg hf (kd := 68608) (o' := 0) (k := 0) (x0 := 0)
        (x1 := 512 * (coordsOf L (workOf L g i)).2.2 + 128 * rank L g + 256 * 0)
        (by reg_val h; rfl) (by simp) (by reg_val h) rfl (by omega) (by omega) (by reg_val h)
        (by omega) (by omega) (by reg_val h)
        (reg_qrow0 (i := i) hpre rfl (reg_of h (by live_dec)) (by omega) (by omega))
        (reg_head (i := i) hpre rfl (reg_of h (by live_dec)) (by omega))
        (reg_batch (i := i) hpre rfl (reg_of h (by live_dec)) (by omega))
        (by omega) (by omega) (by omega) (by omega) (by omega) (by reg_val h)
      exact ⟨a, sp, hk, fun _ => hci _ rfl (by copy_close) (by copy_close) (by copy_close)⟩
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_3)
      obtain ⟨a, sp, hk, hci⟩ := copy_ev hpre hg hf (kd := 84992) (o' := 0) (k := 0) (x0 := 64)
        (x1 := 512 * (coordsOf L (workOf L g i)).2.2 + 128 * rank L g + 256 * 0)
        (by reg_val h; rfl) (by simp) (by reg_val h) rfl (by omega) (by omega) (by reg_val h)
        (by omega) (by omega) (by reg_val h)
        (reg_qrow0 (i := i) hpre rfl (reg_of h (by live_dec)) (by omega) (by omega))
        (reg_head (i := i) hpre rfl (reg_of h (by live_dec)) (by omega))
        (reg_batch (i := i) hpre rfl (reg_of h (by live_dec)) (by omega))
        (by omega) (by omega) (by omega) (by omega) (by omega) (by reg_val h)
      exact ⟨a, sp, hk, fun _ => hci _ rfl (by copy_close) (by copy_close) (by copy_close)⟩
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_4)
      obtain ⟨a, sp, hk, hci⟩ := copy_ev hpre hg hf (kd := 101376) (o' := 0) (k := 8) (x0 := 0)
        (x1 := 512 * (coordsOf L (workOf L g i)).2.2 + 128 * rank L g + 256 * 1)
        (by reg_val h; rfl) (by simp) (by reg_val h) rfl (by omega) (by omega) (by reg_val h)
        (by omega) (by omega) (by reg_val h)
        (reg_qrow1 (i := i) hpre rfl (reg_of h (by live_dec)) (by omega) (by omega))
        (reg_head (i := i) hpre rfl (reg_of h (by live_dec)) (by omega))
        (reg_batch (i := i) hpre rfl (reg_of h (by live_dec)) (by omega))
        (by omega) (by omega) (by omega) (by omega) (by omega) (by reg_val h)
      exact ⟨a, sp, hk, fun _ => hci _ rfl (by copy_close) (by copy_close) (by copy_close)⟩
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_5)
      obtain ⟨a, sp, hk, hci⟩ := copy_ev hpre hg hf (kd := 117760) (o' := 0) (k := 8) (x0 := 64)
        (x1 := 512 * (coordsOf L (workOf L g i)).2.2 + 128 * rank L g + 256 * 1)
        (by reg_val h; rfl) (by simp) (by reg_val h) rfl (by omega) (by omega) (by reg_val h)
        (by omega) (by omega) (by reg_val h)
        (reg_qrow1 (i := i) hpre rfl (reg_of h (by live_dec)) (by omega) (by omega))
        (reg_head (i := i) hpre rfl (reg_of h (by live_dec)) (by omega))
        (reg_batch (i := i) hpre rfl (reg_of h (by live_dec)) (by omega))
        (by omega) (by omega) (by omega) (by omega) (by omega) (by reg_val h)
      exact ⟨a, sp, hk, fun _ => hci _ rfl (by copy_close) (by copy_close) (by copy_close)⟩
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_6)
      obtain ⟨a, sp, hk, hci⟩ := copy_ev hpre hg hf (kd := 16384 * snext s) (o' := 134144)
        (k := 32 + 8 * snext s) (x0 := 64 * rank L g) (x1 := 128 * (n L - 1))
        (by reg_val h; rfl) (by simp) (by reg_val h) rfl (by omega) (by omega) (by reg_val h)
        (by omega) (by omega) (by reg_val h) (by reg_val h)
        (reg_head (i := i) hpre rfl (reg_of h (by live_dec)) (by omega))
        (reg_batch (i := i) hpre rfl (reg_of h (by live_dec)) (by omega))
        (by omega) (by omega) (by omega) (by omega) (by omega) (by reg_val h)
      exact ⟨a, sp, hk, fun hR => hci _ rfl (by copy_close) (by copy_close) (by copy_close)⟩
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_7)
      have htr : tt + 2 ≤ n L := hi.trip rfl
      obtain ⟨a, sp, hk, hci⟩ := copy_ev hpre hg hf (kd := 16384 * s) (o' := 134144)
        (k := 32 + 8 * s) (x0 := 0) (x1 := 128 * (n L - 2 - tt) + 64 * rank L g)
        (by reg_val h; rfl) (by simp) (by reg_val h) rfl (by omega) (by omega) (by reg_val h)
        (by omega) (by omega) (by reg_val h) (by reg_val h)
        (reg_head (i := i) hpre rfl (reg_of h (by live_dec)) (by omega))
        (reg_batch (i := i) hpre rfl (reg_of h (by live_dec)) (by omega))
        (by omega) (by omega) (by omega) (by omega) (by omega) (by reg_val h)
      exact ⟨a, sp, hk, fun hR => hci _ rfl (by copy_close) (by copy_close) (by copy_close)⟩
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_8)
      have htr : tt + 2 ≤ n L := hi.trip rfl
      obtain ⟨a, sp, hk, hci⟩ := copy_ev hpre hg hf (kd := 16384 * s) (o' := 142336)
        (k := 32 + 8 * s) (x0 := 64) (x1 := 128 * (n L - 2 - tt) + 64 * rank L g)
        (by reg_val h; rfl) (by simp) (by reg_val h) rfl (by omega) (by omega) (by reg_val h)
        (by omega) (by omega) (by reg_val h) (by reg_val h)
        (reg_head (i := i) hpre rfl (reg_of h (by live_dec)) (by omega))
        (reg_batch (i := i) hpre rfl (reg_of h (by live_dec)) (by omega))
        (by omega) (by omega) (by omega) (by omega) (by omega) (by reg_val h)
      exact ⟨a, sp, hk, fun hR => hci _ rfl (by copy_close) (by copy_close) (by copy_close)⟩
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_9)
      have htr : tt + 2 ≤ n L := hi.trip rfl
      obtain ⟨a, sp, hk, hci⟩ := copy_ev hpre hg hf (kd := 16384 * snext s) (o' := 134144)
        (k := 32 + 8 * snext s) (x0 := 64 * rank L g) (x1 := 128 * (n L - 2 - tt))
        (by reg_val h; rfl) (by simp) (by reg_val h) rfl (by omega) (by omega) (by reg_val h)
        (by omega) (by omega) (by reg_val h) (by reg_val h)
        (reg_head (i := i) hpre rfl (reg_of h (by live_dec)) (by omega))
        (reg_batch (i := i) hpre rfl (reg_of h (by live_dec)) (by omega))
        (by omega) (by omega) (by omega) (by omega) (by omega) (by reg_val h)
      exact ⟨a, sp, hk, fun hR => hci _ rfl (by copy_close) (by copy_close) (by copy_close)⟩
  | exit =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
    simp only [eventTmpl, Fires] at hf
    obtain ⟨rfl, -⟩ := hf
    rfl

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Loader
