-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Origin
public import Lemmas.Flow.Step.SiteShape
public import Lemmas.Flow.Step.ShapeRegs
public import Lemmas.Flow.Step.ShapeNc
public import Lemmas.Flow.TcAddr
public import Lemmas.Flow.Step.ShapeAccAt
public import Lemmas.Flow.TensorStoreSrc
public import Lemmas.Flow.Store
public import Lemmas.Flow.TensorStoreOrigin
public import Lemmas.TensorStore.TensorStoreThread
public import Lemmas.Flow.TensorIssueCopy
public import Lemmas.Flow.Step.GenericShared

@[expose] public section

/-! # Warpgroup 0's events by state: the table

The event a state of warpgroup 0's control machine fires is the event of its site (`Ev`):

* the mbarrier events with their objects, the shared words of the state's registers (`smLoc`):
  the arrival on the last-store barrier (pc 200, `arrW`), per block the polls of the valid-mask
  slot `vs` with the parity word `pv` (264) and of the QK slot `sl` with the parity word `ps`
  (272), the arrival freeing the valid-mask slot (571) and the arrival on the softmax-ready slot
  `sl` (1122); after the loop the poll of the SV slot `sl` with the parity word `ps` (1184). An
  arrival is one release arrival of count 1 expecting no bytes; a poll is a CTA-scoped acquire.
  Either may instead fault (a misaligned address: `ub`);
* the named barriers with their ids and thread counts: barrier 9 of the four warps (128 threads)
  at the loop's head, the row exchange, the epilogue's exchange and every output chunk; barrier
  `10 + w % 2` of the warp pair (64 threads, `barW`) in the peer exchange; barrier 12 of the CTA
  at the end;
* the Tensor Memory loads and stores with their first columns, all of shape `32x32b`: the score
  loads at columns 400 and 432, the rescale arm's loads and stores and the output loads at
  column `64 c` of chunk `c`; their waits and the `tcgen05` fences;
* the TMA tensor stores of the output chunks, the bulk commit and the bulk wait, the election,
  the vote, the deallocation, the `setmaxnreg` and the exit;
* the shared reads and writes through control address registers with their exact footprints
  (`RdAt`, `WrAt`: the register's word plus the instruction's offset, the element's width and
  index): the valid-mask word (`vm`), the peer stores and reads (`pst k` at `pstW`, `pld k`),
  the row-maximum and row-sum exchange (`mst`, `est` at `%r13`; `mld`, `eld` at `%r14`), the P
  stores (`ost k` at `%r16`); payloads existential;
* the other data accesses (`ld.global.nc`, the LSE's global write, the staging stores) with
  existential addresses and payloads.

The obligations are `ShapeLoop.lean`, `ShapeEpi.lean` (one declaration per site family), joined
in `Shape.lean` (`shape`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

/-! ### The objects -/

/-- The shared words of the role's mbarriers: the last-store barrier (`%r480`), the valid-mask
ring's ready and free slots of the slot word `vs` (`%r516`, `%r542`), the QK, softmax-ready and
SV slots of the slot word `sl` (`%r519`, `%r1259`, `%r1278`). -/
abbrev arrW (L : Launch) : BitVec 64 := addi (sbw L) 222768
abbrev vReadyW (L : Launch) (d : D) : BitVec 64 := addi (r19W L d) 222840
abbrev vFreeW (L : Launch) (d : D) : BitVec 64 := addi (r19W L d) 222872
abbrev qkW (L : Launch) (d : D) : BitVec 64 := addi (r20W L d) 222904
abbrev soW (L : Launch) (d : D) : BitVec 64 := addi (r20W L d) 222920
abbrev svW (L : Launch) (d : D) : BitVec 64 := addi (r20W L d) 222936

/-- The peer exchange's named barrier word (`%r538`, pc 475): `10` or `11` by the warp pair. -/
abbrev barW (w : BitVec 64) : BitVec 64 := truncBits 32 (or32 (andi w 1) (i32 10))

/-- The peer store `k`'s word (`%r530 + k`, pcs 226–233): the other warp pair's quadrant. -/
abbrev pstW (L : Launch) (g : Nat) (w : BitVec 64) (k : Fin 8) : BitVec 64 :=
  addi (r507W L g w) (204800 + 512 * (k.val : Int))

/-- The offset of output chunk `c`'s TMA source from the warp's staging tile (`%r1455`,
`%r1624`, `%r1793`, `%r1963`). -/
def otmaOff (c : Fin 4) : Int := [65536, 73728, 98304, 106496].getD c.val 0

/-- The first output column of chunk `c` of the warp `w` (`w ≤ 1`): `128 w + otmaCol c`, the
coordinate registers `%r1914`, `%r2083`, `%r2252`, `%r2422`. -/
def otmaCol (c : Fin 4) : Nat := [0, 64, 256, 320].getD c.val 0

/-- The offset of output chunk `c`'s staging stores from the staging pointers. -/
def ost2Off (c : Fin 4) : Nat := [0, 8192, 32768, 40960].getD c.val 0

/-- Output chunk `c`'s TMA source word. -/
abbrev otmaW (L : Launch) (w : BitVec 64) (c : Fin 4) : BitVec 64 := addi (r25W L w) (otmaOff c)

/-! ### The event classes -/

/-- A poll of the word `x` with the parity of the word `q`, or undefined behaviour. -/
def PollEv (L : Launch) (g : Nat) (x q : BitVec 64) (e : Event) : Prop :=
  (∃ ok, e.kind = .wait (smLoc L g x 0) ((truncBits 32 q).toNat % 2) ok true .cta) ∨
    ∃ f, e.kind = .ub f

/-- One release arrival on the word `x`, expecting no bytes, or undefined behaviour. -/
def ArrEv (L : Launch) (g : Nat) (x : BitVec 64) (e : Event) : Prop :=
  e.kind = .arrive (smLoc L g x 0) 0 1 true .cta ∨ ∃ f, e.kind = .ub f

/-- A `32x32b` Tensor Memory load at column `a`, or undefined behaviour. -/
def TcLdEv (a : Nat) (e : Event) : Prop :=
  (∃ vals, e.kind = .tc (.ld a vals .s32x32b)) ∨ ∃ f, e.kind = .ub f

/-- A `32x32b` Tensor Memory store at column `a`, or undefined behaviour. -/
def TcStEv (a : Nat) (e : Event) : Prop :=
  (∃ vals, e.kind = .tc (.st a vals .s32x32b)) ∨ ∃ f, e.kind = .ub f

/-- A non-coherent read, or undefined behaviour. -/
def NcEv (e : Event) : Prop := (∃ a bs, e.kind = .nc a bs) ∨ ∃ f, e.kind = .ub f

/-- The proxy fence of the output (`fence.proxy.async.shared::cta`). -/
abbrev proxyK : ProxyFence := .async (some (.shared .cta))

/-- **The event kind of each site** (for the warp word `w`). -/
def EvK (P : Params) (L : Launch) (g : Nat) (w : BitVec 64) (d : D) (e : Event) : Prop :=
  match d.site with
  | .smr => ∃ inst, e.kind = .setMaxReg true 224 inst
  | .sink | .lenA | .lenB => NcEv e
  | .bwait => e.kind = .bulkWait .read 0
  | .arrL => ArrEv L g (arrW L) e
  | .bar0 | .bar2 | .ebar0 | .ebar1 | .obar _ => e.kind = .bar 9 (some 128) .sync
  | .bar1 => e.kind = .bar (barW w).toNat (some 64) .sync
  | .ebar => e.kind = .bar 12 none .sync
  | .wv => PollEv L g (vReadyW L d) (parW d.pv) e
  | .wq => PollEv L g (qkW L d) (parW d.ps) e
  | .wsv => PollEv L g (svW L d) (parW d.ps) e
  | .arrV => ArrEv L g (vFreeW L d) e
  | .arrS => ArrEv L g (soW L d) e
  | .tcfa | .rsf | .efa => e.kind = .tc .fenceAfter
  | .tcfb | .rsfb => e.kind = .tc .fenceBefore
  | .sld _ k => TcLdEv (400 + 32 * k.val) e
  | .rld c | .old c => TcLdEv (64 * c.val) e
  | .rst c => TcStEv (64 * c.val) e
  | .sldw | .rldw _ | .oldw _ => e.kind = .tc .waitLd
  | .rstw _ => e.kind = .tc .waitSt ∨ ∃ f, e.kind = .ub f
  | .vm => RdAt L g (add32 (r19W L d) (r18W w)) 221696 4 0 e
  | .pld k => d.el < 2 ∧ RdAt L g (r17W L g w) (204800 + 512 * (k.val : Int)) 8 d.el e
  | .mld | .eld => RdAt L g (r14W L g) 221184 4 0 e
  | .pst k => WrAt L g (pstW L g w k) 0 16 0 e
  | .mst | .est => WrAt L g (r13W L g) 221184 4 0 e
  | .ost k => d.el < 4 ∧ WrAt L g (r16W L g w) (204800 + 1024 * (k.val : Int)) 4 d.el e
  | .lse => GWrAt (lseAddr P L g) 4 e
  | .ost2 c k => d.el < 4 ∧ GenWrAt L g (stW L g k.val) (ost2Off c) 4 d.el e
  | .vote => (∃ p r, e.kind = .voteMode .any (2 ^ 32 - 1) p r) ∨ ∃ f, e.kind = .ub f
  | .fpx | .ofpx _ => e.kind = .fenceProxy proxyK none
  | .oel _ => (∃ inst ld, e.kind = .elect (2 ^ 32 - 1) inst ld) ∨ ∃ f, e.kind = .ub f
  | .otma c => (∃ a s, e.kind = .tensorStore a s ∧ s.sharedBase = smLoc L g (otmaW L w c) 0 ∧
      a = (W (P.param1Base + 512)).toNat ∧ ∃ d, L.tensorMaps a = some ⟨s.outer, d⟩ ∧
        s.descriptor = d ∧ (w.toNat < 2 → s.rows = none ∧
          BoxOrigin s.origin [128 * w.toNat + otmaCol c, 0, ctaidX L g, ctaidY L g])) ∨
      ∃ f, e.kind = .ub f
  | .commit => e.kind = .bulkCommit
  | .dealloc => e.kind = .tc (.resource .one none (.dealloc 0 512)) ∨ ∃ f, e.kind = .ub f
  | .exit => e.kind = .exit

/-- **The event-shape table of warpgroup 0**: the site's pc and kind. -/
def Ev (P : Params) (L : Launch) (g : Nat) (w : BitVec 64) (d : D) (e : Event) : Prop :=
  e.pc = d.site.pc ∧ EvK P L g w d e

/-! ### Inversion helpers -/

variable {A : List Assumption} {L : Launch} {g : Nat}

/-- The peer barrier's id is a barrier id. -/
theorem barW_lt (w : BitVec 64) : (barW w).toNat < 16 := by
  simp only [barW, or32, andi, r32, i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_or,
    BitVec.toNat_and, BitVec.toNat_ofInt]
  refine Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.lt_of_le_of_lt (Nat.mod_le _ _) ?_)
  refine Nat.or_lt_two_pow (n := 4) ?_ (by decide)
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.lt_of_le_of_lt (Nat.mod_le _ _)
    (Nat.lt_of_le_of_lt Nat.and_le_right (by decide)))

/-- **An arrival names the object at its address register, or faults.** -/
theorem fires_arrive_reg {t : TState} {base pc : Nat} {e : Event} {o : Option TState}
    {x : BitVec 64} {wx : Nat} (hA : A.any (·.clusterScopeMbar t.pc) = false)
    (hb : t.regs base = some (.bits wx x))
    (hf : Fires pc (eventTmpl A L g t
      (.mbarArrive base 0 (.imm 0) (.imm 1) false true .cta none)) e o) :
    e.kind = .arrive (smLoc L g x 0) 0 1 true .cta ∨ ∃ f, e.kind = .ub f := by
  simp only [eventTmpl, widenMbarScope, hA, Bool.false_eq_true, ↓reduceIte, tmaTmpl, mbarLoc,
    effAddr, sharedEffAddr, readReg, hb, readBits, bind, Except.bind, pure, Except.pure,
    ofExec] at hf
  split_ifs at hf with h
  · simp only [Fires] at hf
    exact .inl (by rw [hf.1]; rfl)
  all_goals
    simp only [throw, throwThe, MonadExceptOf.throw, Fires] at hf
    exact .inr ⟨_, congrArg Event.kind hf.1⟩

/-- A `32x32b` Tensor Memory load whose address register holds the column `a`. -/
theorem fires_tcLd_col {t : TState} {ds : List Nat} {ta a pc : Nat} {e : Event}
    {o : Option TState} (hr : t.regs ta = some (b32 a)) (ha : a < 2 ^ 32)
    (hw : A.any (·.tcLdWait t.pc) = false)
    (hf : Fires pc (eventTmpl A L g t (.tcLd ds ta .s32x32b none)) e o) : TcLdEv a e := by
  refine shape_tcLd (P := fun e' => e' = e → TcLdEv a e) hf (by intro s h; cases h) hw
    (fun a' vals he => ?_) (fun f he => .inr ⟨f, by subst he; rfl⟩) rfl
  subst he
  obtain ⟨vals', hv⟩ := fires_tcLd_at hr ha hf ⟨a', vals, .s32x32b, rfl⟩
  exact .inl ⟨vals', by rw [hv]⟩

/-- A `32x32b` Tensor Memory store whose address register holds the column `a`. -/
theorem fires_tcSt_col {t : TState} {ss : List Opnd} {ta a pc : Nat} {e : Event}
    {o : Option TState} (hr : t.regs ta = some (b32 a)) (ha : a < 2 ^ 32)
    (hw : A.any (·.tcStWaitLd t.pc) = false)
    (hf : Fires pc (eventTmpl A L g t (.tcSt ta ss .s32x32b)) e o) : TcStEv a e := by
  refine shape_tcSt (P := fun e' => e' = e → TcStEv a e) hf
    (x := BitVec.ofNat 64 a) hr (by simp only [BitVec.toNat_ofNat]; omega) hw
    (fun a' vals he => ?_) (fun f he => .inr ⟨f, by subst he; rfl⟩) rfl
  subst he
  obtain ⟨rfl, -⟩ := fires_tcSt_at hr ha hf rfl
  exact .inl ⟨vals, rfl⟩

/-- A tensor store whose source register holds `x`: its event reads from `smLoc L g x off`, or
undefined behaviour. -/
theorem fires_tensorStore_at {t : TState} {map : Opnd} {cs : List Opnd} {src : Nat} {off : Int}
    {policy : Option Opnd} {mode : TensorMode} {reduce : Option AtomOp} {pc : Nat} {e : Event}
    {o : Option TState} {x : BitVec 64} (hr : t.regs src = some (.bits 32 x))
    (hf : Fires pc (eventTmpl A L g t (.cpTensorStore map cs src off policy mode reduce)) e o) :
    (∃ a s, e.kind = .tensorStore a s ∧ s.sharedBase = smLoc L g x off) ∨ ∃ f, e.kind = .ub f :=
  (shape_tensorStore (P := fun e' : Event => e' = e → (∃ a s, e.kind = .tensorStore a s) ∨
      ∃ f, e.kind = .ub f) hf (fun a s he => .inl ⟨a, s, by rw [← he]⟩)
      (fun f he => .inr ⟨f, by rw [← he]⟩) rfl).elim
    (fun ⟨a, s, hk⟩ => .inl ⟨a, s, hk, fires_tensorStore_src hr hf hk⟩) .inr

/-- A tile tensor store whose source register holds `x` and whose map register holds `y`: its
event reads from `smLoc L g x off` with the descriptor of the map at `y`, or undefined
behaviour. -/
theorem fires_tensorStore_map {t : TState} {r : Nat} {cs : List Opnd} {src : Nat} {off : Int}
    {policy : Option Opnd} {reduce : Option AtomOp} {pc : Nat} {e : Event}
    {o : Option TState} {x y : BitVec 64} (hr : t.regs src = some (.bits 32 x))
    (hm : t.regs r = some (.bits 64 y))
    (hf : Fires pc (eventTmpl A L g t (.cpTensorStore (.reg r) cs src off policy .tile reduce)) e
      o) :
    (∃ a s, e.kind = .tensorStore a s ∧ s.sharedBase = smLoc L g x off ∧ a = y.toNat ∧
      ∃ d, L.tensorMaps a = some ⟨s.outer, d⟩ ∧ s.descriptor = d) ∨ ∃ f, e.kind = .ub f := by
  rcases fires_tensorStore_at hr hf with ⟨a, s, hk, hs⟩ | h
  · obtain ⟨ha, ⟨d, hd, hdd⟩, -⟩ := fires_cpTensorStore_spec hf a s hk
    rw [tensorMapAddress_bits hm] at ha
    cases ha
    exact .inl ⟨_, s, hk, hs, rfl, d, hd, hdd⟩
  · exact .inr h

/-- **The origin of a tile tensor store** whose four coordinate registers hold the values `x0` to
`x3` below `2 ^ 31`: no gather rows and that origin. -/
theorem tensorStore_origin {t : TState} {r0 r1 r2 r3 x0 x1 x2 x3 : Nat} {map : Opnd} {src : Nat}
    {off : Int} {policy : Option Opnd} {reduce : Option AtomOp} {pc : Nat} {e : Event}
    {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t (.cpTensorStore map [.reg r0, .reg r1, .reg r2, .reg r3] src
      off policy .tile reduce)) e o)
    (h0 : t.regs r0 = some (b32 x0)) (h1 : t.regs r1 = some (b32 x1))
    (h2 : t.regs r2 = some (b32 x2)) (h3 : t.regs r3 = some (b32 x3)) (b0 : x0 < 2 ^ 31)
    (b1 : x1 < 2 ^ 31) (b2 : x2 < 2 ^ 31) (b3 : x3 < 2 ^ 31) {a : Nat} {s : TensorStore.Spec}
    (hk : e.kind = .tensorStore a s) : s.rows = none ∧ BoxOrigin s.origin [x0, x1, x2, x3] := by
  have hok := fires_cpTensorStore_ok hf hk
  obtain ⟨-, -, -, -, -, hr, -⟩ := tensorStoreSpec_ok hok
  exact ⟨hr.mpr rfl, tensorStoreSpec_origin_regs hok h0 h1 h2 h3 b0 b1 b2 b3⟩

set_option hygiene false in
/-- The common part of opening a concrete site: unfold the facts `hF`, the pc `hpc`, look the
instruction up, and unfold the table's row. -/
macro "w0_body" : tactic => `(tactic| (
  try dsimp only [Flow.Code.AtD, code, facts, Site.pc, Fin.isValue, Fin.val_zero, Fin.val_one,
    Fin.val_two, ost2Base, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some] at hpc hc hF ⊢
  try simp only [Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.reduceLT, Nat.reduceEqDiff,
    Fin.isValue, Fin.val_ofNat, Nat.reduceMod] at hpc hc hF ⊢
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  try simp only [EvK]))

set_option hygiene false in
/-- Open the shape obligation of a concrete site: the facts `hF`, the pc `hpc`, the instruction
by its lookup, and the table's row. -/
macro "w0_shape" : tactic => `(tactic| (
  intro t ins e o hat _ hc hf
  obtain ⟨hpc, -, -, -, hF⟩ := hat
  w0_body))

set_option hygiene false in
/-- `w0_shape` keeping the element sub-step `hsub : t.sub = _` and the invariant `hi`. -/
macro "w0_shapeS" : tactic => `(tactic| (
  intro t ins e o hat hi hc hf
  obtain ⟨hpc, hsub, -, -, hF⟩ := hat
  w0_body))

set_option hygiene false in
/-- A register's fact at an opened site. -/
macro "rg " r:num : term => `(regs_of_factsFrom hF (r := $r) (by decide +kernel))

set_option hygiene false in
/-- A register's fact at an opened site, the register found by unification. -/
macro "rg_" : term => `(regs_of_factsFrom hF (by decide +kernel))

set_option hygiene false in
/-- A site's `32x32b` Tensor Memory load at column `a` from address register `r`. -/
macro "w0_tcld " a:num r:num : tactic => `(tactic| (
  w0_shape
  exact fires_tcLd_col (a := $a) (rg $r) (by decide) (by rw [hpc]; decide) hf))

set_option hygiene false in
/-- A site's `32x32b` Tensor Memory store at column `a` from address register `r`. -/
macro "w0_tcst " a:num r:num : tactic => `(tactic| (
  w0_shape
  exact fires_tcSt_col (a := $a) (rg $r) (by decide) (by rw [hpc]; decide) hf))

set_option hygiene false in
/-- A site's barrier 9 of 128 threads, id and count from registers `a` and `b` (`hp` gives the
block's size). -/
macro "w0_bar9 " a:num b:num : tactic => `(tactic| (
  w0_shape
  exact shape_barSyncNR (P := fun e : Event => e.kind = .bar 9 (some 128) .sync) hf
    (readBits_reg (rg $a)) (by decide) (readBits_reg (rg $b)) (by decide) (by decide)
    (by rw [hp.block]; decide) rfl))

set_option hygiene false in
/-- A site's election with the full mask in register `r`. -/
macro "w0_elect " r:num : tactic => `(tactic| (
  w0_shape
  exact shape_elect (P := fun e : Event => (∃ inst ld, e.kind = .elect (2 ^ 32 - 1) inst ld) ∨
    ∃ f, e.kind = .ub f) hf (readBits_reg (rg $r)) (fun inst ld => .inl ⟨inst, ld, rfl⟩)
    (fun f => .inr ⟨f, rfl⟩)))

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
