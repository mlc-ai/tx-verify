-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Origin
public import Lemmas.Flow.Step.SiteShape
public import Lemmas.Flow.Step.ShapeRegs
public import Lemmas.Flow.Step.TcFields
public import Lemmas.Flow.Step.TcDesc

@[expose] public section

/-! # The MMA warp's events by state: the table

The event a state of the MMA warp fires is the event of its site (`Ev`): the election (full mask),
the two `.nc` length reads, undefined behaviour at the trap, a TMA tensor copy of the Q tile on
`bar_q_tma` moving 8192 bytes (the query map's box `QBox`, `Pre.mapQBind`) to byte `8192 k`
from the origin `(64 k, 0, %ctaid.x, %ctaid.y)`,
the `expect_tx 65536` arrival
and the poll of `bar_q_tma` with parity 0, the Tensor Core fences, the `tcgen05.cp` of shape
`128x256b` to column `cpCol k` from the descriptor word `cpW k`, the commit to `bar_q_utccp`
and its poll with parity 0, per block the poll of `bar_dequant_ready` of the phase with the parity
word, an MMA with its Tensor Memory operands and shared descriptor words (`MmaEv`: QK `k` writes
D at 400 from A at `cpCol k`, accumulating from `k = 1`, B `qkBW`; PV `k` writes D at `pvCol k`
from shared A `pvAW`, B `pvBW`), the commit to `bar_qk_done` of the phase, the poll of
`bar_so_ready` of the phase, the commit to `bar_sv_done` of the phase, the barrier `12` of the whole
CTA and the exit. An address-reading event may instead fault (`ub`). The objects are the shared
words of the registers (`smLoc`): `Ref.lean` names their families. The obligations are
`Shape*.lean`, one declaration per site family, joined in `Shape.lean` (`shape`); `shape_open` opens
one site's obligation. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

/-- The shared words of the role's mbarriers (`%r811`, `%r843`, and the loop's `%r855`, `%r877`,
`%r878`, `%r883` of the phase). -/
abbrev qTmaW (L : Launch) : BitVec 64 := addi (sbw L) 222776
abbrev qUtccpW (L : Launch) : BitVec 64 := addi (sbw L) 222784
abbrev readyW (L : Launch) (pha : BitVec 64) : BitVec 64 := addi (bb L pha) 222792
abbrev qkW (L : Launch) (pha : BitVec 64) : BitVec 64 := addi (bb L pha) 222904
abbrev soW (L : Launch) (pha : BitVec 64) : BitVec 64 := addi (bb L pha) 222920
abbrev svW (L : Launch) (pha : BitVec 64) : BitVec 64 := addi (bb L pha) 222936
/-- The block loop's parity word (`%r879`). -/
abbrev parW (par : BitVec 64) : BitVec 64 := andi (zext16 par) 255

/-- A poll of the word `x` with the parity of the word `q`, or undefined behaviour. -/
def PollEv (L : Launch) (g : Nat) (x q : BitVec 64) (e : Event) : Prop :=
  (∃ ok, e.kind = .wait (smLoc L g x 0) ((truncBits 32 q).toNat % 2) ok true .cta) ∨
    ∃ f, e.kind = .ub f

/-- A Tensor Core commit to the word `x`, its only target, or undefined behaviour. -/
def CommitEv (L : Launch) (g : Nat) (x : BitVec 64) (e : Event) : Prop :=
  (∃ s, e.kind = .tc (.commit s) ∧ s.mbar = smLoc L g x 0 ∧ s.group = .one ∧
    ∀ rank l, TcCommit.target s rank = some l → l = s.mbar) ∨ ∃ f, e.kind = .ub f

/-- The Tensor Memory column of copy `k` of the query and of QK MMA `k`'s A (`%r362`,
`%r371`–`%r384`, `%r400`, `%r403`–`%r418`): `256 + 8 k`. -/
abbrev cpCol (k : Nat) : Nat := 256 + 8 * k
/-- The D column of the score (QK) MMAs (`%r399`). -/
abbrev qkCol : Nat := 400
/-- The D column of PV MMA `k` (`%r402` = 0, `%r424` = 128, alternating). -/
abbrev pvCol (k : Nat) : Nat := 128 * (k % 2)
/-- The instruction descriptor words of the QK MMAs (`%r401`: M 64, N 128) and the PV MMAs
(`%r422`: M 64, N 256). -/
abbrev qkIdesc : Nat := 69207184
abbrev pvIdesc : Nat := 71369872

/-- The shared descriptor words: QK MMA `k`'s B (`%rd88` advanced by `qkOff k`), PV MMA `k`'s B
(`%rd105` advanced by `pvOff k`), PV MMA `k`'s A (`%rd104` advanced by `pvAOff k`) and copy `k`'s
source (`%rd87` with `cpOff k`). -/
def pvAOff (k : Nat) : Int := [0, 0, 128, 128, 256, 256, 384, 384].getD k 0
def qkBW (L : Launch) (pha : BitVec 64) (k : Nat) : BitVec 64 :=
  if k = 0 then kd L pha else join (addi (lo32 (kd L pha)) (qkOff k)) (hi32 (kd L pha))
def pvBW (L : Launch) (pha : BitVec 64) (k : Nat) : BitVec 64 :=
  if k = 0 then vd L pha else join (addi (lo32 (vd L pha)) (pvOff k)) (hi32 (vd L pha))
def pvAW (L : Launch) (k : Nat) : BitVec 64 :=
  if k / 2 = 0 then rd104 L else join (addi (lo32 (rd104 L)) (pvAOff k)) (hi32 (rd104 L))
def cpW (L : Launch) (k : Nat) : BitVec 64 :=
  if k = 0 then ori64 (rd87 L) (cpOff 0) else addi64 (rd87 L) (cpOff k)

/-- A `.ws` `cta_group::1` `kind::f16` MMA issue with D at column `c`, A at `aT` (none: in shared
memory), the descriptor of the word `i`, the issuing CTA's group, accumulate flag `acc`, every
output lane enabled and the shared descriptors of the words `aw`, `bw`; or undefined
behaviour. -/
def MmaEv (L : Launch) (g c : Nat) (aT : Option Nat) (i : Nat) (acc : Bool) (aw bw : Nat)
    (e : Event) : Prop :=
  (∃ s, e.kind = .tc (.mma c s acc [0, 0, 0, 0]) ∧ s.aTmem = aT ∧
    TcMma.decode .one true .f16 i = some s.descriptor ∧
    (∃ ctas, L.ctaGroup (g / L.block) s.descriptor.group = some ctas ∧
      ctas.head? = some s.lowCta ∧ ctas.getLast? = some s.highCta) ∧
    TcShared.decode aw = some s.a ∧ TcShared.decode bw = some s.b) ∨ ∃ f, e.kind = .ub f

/-- PV MMA `k`'s accumulate flag: the block counter is nonzero for the first two, set after. -/
def pvAcc (cnt : BitVec 64) (k : Nat) : Bool :=
  if k < 2 then scmpi .ne .b (sel (scmpi .ne .b cnt 0) (i32 1) (i32 0)) 0 else true

/-- The query map's box: 64 two-byte columns by 64 rows, 128-byte swizzle. -/
def QBox {n : Nat} (d : TensorDescriptor.Descriptor n) : Prop :=
  TensorTile.count d.box 0 = 64 ∧ TensorTile.rows d.box = 64 ∧ d.format.bytes = 2 ∧
    d.swizzle = .b128

/-- The event kind of each site. -/
def EvK (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  match d.site with
  | .elect => (∃ inst ld, e.kind = .elect (2 ^ 32 - 1) inst ld) ∨ ∃ f, e.kind = .ub f
  | .loadTopk | .loadExtra => (∃ a bs, e.kind = .nc a bs) ∨ ∃ f, e.kind = .ub f
  | .trap => ∃ f, e.kind = .ub f
  | .qLoad k =>
      (∃ a s, e.kind = .tensorIssue a s ∧ s.mbar = smLoc L g (qTmaW L) 0 ∧
        TensorTransfer.bytes s.descriptor = 8192 ∧
        s.sharedBase = ⟨.shared, g / L.block, L.sharedBase + 8192 * k.val⟩ ∧ QBox s.descriptor ∧
        (∃ b, L.paramObjects (param "1") = some (mapParam, b) ∧
          L.tensorMaps (b + 128) = some ⟨s.outer, s.descriptor⟩) ∧
        s.rows = none ∧ BoxOrigin s.origin [64 * k.val, 0, ctaidX L g, ctaidY L g]) ∨
        ∃ f, e.kind = .ub f
  | .qArrive => e.kind = .arrive (smLoc L g (qTmaW L) 0) 65536 1 true .cta
  | .qWait => PollEv L g (qTmaW L) (i32 0) e
  | .qCopyWait => PollEv L g (qUtccpW L) (i32 0) e
  | .qFence | .qCopyFence | .kvFence | .soFence => e.kind = .tc .fenceAfter
  | .qCopy k =>
      (∃ s, e.kind = .tc (.cp s) ∧ s.shape = .s128x256b ∧ s.fmt = none ∧ s.address = cpCol k ∧
        L.ctaGroup (g / L.block) .one = some s.ctas ∧
        TcShared.decode (cpW L k).toNat = some s.src) ∨ ∃ f, e.kind = .ub f
  | .qCopyCommit => CommitEv L g (qUtccpW L) e
  | .kvWait => PollEv L g (readyW L d.pha) (parW d.par) e
  | .soWait => PollEv L g (soW L d.pha) (parW d.par) e
  | .qk k => MmaEv L g qkCol (some (cpCol k)) qkIdesc (k.val != 0) (qkBW L d.pha k).toNat
      (qkBW L d.pha k).toNat e
  | .pv k => MmaEv L g (pvCol k) none pvIdesc (pvAcc d.cnt k) (pvAW L k).toNat
      (pvBW L d.pha k).toNat e
  | .qkCommit => CommitEv L g (qkW L d.pha) e
  | .pvCommit => CommitEv L g (svW L d.pha) e
  | .outBar => e.kind = .bar 12 none .sync
  | .exit => e.kind = .exit
  | .leave _ => True

/-- **The event-shape table of the MMA warp**: the site's pc and kind. -/
def Ev (L : Launch) (g : Nat) (d : D) (e : Event) : Prop := e.pc = d.site.pc ∧ EvK L g d e

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- A role mbarrier word at a multiple of 8 above the shared base is 8-byte aligned. -/
theorem sbw_m8 (hp : Pre P L m) {c : Nat} (hc : c % 8 = 0) :
    (truncBits 32 (truncBits 32 (addi (sbw L) c) + BitVec.ofInt 64 0)).toNat % 8 = 0 := by
  have h1 := hp.sharedAlignment
  have h2 := hp.sharedBase
  have h3 := hp.sharedRange
  unfold sharedBytes at h3
  simp only [addi, r32, i32, sbw, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add,
    BitVec.toNat_ofInt]
  omega

/-- A cluster-addressed mbarrier register holding a 32-bit word: the object at `smLoc` of the
thread's CTA when the address is a multiple of 8. -/
theorem mbarClusterLoc_bits {t : TState} {r : Nat} {x : BitVec 64}
    (hr : t.regs r = some (.bits 32 x))
    (h8 : (truncBits 32 (truncBits 32 x + BitVec.ofInt 64 0)).toNat % 8 = 0) :
    mbarClusterLoc L g t r 0 = .ok (smLoc L g x 0) := by
  simp [mbarClusterLoc, sharedEffAddr, readReg, readBits, hr, smLoc, bind, Except.bind,
    pure, Except.pure]
  simpa using h8

/-- A `.nc` load: its read, or undefined behaviour. -/
theorem fires_ncLoad_kind {A : List Assumption} {t : TState} {sp : Space} {w : Nat}
    {ds : List Nat} {base : Nat} {off : Int} {pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (loadTmpl A L g t sp true w ds base off) e o) :
    (∃ a bs, e.kind = .nc a bs) ∨ ∃ f, e.kind = .ub f := by
  simp only [loadTmpl, ↓reduceIte] at hf
  split at hf
  · simp only [Fires] at hf
    exact .inr ⟨_, congrArg Event.kind hf.1⟩
  · split at hf
    · simp only [Fires] at hf
      obtain ⟨bs, -, he, -⟩ := hf
      exact .inl ⟨_, bs, congrArg Event.kind he⟩
    · simp only [Fires] at hf
      exact .inr ⟨_, congrArg Event.kind hf.1⟩

/-- An MMA's fields from the operand lemmas (`fires_tcMma*_fields`, `fires_tcMma*_desc`), the
words evaluated. -/
theorem mmaEv_of {e : Event} {c i aw bw : Nat} {aT aT' : Option Nat} {acc : Bool}
    {vd vi : BitVec 64} {ms : List Nat}
    (h : (∃ s, e.kind = .tc (.mma vd.toNat s acc ms) ∧ s.aTmem = aT' ∧
      TcMma.decode .one true .f16 vi.toNat = some s.descriptor ∧
      ∃ ctas, L.ctaGroup (g / L.block) s.descriptor.group = some ctas ∧
        ctas.head? = some s.lowCta ∧ ctas.getLast? = some s.highCta) ∨ ∃ f, e.kind = .ub f)
    (hD : ∀ {c s acc ms}, e.kind = .tc (.mma c s acc ms) →
      TcShared.decode aw = some s.a ∧ TcShared.decode bw = some s.b)
    (hc : vd.toNat = c) (ha : aT' = aT) (hi : vi.toNat = i) (hms : ms = [0, 0, 0, 0]) :
    MmaEv L g c aT i acc aw bw e := by
  subst hc ha hi hms
  rcases h with ⟨s, h1, h2, h3, h4⟩ | h
  · exact .inl ⟨s, h1, h2, h3, h4, hD h1⟩
  · exact .inr h

/-- A 64-bit register read of a 64-bit word the facts give. -/
theorem readBits64_of {t : TState} {r : Nat} {x : BitVec 64} (h : t.regs r = some (.bits 64 x)) :
    readBits L g t 64 (.reg r) = .ok x := by
  have hx : x.toNat % 18446744073709551616 = x.toNat := Nat.mod_eq_of_lt x.isLt
  simp [readBits, readReg, h, bind, Except.bind, pure, Except.pure, truncBits, hx]

/-- A register read of a word the facts give. -/
theorem readBits_of {t : TState} {r w : Nat} {x : BitVec 64} (h : t.regs r = some (.bits w x)) :
    readBits L g t 32 (.reg r) = .ok (truncBits 32 x) := by
  simp [readBits, readReg, h, bind, Except.bind, pure, Except.pure]

/-- The four output-lane mask words `0`. -/
theorem mask0_read {t : TState} :
    [Opnd.imm 0, .imm 0, .imm 0, .imm 0].mapM (readBits L g t 32) = .ok [0, 0, 0, 0] := rfl

/-- The form of the role's MMAs: `.ws`, `cta_group::1`, `kind::f16`, a register descriptor and
enable predicate, the masks `0`. -/
structure MmaForm (m : TcMmaInstr) (rI re : Nat) : Prop where
  rule : m.rule = some .threadTc
  group : m.group = .one
  ws : m.ws = true
  kind : m.kind = .f16
  idesc : m.idesc = .reg rI
  enable : m.enableD = .reg re
  mask : m.mask = [.imm 0, .imm 0, .imm 0, .imm 0]

/-- **An MMA with A in Tensor Memory at `[ta]`**: its fields from the register facts. -/
theorem mmaTmem_ev {A : List Assumption} {t : TState} {m : TcMmaInstr} {ta rI re rb : Nat}
    {xd xa xi xb : BitVec 64} {acc : Bool} {pc : Nat} {e : Event} {o : Option TState}
    {c a i : Nat} {wb : BitVec 64}
    (hf : Fires pc (eventTmpl A L g t (.tcMma m)) e o) (hF : MmaForm m rI re)
    (hmA : m.a = .tmem ta 0) (hmB : m.bdesc = .reg rb)
    (hd : t.regs m.d = some (.bits 32 xd)) (hA : t.regs ta = some (.bits 32 xa))
    (hI : t.regs rI = some (.bits 32 xi)) (he : t.regs re = some (.pred acc))
    (hB : t.regs rb = some (.bits 64 xb)) (hw : xb = wb)
    (hc : (truncBits 32 xd).toNat = c) (ha : (truncBits 32 xa).toNat = a)
    (hi : (truncBits 32 xi).toNat = i) : MmaEv L g c (some a) i acc wb.toNat wb.toNat e := by
  have hD := fun {c s acc ms} (hk : e.kind = .tc (.mma c s acc ms)) =>
    fires_tcMmaTmem_desc (vb := wb) hF.rule hmA (by rw [hmB, ← hw]; exact readBits64_of hB) hf hk
  have h := fires_tcMmaTmem_fields hF.rule hmA hF.idesc (readBits_of hd) (readBits_of hA)
    (tmemOffset_zero _) (readBits_of hI) (by rw [hF.mask]; exact mask0_read)
    (by rw [hF.enable]; exact mmaEnable_of he) hf
  rw [hF.group, hF.ws, hF.kind] at h
  exact mmaEv_of h hD hc (by rw [ha]) hi rfl

/-- **An MMA with A in shared memory**: its fields from the register facts. -/
theorem mmaSmem_ev {A : List Assumption} {t : TState} {m : TcMmaInstr} {ra rI re rb : Nat}
    {xd xi xa xb : BitVec 64} {acc : Bool} {pc : Nat} {e : Event} {o : Option TState}
    {c i : Nat} {wa wb : BitVec 64}
    (hf : Fires pc (eventTmpl A L g t (.tcMma m)) e o) (hF : MmaForm m rI re)
    (hmA : m.a = .smem (.reg ra)) (hmB : m.bdesc = .reg rb)
    (hd : t.regs m.d = some (.bits 32 xd)) (hI : t.regs rI = some (.bits 32 xi))
    (he : t.regs re = some (.pred acc))
    (hA : t.regs ra = some (.bits 64 xa)) (hB : t.regs rb = some (.bits 64 xb))
    (hwa : xa = wa) (hwb : xb = wb)
    (hc : (truncBits 32 xd).toNat = c) (hi : (truncBits 32 xi).toNat = i) :
    MmaEv L g c none i acc wa.toNat wb.toNat e := by
  have hD := fun {c s acc ms} (hk : e.kind = .tc (.mma c s acc ms)) =>
    fires_tcMmaSmem_desc (va := wa) (vb := wb) hF.rule hmA (by rw [← hwa]; exact readBits64_of hA)
      (by rw [hmB, ← hwb]; exact readBits64_of hB) hf hk
  have h := fires_tcMmaSmem_fields hF.rule hmA hF.idesc (readBits_of hd) (readBits_of hI)
    (by rw [hF.mask]; exact mask0_read) (by rw [hF.enable]; exact mmaEnable_of he) hf
  rw [hF.group, hF.ws, hF.kind] at h
  exact mmaEv_of h hD hc rfl hi rfl

/-- **A `128x256b` copy to `[ta]`**: its fields from the register fact. -/
theorem cp_ev {A : List Assumption} {t : TState} {ta rs : Nat} {x xs w : BitVec 64}
    {pc : Nat} {e : Event} {o : Option TState} {c : Nat}
    (hf : Fires pc (eventTmpl A L g t (.tcCp .one .s128x256b ta (.reg rs) none)) e o)
    (hA : t.regs ta = some (.bits 32 x)) (hS : t.regs rs = some (.bits 64 xs)) (hw : xs = w)
    (hc : (truncBits 32 x).toNat = c) :
    (∃ s, e.kind = .tc (.cp s) ∧ s.shape = .s128x256b ∧ s.fmt = none ∧ s.address = c ∧
        L.ctaGroup (g / L.block) .one = some s.ctas ∧ TcShared.decode w.toNat = some s.src) ∨
      ∃ f, e.kind = .ub f := by
  rcases fires_tcCp_fields (readBits_of hA) hf with ⟨s, h1, h2, h3, h4, h5⟩ | h
  · exact .inl ⟨s, h1, h2, h3, h4.trans hc, h5,
      fires_tcCp_desc (vs := w) (by rw [← hw]; exact readBits64_of hS) hf h1⟩
  · exact .inr h

set_option hygiene false in
/-- Open the shape obligation of a concrete site: the facts `hF`, the pc `hpc`, the instruction
by its lookup, and the table's row. -/
macro "shape_open" : tactic => `(tactic| (
  intro t ins e o hat _ hc hf
  obtain ⟨hpc, -, -, -, hF⟩ := hat
  try dsimp only [Flow.Code.AtD, code, facts, Site.pc, Fin.isValue, Fin.val_zero, Fin.val_one,
    Fin.val_two] at hpc hc hF ⊢
  try simp only [Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.reduceLT, Nat.reduceEqDiff,
    Fin.isValue, Fin.val_ofNat, Nat.reduceMod] at hpc hc hF ⊢
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  try simp only [EvK, PollEv, CommitEv]))

set_option hygiene false in
/-- A register's fact at an opened site. -/
macro "rg " r:num : term => `(regs_of_factsFrom hF (r := $r) (by decide))

set_option hygiene false in
/-- A register's fact at an opened site, the register found by unification. -/
macro "rg_" : term => `(regs_of_factsFrom hF (by decide))

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
