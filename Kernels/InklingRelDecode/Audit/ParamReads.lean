-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec

@[expose] public section

/-!
# Parameter audit of the Inkling program

`Pre` constrains the 16 scalar parameters the program reads (`readParams`) and the tensor-map
object `param_1`. This file checks that list against the decoded program.

`ParamRef` is a use of a kernel parameter inside an instruction, and `opRefs` collects the uses
of one instruction: every `AddrBase.param` base of an address and every `Opnd.paramSym` operand.
It matches every constructor of `Op` and every operand-carrying structure without a wildcard, so
a new `Op` constructor or `Opnd`/`AddrBase` case is a compile error here. A `ld.param` is a
`.mem` load in the `.param` space from a `param` base (`.read`); any other use of a `param` base
is `.other`; an `unmodeled` instruction is `.unmodeled`.

The program has 17 uses (`refs_eq`): the 16 reads, in program order, and the address of
`param_1` (`mov.b64 %rd77, param_1`). There is no `.other` or `.unmodeled` use, and no access in
the `.param` space through a register (`paramSpace_param_based`). The only parameter address the
program ever forms is that of `param_1` (`syms_eq`), so a register-based access cannot reach any
other parameter. The reads are the names of `Pre` (`reads_perm`), each is read once, and the
width of each is the declared width (`read_widths`).

The check is on the decoded `Op`/`Opnd` structure, not on source text. `readParams` is written
out by hand from the fields of `Pre`; `defines_refs` proves from `Pre` that every parameter use of
the program has a value in the launch.
-/

namespace PTX.Kernels.InklingRelDecode.Audit
open PTX

/-- A use of a kernel parameter by an instruction. -/
inductive ParamRef where
  /-- `ld.param` of `bits` bits at byte `off` of the scalar parameter `name`. -/
  | read (name : String) (off : Int) (bits : Nat)
  /-- The address of the parameter object `name` (`Opnd.paramSym`). -/
  | sym (name : String)
  /-- Any other use of a parameter base: a store, an atomic, a parameter object base, a load in
  another space. -/
  | other (name : String)
  /-- An instruction without a family representation; its operands are not inspected. -/
  | unmodeled
  deriving DecidableEq

/-- The uses in an operand. -/
def opndRefs : Opnd → List ParamRef
  | .paramSym n => [.sym n]
  | .reg _ | .imm _ | .f32imm _ | .sreg _ | .sharedSym _ | .localSym _ => []

def opndsRefs (l : List Opnd) : List ParamRef := l.flatMap opndRefs

def optRefs : Option Opnd → List ParamRef
  | none => []
  | some o => opndRefs o

/-- The uses in an address that is not a `ld.param` source. -/
def addrRefs (a : Addr) : List ParamRef :=
  match a.base with
  | .param n _ => [.other n]
  | .reg .. | .sharedSym _ | .imm _ | .localSym _ | .constSym _ => []

def optAddrRefs : Option Addr → List ParamRef
  | none => []
  | some a => addrRefs a

/-- The uses in a memory access: a load of the `.param` space from a scalar parameter is a read,
every other `param` base is `.other`. -/
def memRefs (a : MemAccess) : List ParamRef :=
  (match a.addr.base with
    | .param n object =>
      if a.kind == .load && a.space == some .param && !object then
        [.read n a.addr.off (a.elem.width * a.vec)]
      else [.other n]
    | .reg .. | .sharedSym _ | .imm _ | .localSym _ | .constSym _ => []) ++
    opndsRefs a.srcs ++ optRefs a.hints.policy

def addrInstrRefs : AddrInstr → List ParamRef
  | .cvta _ _ _ _ a | .isspacep _ _ a | .getctarank _ _ _ a => opndRefs a
  | .mapa _ _ _ a b => opndRefs a ++ opndRefs b
  | .prefetch _ _ _ a | .applypriority _ a => addrRefs a

def policyRefs : PolicyKind → List ParamRef
  | .range _ a p t => addrRefs a ++ opndRefs p ++ opndRefs t
  | .fraction f => optRefs f
  | .cvt a => opndRefs a

def miscRefs : MiscInstr → List ParamRef
  | .createPolicy _ k => policyRefs k
  | .nanosleep t => opndRefs t
  | .pmevent .. | .gridDep _ => []

def fenceRefs : FenceInstr → List ParamRef
  | .thread .. => []
  | .proxy _ _ a => optAddrRefs a

def tcMmaARefs : TcMmaA → List ParamRef
  | .smem d => opndRefs d
  | .tmem .. => []

def tcMmaRefs (m : TcMmaInstr) : List ParamRef :=
  tcMmaARefs m.a ++ opndRefs m.bdesc ++ opndRefs m.idesc ++ opndsRefs m.mask ++
    opndRefs m.enableD ++ optRefs m.zeroColumnMask

def bulkRefs (c : BulkCopy) : List ParamRef :=
  opndRefs c.size ++ optRefs (c.multicast.map (·.2)) ++
    (match c.ignoreOob with
      | none => []
      | some (l, r) => opndRefs l ++ opndRefs r) ++
    optRefs c.cachePolicy ++ optRefs c.mask

def asyncStoreRefs (s : AsyncStore) : List ParamRef :=
  addrRefs s.addr ++ opndsRefs s.srcs ++ optAddrRefs s.mbar

def cpAsyncSrcRefs : CpAsyncSource → List ParamRef
  | .full => []
  | .size n | .ignore n => opndRefs n

/-- The parameter uses of one operation. -/
def opRefs : Op → List ParamRef
  | .prefetchTensorMap _ _ s => opndRefs s
  | .prefetchTensor m cs _ cp => opndRefs m ++ opndsRefs cs ++ optRefs cp
  | .setMaxReg .. => []
  | .int i => opndsRefs i.srcs
  | .move m => opndsRefs m.srcs
  | .cvt c => opndsRefs c.srcs
  | .mem a => memRefs a
  | .addr c => addrInstrRefs c
  | .warp w => opndsRefs w.srcs ++ optRefs w.mask
  | .matrix m => optAddrRefs m.addr ++ opndsRefs m.srcs
  | .misc m => miscRefs m
  | .float f => opndsRefs f.srcs
  | .barSync b _ => opndRefs b
  | .barSyncN b c _ | .barArrive b c _ => opndRefs b ++ opndRefs c
  | .cluster _ | .bra .. | .ret | .exit | .trap => []
  | .brx i _ _ => opndRefs i
  | .cpTensor (map := m) (coords := cs) (multicast := mc) (cachePolicy := cp) .. =>
    opndRefs m ++ opndsRefs cs ++ optRefs (mc.map (·.2)) ++ optRefs cp
  | .cpTensorStore m cs _ _ cp _ _ => opndRefs m ++ opndsRefs cs ++ optRefs cp
  | .bulkCommit | .bulkWait .. | .clcTryCancel .. => []
  | .clcQuery _ _ r => opndRefs r
  | .mbarInit _ _ c => opndRefs c
  | .mbarInval .. | .fenceMbarInit => []
  | .fence f => fenceRefs f
  | .mbarArrive (tx := tx) (count := c) .. => opndRefs tx ++ opndRefs c
  | .cpBulk c => bulkRefs c
  | .asyncStore s => asyncStoreRefs s
  | .cpAsync (source := s) (cachePolicy := cp) .. => cpAsyncSrcRefs s ++ optRefs cp
  | .cpAsyncCommit | .cpAsyncWait .. | .cpAsyncArrive .. => []
  | .prefetchBulk _ _ s cp => opndRefs s ++ optRefs cp
  | .mbarWait (parity := p) .. => opndRefs p
  | .tcAlloc _ _ _ n => opndRefs n
  | .tcDealloc _ t n => opndRefs t ++ opndRefs n
  | .tcRelinquish _ => []
  | .tcMma m => tcMmaRefs m
  | .tcCommit _ _ _ m => optRefs m
  | .tcFenceBefore | .tcFenceAfter | .tcLd .. | .tcWaitLd | .tcWaitSt | .tcShift .. => []
  | .tcSt _ ss _ => opndsRefs ss
  | .tcCp _ _ _ d _ => opndRefs d
  | .unmodeled _ => [.unmodeled]

/-- The parameter uses of the program, in program order. -/
def refs : List ParamRef := kernel.code.flatMap fun i => opRefs i.op

/-- The parameter uses of the program with their program positions. -/
def refSites : List (Nat × ParamRef) :=
  kernel.code.zipIdx.flatMap fun p => (opRefs p.1.op).map (p.2, ·)

/-- The scalar parameters `Pre` constrains, in the order of its fields. -/
def readParams : List String :=
  [param "0", param "6", param "7", param "8", param "9", param "10", param "11", param "15",
    param "16", param "17", param "18", param "21", param "22", param "23", param "24",
    param "25"]

/-- The names of the `.read` uses. -/
def readNames : List ParamRef → List String
  | [] => []
  | .read n _ _ :: rs => n :: readNames rs
  | _ :: rs => readNames rs

/-- The names of the `.sym` uses. -/
def symNames : List ParamRef → List String
  | [] => []
  | .sym n :: rs => n :: symNames rs
  | _ :: rs => symNames rs

/-- The parameter uses of the program, with their positions: the 16 `ld.param` reads of the
scalar parameters and the address of the tensor-map object `param_1` at pc 6. -/
theorem refSites_eq : refSites =
    [(0, .read (param "24") 0 32), (1, .read (param "23") 0 32), (2, .read (param "22") 0 32),
      (3, .read (param "21") 0 32), (4, .read (param "18") 0 32), (5, .read (param "7") 0 64),
      (6, .sym (param "1")), (20, .read (param "17") 0 32), (21, .read (param "16") 0 32),
      (22, .read (param "15") 0 32), (23, .read (param "9") 0 64), (24, .read (param "8") 0 64),
      (25, .read (param "6") 0 64), (26, .read (param "0") 0 64),
      (316, .read (param "25") 0 32), (317, .read (param "11") 0 64),
      (318, .read (param "10") 0 64)] := by
  decide +kernel

theorem refs_eq : refs =
    [.read (param "24") 0 32, .read (param "23") 0 32, .read (param "22") 0 32,
      .read (param "21") 0 32, .read (param "18") 0 32, .read (param "7") 0 64,
      .sym (param "1"), .read (param "17") 0 32, .read (param "16") 0 32,
      .read (param "15") 0 32, .read (param "9") 0 64, .read (param "8") 0 64,
      .read (param "6") 0 64, .read (param "0") 0 64, .read (param "25") 0 32,
      .read (param "11") 0 64, .read (param "10") 0 64] := by
  decide +kernel

/-- Every parameter use of the program is a `ld.param` read or the address of a parameter
object: no store, atomic, other-space access or unmodeled instruction mentions a parameter. -/
theorem no_other : refs.all (fun r => match r with
    | .read .. | .sym _ => true
    | .other _ | .unmodeled => false) = true := by
  rw [refs_eq]
  decide +kernel

/-- No access in the `.param` space has a base other than a parameter, so none goes through a
register. -/
theorem paramSpace_param_based : kernel.code.all (fun i => match i.op with
    | .mem a => a.space != some .param || (match a.addr.base with | .param .. => true | _ => false)
    | .matrix m => m.space != some .param || m.addr.isNone
    | _ => true) = true := by
  decide +kernel

/-- The only parameter whose address the program forms is the tensor-map object `param_1`. -/
theorem syms_eq : symNames refs = [param "1"] := by
  rw [refs_eq]
  decide +kernel

/-- `param_1` is the declared by-value object, and not a scalar parameter. -/
theorem sym_is_object : kernel.paramObjects.map (·.name) = [param "1"] ∧
    (kernel.params.map (·.1)).contains (param "1") = false := by
  decide +kernel

/-- The scalar parameters read are exactly the list `Pre` constrains, and each is read once. -/
theorem reads_perm : (readNames refs).Perm readParams ∧ (readNames refs).Nodup := by
  rw [refs_eq]
  decide +kernel

/-- Each read is at offset 0 and has the declared width of its parameter. -/
theorem read_widths : refs.all (fun r => match r with
    | .read n off w => off == 0 && List.lookup n kernel.params == some w
    | _ => true) = true := by
  rw [refs_eq]
  decide +kernel

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- `Pre` constrains every parameter the program uses: each read scalar has a value in the launch,
and the address taken is that of a published parameter object. -/
theorem defines_refs (h : Pre P L mem0) : ∀ r ∈ refs, match r with
    | .read n _ _ => ∃ v, L.params n = some v
    | .sym n => ∃ o, L.paramObjects n = some o
    | _ => False := by
  intro r hr
  rw [refs_eq] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
  first
    | exact ⟨_, h.paramQ⟩ | exact ⟨_, h.paramRel⟩ | exact ⟨_, h.paramBt⟩
    | exact ⟨_, h.paramSeq⟩ | exact ⟨_, h.paramCu⟩ | exact ⟨_, h.paramO⟩
    | exact ⟨_, h.paramLse⟩ | exact ⟨_, h.paramStrideQ⟩ | exact ⟨_, h.paramStrideRel⟩
    | exact ⟨_, h.paramStrideBt⟩ | exact ⟨_, h.paramPageRows⟩
    | exact ⟨_, h.paramHeadRows⟩
    | exact ⟨_, h.paramHeadCols⟩ | exact ⟨_, h.paramSplits⟩ | exact ⟨_, h.paramNTok⟩
    | exact ⟨_, h.paramKv⟩
    | (obtain ⟨b, _, hb, _⟩ := h.paramScale; exact ⟨_, hb⟩)

end PTX.Kernels.InklingRelDecode.Audit
