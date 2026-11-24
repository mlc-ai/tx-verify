-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Local
public import Core.Source.Decode

/-!
# Special register values (THREAD-SREG)

Every register of PROG-ISA-SREG has a value (launch geometry, lane, or an unconstrained initial
value), is read by an event (a register that changes while the thread runs), or has no rule.
-/

namespace PTX.Tests.SRegValues
noncomputable section

private def launch : Launch := {
  grid := 8, block := 96, params := fun _ => none, clusterSize := 2
}

-- Launch registers: thread 37 of CTA 3, cluster 1, rank 1.
example : sregValue launch (3 * 96 + 37) ⟨.tid, some .x⟩ = some 37 := rfl
example : sregValue launch (3 * 96 + 37) ⟨.ctaid, some .x⟩ = some 3 := rfl
example : sregValue launch 0 ⟨.ntid, some .x⟩ = some 96 := rfl
example : sregValue launch 0 ⟨.nctaid, some .x⟩ = some 8 := rfl
example : sregValue launch (3 * 96) ⟨.clusterid, some .x⟩ = some 1 := rfl
example : sregValue launch (3 * 96) ⟨.clusterCtaid, some .x⟩ = some 1 := rfl
example : sregValue launch (3 * 96) ⟨.clusterCtarank, none⟩ = some 1 := rfl
example : sregValue launch 0 ⟨.nclusterid, some .x⟩ = some 4 := rfl
example : sregValue launch 0 ⟨.clusterNctarank, none⟩ = some 2 := rfl

-- The launch is one-dimensional: `.y` and `.z` are 0 and their extents 1, for clusters too.
example : sregValue launch (3 * 96 + 37) ⟨.clusterid, some .y⟩ = some 0 := rfl
example : sregValue launch (3 * 96 + 37) ⟨.clusterid, some .z⟩ = some 0 := rfl
example : sregValue launch (3 * 96 + 37) ⟨.clusterCtaid, some .z⟩ = some 0 := rfl
example : sregValue launch (3 * 96 + 37) ⟨.nclusterid, some .y⟩ = some 1 := rfl
example : sregValue launch (3 * 96 + 37) ⟨.clusterNctaid, some .z⟩ = some 1 := rfl
example : launch.OneDim := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
example : launch.oneDimLaunch := ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, by decide⟩
-- Every one-dimensional launch has the values of the one-dimensional model.
example (L : Launch) (h : L.OneDim) (g : Nat) :
    sregValue L g ⟨.ctaid, some .x⟩ = some (g / L.block) := (sregValue_oneDim h g).2.2.1
example (L : Launch) (h : L.OneDim) (g : Nat) :
    sregValue L g ⟨.ctaid, some .z⟩ = some 0 :=
  ((sregValue_oneDim h g).2.2.2.2.2.2.2.2.2.2 .z (by decide)).2.1
-- A rank has no component.
example (L : Launch) (g : Nat) : sregValue L g ⟨.clusterCtarank, some .x⟩ = none := rfl

-- Lane registers: thread 37 of a CTA is lane 5 of its warp.
example : sregValue launch (3 * 96 + 37) ⟨.laneid, none⟩ = some 5 := rfl
example : sregValue launch (3 * 96 + 37) ⟨.lanemaskEq, none⟩ = some 0x20 := rfl
example : sregValue launch (3 * 96 + 37) ⟨.lanemaskLe, none⟩ = some 0x3F := rfl
example : sregValue launch (3 * 96 + 37) ⟨.lanemaskLt, none⟩ = some 0x1F := rfl
example : sregValue launch (3 * 96 + 37) ⟨.lanemaskGe, none⟩ = some 0xFFFFFFE0 := rfl
example : sregValue launch (3 * 96 + 37) ⟨.lanemaskGt, none⟩ = some 0xFFFFFFC0 := rfl
-- Lane 0 and lane 31, the ends of the masks.
example : sregValue launch 96 ⟨.laneid, none⟩ = some 0 := rfl
example : sregValue launch 96 ⟨.lanemaskLt, none⟩ = some 0 := rfl
example : sregValue launch 96 ⟨.lanemaskGe, none⟩ = some 0xFFFFFFFF := rfl
example : sregValue launch (96 + 63) ⟨.laneid, none⟩ = some 31 := rfl
example : sregValue launch (96 + 63) ⟨.lanemaskEq, none⟩ = some 0x80000000 := rfl
example : sregValue launch (96 + 63) ⟨.lanemaskLe, none⟩ = some 0xFFFFFFFF := rfl
example : sregValue launch (96 + 63) ⟨.lanemaskGt, none⟩ = some 0 := rfl
-- The read path truncates to the declared width.
example : readBits launch 96 {} 32 (.sreg ⟨.lanemaskGe, none⟩) =
    .ok (BitVec.ofNat 64 0xFFFFFFFF) := rfl
-- Thread 95 of CTA 0 is lane 31 of warp 2.
example : sregValue launch 95 ⟨.laneid, none⟩ = some 31 := rfl

-- Initial registers: the launch's value, which any launch may choose.
example (L : Launch) (g : Nat) :
    sregValue L g ⟨.nsmid, none⟩ = some (L.sregInit g ⟨.nsmid, none⟩) := rfl
example (L : Launch) (g i : Nat) :
    sregValue L g ⟨.envreg i, none⟩ = some (L.sregInit g ⟨.envreg i, none⟩) := rfl
example (L : Launch) (g : Nat) :
    sregValue L g ⟨.dynamicSmemSize, none⟩ = some (L.sregInit g ⟨.dynamicSmemSize, none⟩) := rfl
example (L : Launch) (g : Nat) :
    sregValue L g ⟨.perctamemorysize, none⟩ = some (L.sregInit g ⟨.perctamemorysize, none⟩) := rfl
example : sregValue { launch with sregInit := fun _ _ => 7 } 0 ⟨.gridid, none⟩ = some 7 := rfl
example : sregValue { launch with sregInit := fun _ _ => 9 } 0 ⟨.gridid, none⟩ = some 9 := rfl
example (L : Launch) (g : Nat) (s : SReg) (h : s.kind = some .initial) :
    sregValue L g s = some (L.sregInit g s) := sregValue_initial h

-- `%is_explicit_cluster` is the launch's flag, read as a `.pred` source; a launch with clusters
-- of two CTAs is explicit unless it says otherwise.
example : sregValue launch 0 ⟨.isExplicitCluster, none⟩ = some 1 := rfl
example : sregValue { launch with explicitCluster := false } 0 ⟨.isExplicitCluster, none⟩ =
    some 0 := rfl
private def predEnv : Decode.Env := { classes := [⟨"p".toList, 1, 1⟩], labels := [], params := [] }
example : Decode.op predEnv "mov.pred" [.register "p0", .register "%is_explicit_cluster"] =
    .ok (.move ⟨.scalar, .pred, [some 0], [.sreg ⟨.isExplicitCluster, none⟩]⟩) := rfl
example (t : TState) : execLocal launch 0 t
    (.move ⟨.scalar, .pred, [some 0], [.sreg ⟨.isExplicitCluster, none⟩]⟩) =
      .ok (next (setReg t 0 (.pred true))) := rfl
example : readPred launch 0 {} (.sreg ⟨.isExplicitCluster, none⟩) = .ok true := rfl
example : readPred { launch with explicitCluster := false } 0 {}
    (.sreg ⟨.isExplicitCluster, none⟩) = .ok false := rfl
-- Rejected: a 32-bit special register is not a `.pred` source.
example : (Decode.op predEnv "mov.pred" [.register "p0", .register "%laneid"]).toOption =
    none := rfl
example : readPred launch 0 {} (.sreg ⟨.laneid, none⟩) = .error .typeMismatch := rfl

-- Registers that change while the thread runs are read by an event and have no local value.
example : SReg.rule ⟨.clock, none⟩ = some .threadSreg := rfl
example : SReg.varying ⟨.smid, none⟩ = true := rfl
example : SReg.varying ⟨.laneid, none⟩ = false := rfl
example : readBits launch 0 {} 32 (.sreg ⟨.clock, none⟩) = .error .noRule := rfl
example : readBits launch 0 {} 64 (.sreg ⟨.globaltimer, none⟩) = .error .noRule := rfl
-- Bounds: the width, and `%nsmid` for `%smid`.
example : SReg.readBound launch 0 ⟨.clock, none⟩ = 2 ^ 32 := rfl
example : SReg.readBound launch 0 ⟨.clock64, none⟩ = 2 ^ 64 := rfl
example : SReg.readBound { launch with sregInit := fun _ _ => 132 } 0 ⟨.smid, none⟩ = 132 := rfl
example : SReg.readBound launch 0 ⟨.smid, none⟩ = 2 ^ 32 := rfl

-- Registers without a rule: the undefined performance counters.
example : SReg.rule ⟨.pm 0, none⟩ = none := rfl
example : readBits launch 0 {} 32 (.sreg ⟨.pm 0, none⟩) = .error .noRule := rfl
example : readBits launch 0 {} 64 (.sreg ⟨.pm64 7, none⟩) = .error .noRule := rfl

-- A register has a value exactly when it has a rule and does not change.
example (L : Launch) (g : Nat) (s : SReg) :
    (sregValue L g s).isSome = (s.rule.isSome && !s.varying) := sregValue_isSome L g s

-- Decoding: a read at another width than the register's type is rejected.
private def env : Decode.Env := { classes := [⟨"r".toList, 1, 32⟩], labels := [], params := [] }
example : Decode.op env "mov.u32" [.register "r0", .register "%laneid"] =
    .ok (.move ⟨.scalar, .int .u 32, [some 0], [.sreg ⟨.laneid, none⟩]⟩) := rfl
example : (Decode.op env "mov.u32" [.register "r0", .register "%clock64"]).toOption = none := rfl
example (t : TState) :
    execLocal launch (96 + 63) t (.move ⟨.scalar, .int .u 32, [some 0], [.sreg ⟨.laneid, none⟩]⟩) =
      .ok (next (setReg t 0 (.bits 32 31))) := rfl

-- `%perctamemory` registers decode only in a kernel with `.minperctamemory`.
private def env64 : Decode.Env := { classes := [⟨"rd".toList, 1, 64⟩], labels := [], params := [] }
example : (Decode.op env64 "mov.u64" [.register "rd0", .register "%perctamemoryoffset"]).toOption =
    none := rfl
example : Decode.op { env64 with perCtaMemory := true } "mov.u64"
    [.register "rd0", .register "%perctamemoryoffset"] =
    .ok (.move ⟨.scalar, .int .u 64, [some 0], [.sreg ⟨.perctamemoryoffset, none⟩]⟩) := rfl

end
end PTX.Tests.SRegValues
