# Protocol layer: what remains

The thread layer exposes, for every event of every launched thread, the machine state it came from
(`Frame.stateAt` and the role invariant; see `Proof/Thread/Wg0Sound.lean`). The protocol layer
turns those states and the object histories into the orderings the result and safety layers use.

Objects and counts are `Proof/Protocol/Mbar.lean` (`Mbar`, `NBar`), checked against the decoded
initializers.

## Index ring (`validReady` / `validFree`, 4 slots)

For each block `i` of a row and slot `p = i % 4`, parity `q = i / 4 % 2`:

1. Each of the 32 index lanes stores its coordinate pair in slot `p`. One lane per quad
   also stores the quad's validity byte. All 32 lanes then arrive on `validReady p`.
2. The elected raw-KV producer polls `validReady p` at parity `q`. A successful poll observes
   the 32 arrivals, which order the coordinate stores before the producer's shared loads.
3. The producer loads the word at position `2*lane+pair`. The lemmas
   `IndexTma.coordAt_eq_coordValue` and `coordOff_eq_coordBase` identify it with the index lane's word.
4. The producer arrives on `validFree p` after issuing the copies. The 128 softmax threads arrive
   after their last read of the slot. The index warp polls at parity `q ^ 1` before rewriting it.

## Raw ring (`rawReady` / `rawFree`, 2 buffers)

1. The producer's lane uses `arrive_and_expect_tx` on `rawReady b` with `B_TOPK * 576` bytes.
   The 16 gather4 copies complete into it. The 128 dequant threads poll at `block/2 % 2`.
2. After the poll the dequantizer's raw/scale loads read the rows at the producer's destinations
   (`RawTmaDequant.rawRow_addr_eq`, `scaleRow_addr_eq`).
3. The dequantizer arrives on `rawFree b` after its last read. The producer polls
   with the next round's parity before reusing the buffer.

## Other objects

`qTma`, `qUtccp`, `lastStore`, `dequantReady`, `qkDone`, `soReady`, `svDone` hand off the Q tile,
the TMEM copies, the P and O stages, and the raw/dequant tiles between warp 4, warp 5, wg0 and wg2.
Their counts and producers/consumers are in the S7 table. Named barriers: `wg0` (9, 128),
`warpPair` (10/11, 64), `everyone` (12, 384; the five role sites sum to 384 arrivals).
