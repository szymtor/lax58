# Arena/native equivalence implementation record

Status: completed locally. The two verified compilers, their run simulations,
and the class-level equivalence described below now kernel-check. This file is
retained to document the design and resource argument.

The target is the existing open statement
`RamPolynomialComparison.bitPolynomialTime_iff_ramPolytime`.
Keep its arena-input definition unchanged. Both exponential separation
endpoints are already proved independently; they are not substitutes for
this general equivalence.

## Safe machine composition

An arbitrary upstream program may use every address. Therefore a converter
cannot assume fixed scratch cells are unused, or simply prepend a program
that leaves its scratch memory behind in the upstream machine's address space.

Implemented approach: simulate a virtual `v`-bit RAM at physical width
`v+1`, using even addresses for all virtual cells and odd addresses for
adapter/compiler scratch. `RamVirtualMemory` already proves the exact
interleaving read/write equations, address bounds, and double-modulus law.

The constant-overhead instruction translation establishes:

- Direct virtual address `a` maps to `2 * (a % 2^v)`.
- Indirect addressing first reads the virtual cell, then doubles its value.
- Mask every produced virtual value by `2^v-1`. Physical arithmetic followed
  by this mask reproduces arithmetic modulo `2^v`, including oversized
  program literals. Handle virtual complement explicitly.
- Obtain the virtual mask uniformly as half of the physical all-ones word;
  no instruction or program depends on the runtime width.
- Translate jumps to block addresses. Prove halted/out-of-range states and
  exhausted logical input as well as ordinary instructions.
- Give reads a bounded, inline adapter; output instructions write the exact
  virtual output. Prove one-step simulation, then run/time transfer.

## Streaming adapters (no payload buffer required)

For a natural list of length `n`, the arena root is `6*n`. The remaining
tape contains natural blocks `[0,x,0]` in input order, one nil block, then
pair blocks in reverse element order. Pair `i` has words
`[1, 3*i, 6*n-3*i-3]` for `i=n-1,...,0`.

- Physical arena to virtual native: read/store root, compute `n`; supply
  virtual prefix `n`, then skip tags/padding and supply the next payload.
  After `n` payloads, a logical read halts even though unused arena words
  remain on the physical tape.
- Physical native to virtual arena: the implemented prelude reads the known
  length and buffers exactly the `n` payload words in protected odd cells.
  This is safe even if the simulated source halts before consuming its arena:
  the physical native tape contains exactly those `n+1` words. Subsequent
  logical reads use an eight-state generator for the root, natural triples,
  nil triple, and reverse pair triples. Only payloads are buffered; arena fit
  leaves enough odd cells after the fixed scratch prefix. The first request
  after the full logical arena jumps outside the compiled program and halts.

Each requested logical word needs bounded work; a computation may halt
without consuming its entire logical or physical input. Prove the exact
arena tape formula, rather than assuming the verbal layout above.

## Resource transfer and completion gates

Increase the sufficient bit polynomial by a constant and a linear binary-size
term to fit fixed scratch addresses, counters, generated arena pointers, and
the protected payload buffer.
Use the same logical binary size `B` in both directions. At every sufficient
physical width, the virtual width is sufficient for the original witness.
`BitPolynomialTime.using_iff` already supplies the bit-width interface.

Both directions have polynomial time bounds and exact output preservation.
The polynomial witnesses in the two directions may have unrelated degrees;
only existence of some polynomial bound is required.
The final theorem's guarded axiom audit confirms that it does not assume its
own conclusion or either separation statement.
