layer x86_checks uses x86_64_linux

// Earlier forms of parts of the x86 model, kept to prove that the current
// forms mean the same (proofs/x86.core). Nothing here is used by the claim.

// The memory write of the `mem` view before its closed form `store_le`:
// byte by byte, byte i of v at a + i.
proc[Machine] store_bytes(a: Addr, n: nat, v: nat) {
  for i in 0..n { vm.bytes[a + bits[64](i)] := bits[8](v / 256^i) }
}
