import PropertyTesting.Correctness.Decidable

def bytesToUint64 (b1 b2 b3 b4 b5 b6 b7 b8: UInt8): UInt64 :=
  (((((((b1.toUInt64*8+b2.toUInt64)*8+b3.toUInt64)*8+b4.toUInt64)*8+b5.toUInt64)*8+b6.toUInt64)*8+b7.toUInt64)*8+b8.toUInt64)

def uint64sToUint256 (x1 x2 x3 x4: UInt64): UInt256 := {
  val := ((Fin.ofNat (x1.toNat) * 18446744073709551616 + Fin.ofNat (x2.toNat)) * 18446744073709551616 + Fin.ofNat (x3.toNat)) * 18446744073709551616 + Fin.ofNat (x4.toNat)
}

def parseTraceTailRec (bin: List UInt8) (acc: List (UInt64 × UInt64 × UInt64)): List (UInt64 × UInt64 × UInt64) :=
  match bin with
  | [] => acc
  | a1::a2::a3::a4::a5::a6::a7::a8::b1::b2::b3::b4::b5::b6::b7::b8::c1::c2::c3::c4::c5::c6::c7::c8::rest =>
    parseTraceTailRec rest (acc.append [(
      (bytesToUint64 a8 a7 a6 a5 a4 a3 a2 a1),
      (bytesToUint64 b8 b7 b6 b5 b4 b3 b2 b1),
      (bytesToUint64 c8 c7 c6 c5 c4 c3 c2 c1)
    )])
  | _ => []

--no native UInt256 so we're using Uint64 for now
def parseMemoryMapTailRec (bin: List UInt8) (acc: List (UInt64 × UInt256)): List (UInt64 × UInt256) :=
  match bin with
  | [] => acc
  | a1::a2::a3::a4::a5::a6::a7::a8::b1::b2::b3::b4::b5::b6::b7::b8::b9::b10::b11::b12::b13::b14::b15::b16::b17::b18::b19::b20::b21::b22::b23::b24::b25::b26::b27::b28::b29::b30::b31::b32::rest =>
    parseMemoryMapTailRec rest (acc.append [((bytesToUint64 a8 a7 a6 a5 a4 a3 a2 a1), (
      uint64sToUint256 (bytesToUint64 b32 b31 b30 b29 b28 b27 b26 b25)
      (bytesToUint64 b24 b23 b22 b21 b20 b19 b18 b17)
      (bytesToUint64 b16 b15 b14 b13 b12 b11 b10 b9)
      (bytesToUint64 b8 b7 b6 b5 b4 b3 b2 b1)
    ))])
  | _ => []

def main : IO Unit := do
  let _ ← IO.Process.run {cmd:="cairo-compile", args:=#["../cairo-vm-go/integration_tests/cairo_files/factorial.cairo", "--proof_mode", "--output", "./factorial_compiled.json"]}
  let _ ← IO.Process.run {cmd:="sh", args:=#["-c", "../cairo-vm-go/bin/cairo-vm run  --proofmode --tracefile ./factorial_trace --memoryfile ./factorial_memory ./factorial_compiled.json"]}
  let trace ← IO.FS.readBinFile "./factorial_trace"
  IO.println trace.size
  let parsedTrace := parseTraceTailRec trace.toList []
  -- IO.println parsedTrace
  let memoryMap ← IO.FS.readBinFile "./factorial_memory"
  IO.println memoryMap.size
  let parsedMemoryMap := parseMemoryMapTailRec memoryMap.toList []
  -- IO.println parsedMemoryMap
  let decision := isTraceValid_checked_decidable parsedTrace parsedMemoryMap
  match decision with
    | .isTrue _ => IO.println "success"
    | .isFalse _ => IO.println "failure"
  return ()