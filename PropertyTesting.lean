import PropertyTesting.Correctness.Decidable

def bytesToUint64 (b1 b2 b3 b4 b5 b6 b7 b8: UInt8): UInt64 :=
  (((((((b1.toUInt64*256+b2.toUInt64)*256+b3.toUInt64)*256+b4.toUInt64)*256+b5.toUInt64)*256+b6.toUInt64)*256+b7.toUInt64)*256+b8.toUInt64)

def uint64sToUint256 (x1 x2 x3 x4: UInt64): UInt256 := {
  val := ((Fin.ofNat (x1.toNat) * 18446744073709551616 + Fin.ofNat (x2.toNat)) * 18446744073709551616 + Fin.ofNat (x3.toNat)) * 18446744073709551616 + Fin.ofNat (x4.toNat)
}

def parseTraceTailRec (bin: List UInt8) (acc: List (UInt64 × UInt64 × UInt64)): List (UInt64 × UInt64 × UInt64) :=
  match bin with
  | [] => acc
  | ap1::ap2::ap3::ap4::ap5::ap6::ap7::ap8::fp1::fp2::fp3::fp4::fp5::fp6::fp7::fp8::pc1::pc2::pc3::pc4::pc5::pc6::pc7::pc8::rest =>
    parseTraceTailRec rest (acc.append [(
      (bytesToUint64 pc8 pc7 pc6 pc5 pc4 pc3 pc2 pc1),
      (bytesToUint64 ap8 ap7 ap6 ap5 ap4 ap3 ap2 ap1),
      (bytesToUint64 fp8 fp7 fp6 fp5 fp4 fp3 fp2 fp1)
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

def runTest : IO Unit := do
  let _ ← IO.Process.run {cmd:="cairo-compile", args:=#["../cairo-vm-go/integration_tests/cairo_files/factorial.cairo", "--proof_mode", "--output", "./factorial_compiled.json"]}
  let _ ← IO.Process.run {cmd:="sh", args:=#["-c", "../cairo-vm-go/bin/cairo-vm run  --proofmode --tracefile ./factorial_trace --memoryfile ./factorial_memory ./factorial_compiled.json"]}
  let trace ← IO.FS.readBinFile "./factorial_trace"
  IO.println trace.size
  let parsedTrace := parseTraceTailRec trace.toList []
  IO.FS.writeFile "./factorial_trace.txt" (parsedTrace.map (λ (pc, ap, fp) => "(pc:=" ++ (pc.val: ℕ).repr ++ ", ap:=" ++ (ap.val: ℕ).repr ++ ", fp:=" ++ (fp.val: ℕ).repr ++ ")\n")).toString
  let memoryMap ← IO.FS.readBinFile "./factorial_memory"
  IO.println memoryMap.size
  let parsedMemoryMap := parseMemoryMapTailRec memoryMap.toList []
  IO.FS.writeFile "./factorial_memory.txt" (parsedMemoryMap.map (λ(k,v) => "(" ++ (k.val: ℕ).repr ++ ", " ++ (v.val: ℕ).repr ++ ")\n")).toString
  let decision := isTraceValid_checked_decidable parsedTrace parsedMemoryMap
  match decision with
    | .isTrue _ => IO.println "success"
    | .isFalse _ => IO.println "failure"
  return ()