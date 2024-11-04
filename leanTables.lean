/-
Copyright © 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import UnicodeData

open Unicode

def compressProp (arr : Array (UInt32 × UInt32)) (noOverlap : Bool := true) : Id <| Array (UInt32 × UInt32) :=
  if h : arr.size > 0 then do
    let mut res := #[]
    let mut top := arr[0]
    for a in arr[1:] do
      if noOverlap && a.1 ≤ top.2 then
        panic! "overlap!"
      else if a.1 ≤ top.2 + 1 then
        top := (top.1, max a.2 top.2)
      else
        res := res.push top
        top := a
    return res.push top
  else #[]

def compressData [BEq α] (arr : Array (UInt32 × UInt32 × α)) (noOverlap : Bool := true) : Id <| Array (UInt32 × UInt32 × α) :=
  if h : arr.size > 0 then do
    let mut res := #[]
    let mut top := arr[0]
    for a in arr[1:] do
      if noOverlap && a.1 ≤ top.2.1 then
        panic! "overlap!"
      else if a.2.2 == top.2.2 && a.1 ≤ top.2.1 + 1 then
        top := (top.1, max a.2.1 top.2.1, top.2.2)
      else
        res := res.push top
        top := a
    return res.push top
  else #[]

def mergeProp (d : Array (Array (UInt32 × UInt32))) (noOverlap : Bool := true) : Array (UInt32 × UInt32) :=
  let data := d.flatten.qsort fun a b => a.1 < b.1
  compressProp data noOverlap

def mergeData [BEq α] (d : Array (Array (UInt32 × UInt32 × α))) (noOverlap : Bool := true) : Array (UInt32 × UInt32 × α) :=
  let data := d.flatten.qsort fun a b => a.1 < b.1
  compressData data noOverlap

def statsData (array : Array (UInt32 × UInt32 × α)) : Id <| Nat × Nat := do
  let mut ct := 0
  for (c₀, c₁, _) in array do
    ct := ct + (c₁.toNat - c₀.toNat)
  return (array.size, ct)

def statsProp (array : Array (UInt32 × UInt32)) : Id <| Nat × Nat := do
  let mut ct := 0
  for (c₀, c₁) in array do
    ct := ct + (c₁.toNat - c₀.toNat)
  return (array.size, ct)

def mkBidiClass : IO <| Array (UInt32 × UInt32 × BidiClass) := do
  let mut t := #[]
  for d in UnicodeData.data do
    if d.characterName.takeRight 7 == ", Last>" then
      match t.back? with
      | some (c₀, _, bc) =>
        t := t.pop.push (c₀, d.codeValue, bc)
      | none => unreachable!
    else
      match t.back? with
      | some (c₀, c₁, bc) =>
        if d.codeValue = c₁ + 1 && d.bidiClass == bc then
          t := t.pop.push (c₀, c₁+1, bc)
        else
          t := t.push (d.codeValue, d.codeValue, d.bidiClass)
      | none =>
        t := t.push (d.codeValue, d.codeValue, d.bidiClass)
  return t

def mkBidiMirrored : IO <| Array (UInt32 × UInt32) := do
  let mut t := #[]
  for d in UnicodeData.data do
    if d.bidiMirrored then
      match t.back? with
      | some (c₀, c₁) =>
        if d.codeValue == c₁ + 1 then
          t := t.pop.push (c₀, d.codeValue)
        else
          t := t.push (d.codeValue, d.codeValue)
      | none =>
        t := t.push (d.codeValue, d.codeValue)
  return t

def mkCanonicalCombiningClass : IO <| Array (UInt32 × UInt32 × Nat) := do
  let mut t := #[]
  for d in UnicodeData.data do
    if d.canonicalCombiningClass > 0 then
      match t.back? with
      | some (c₀, c₁, cc) =>
        if t.size != 0 && d.codeValue == c₁ + 1 && d.canonicalCombiningClass == cc then
          t := t.pop.push (c₀, c₁+1, cc)
        else
          t := t.push (d.codeValue, d.codeValue, d.canonicalCombiningClass)
      | none =>
        t := t.push (d.codeValue, d.codeValue, d.canonicalCombiningClass)
  return t

partial def mkCanonicalDecompositionMapping : IO <| Array (UInt32 × List Char) := do
  let mut t := #[]
  for data in UnicodeData.data do
    match data.decompositionMapping with
    | some ⟨none, l⟩ =>
      t := t.push (data.codeValue, fullDecomposition l)
    | _ => continue
  return t
where
  fullDecomposition : List Char → List Char
  | [] => unreachable!
  | h :: t =>
    match (getUnicodeData h).decompositionMapping with
    | some ⟨none, l⟩ => fullDecomposition (l ++ t)
    | _ => h :: t

def mkCaseMapping : IO <| Array (UInt32 × UInt32 × UInt32 × UInt32 × UInt32) := do
  let mut t := #[]
  for data in UnicodeData.data do
    match data with
    | ⟨_, _, _, _, _, _, _, _, none, none, none⟩ => continue
    | ⟨c, _, _, _, _, _, _, _, um, lm, tm⟩ =>
      let uc := match um with | some uc => uc.val | _ => c
      let lc := match lm with | some lc => lc.val | _ => c
      let tc := match tm with | some tc => tc.val | _ => uc
      match t.back? with
      | some (c₀,c₁,m) =>
        if (c == c₁ + 1) && (m == (uc, lc, tc)) then
          t := t.pop.push (c₀, c, m)
        else
          t := t.push (c, c, uc, lc, tc)
      | _ =>
          t := t.push (c, c, uc, lc, tc)
  return t

def mkDecompositionMapping : IO <| Array (UInt32 × String) := do
  let mut t := #[]
  for data in UnicodeData.data do
    match data.decompositionMapping with
    | some ⟨none, l⟩ =>
      t := t.push (data.codeValue, ";" ++ ";".intercalate (l.map (toHexStringAux <| Char.val .)))
    | some ⟨some k, l⟩ =>
      t := t.push (data.codeValue, s!"{k};" ++ ";".intercalate (l.map (toHexStringAux <| Char.val ·)))
    | _ => continue
  return t

def mkGeneralCategory : IO <| Array (UInt32 × UInt32 × GeneralCategory) := do
  let mut t := #[(0,0,GeneralCategory.Cc)]
  for i in [1:UnicodeData.data.size] do
    let data := UnicodeData.data[i]!
    let c := data.codeValue
    let k := data.generalCategory
    if data.characterName.takeRight 8 == ", First>" then
      t := t.push (c, c, k)
    else if data.characterName.takeRight 7 == ", Last>" then
      match t.back with
      | (c₀, _, k) =>
        t := t.pop.push (c₀, c, k)
    else
      let k :=
        if k == .Lu && (c &&& 1) == 0 && UnicodeData.data[i+1]!.codeValue == c+1 then
          if UnicodeData.data[i+1]!.generalCategory == .Ll
          then .LC
          else k
        else if k == .Ll && (c &&& 1) != 0 && UnicodeData.data[i-1]!.codeValue == c-1 then
          if UnicodeData.data[i-1]!.generalCategory == .Lu
          then .LC
          else k
        else if k == .Ps && (c &&& 1) == 0 && UnicodeData.data[i+1]!.codeValue == c+1 then
          if UnicodeData.data[i+1]!.generalCategory == .Pe
          then .PG
          else k
        else if k == .Pe && (c &&& 1) != 0 && UnicodeData.data[i-1]!.codeValue == c-1 then
          if UnicodeData.data[i-1]!.generalCategory == .Ps
          then .PG
          else k
        else if k == .Pi && (c &&& 1) == 0 && UnicodeData.data[i+1]!.codeValue == c+1 then
          if UnicodeData.data[i+1]!.generalCategory == .Pf
          then .PQ
          else k
        else if k == .Pf && (c &&& 1) != 0 && UnicodeData.data[i-1]!.codeValue == c-1 then
          if UnicodeData.data[i-1]!.generalCategory == .Pi
          then .PQ
          else k
        else k
      match t.back with
      | (c₀, c₁, k₁) =>
        if c == c₁ + 1 && k == k₁ then
          t := t.pop.push (c₀, c, k)
        else
          t := t.push (c, c, k)
  return t

def mkNoncharacterCodePoint : Array (UInt32 × UInt32) :=
  PropList.data.noncharacterCodePoint.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkName : IO <| Array (UInt32 × UInt32 × String) := do
  let mut t := #[(0,0,"<Control>")]
  for i in [1:UnicodeData.data.size] do
    let data := UnicodeData.data[i]!
    let c := data.codeValue
    let n := data.characterName.toString
    if n.takeRight 8 == ", First>" then
      if "<CJK Ideograph".isPrefixOf n then
        t := t.push (c, c, "<CJK Unified Ideograph>")
      else if "<Tangut Ideograph".isPrefixOf n then
        t := t.push (c, c, "<Tangut Ideograph>")
      else if n.takeRight 17 == "Surrogate, First>" then
        match t.back with
        | (c₀, c₁, n₀) =>
          if c == c₁ + 1 && n₀ == "<Surrogate>" then
            t := t.pop.push (c₀, c, "<Surrogate>")
          else
            t := t.push (c, c, "<Surrogate>")
      else if n.takeRight 19 == "Private Use, First>" then
        t := t.push (c, c, "<Private Use>")
      else
        t := t.push (c, c, n.dropRight 8 ++ ">")
    else if n.takeRight 7 == ", Last>" then
      match t.back with
      | (c₀, _, n₀) =>
        t := t.pop.push (c₀, c, n₀)
    else if n == "<control>" then
      match t.back with
      | (c₀, _, n₀) =>
        if n₀ == "<Control>" then
          t := t.pop.push (c₀, c, n₀)
        else
          t := t.push (c, c, "<Control>")
    else if "CJK COMPATIBILITY IDEOGRAPH-".isPrefixOf n then
      match t.back with
      | (c₀, c₁, n) =>
        if c == c₁ + 1 && n == "<CJK Compatibility Ideograph>" then
          t := t.pop.push (c₀, c, n)
        else
          t := t.push (c, c, "<CJK Compatibility Ideograph>")
    else if "KHITAN SMALL SCRIPT CHARACTER-".isPrefixOf n then
      match t.back with
      | (c₀, c₁, n) =>
        if c == c₁ + 1 && n == "<Khitan Small Script Character>" then
          t := t.pop.push (c₀, c, n)
        else
          t := t.push (c, c, "<Khitan Small Script Character>")
    else if "NUSHU CHARACTER-".isPrefixOf n then
      match t.back with
      | (c₀, c₁, n) =>
        if c == c₁ + 1 && n == "<Nushu Character>" then
          t := t.pop.push (c₀, c, n)
        else
          t := t.push (c, c, "<Nushu Character>")
    else if "TANGUT COMPONENT-".isPrefixOf n then
      match t.back with
      | (c₀, c₁, n) =>
        if c == c₁ + 1 && n == "<Tangut Component>" then
          t := t.pop.push (c₀, c, n)
        else
          t := t.push (c, c, "<Tangut Component>")
    else
      match t.back with
      | (c₀, c₁, n₀) =>
        if c == c₁ + 1 && n == n₀ then
          t := t.pop.push (c₀, c, n)
        else
          t := t.push (c, c, n)
  return mergeData #[t, mkNoncharacterCodePoint.map fun (c₀, c₁) => (c₀, c₁, "<Reserved>")]

def mkNumericValue : IO <| Array (UInt32 × UInt32 × NumericType) := do
  let mut t := #[]
  for d in UnicodeData.data do
    match d.numeric with
    | some (.decimal 0) =>
      t := t.push (d.codeValue, d.codeValue + 9, .decimal 0)
    | some (.digit v) =>
      match t.back with
      | (c₀, c₁, n@(NumericType.digit x)) =>
        let last := x.val + c₁.val - c₀.val
        if d.codeValue == c₁ + 1 && v.val == last + 1 then
          t := t.pop.push (c₀, d.codeValue, n)
        else
          t := t.push (d.codeValue, d.codeValue, .digit v)
      | _ =>
        t := t.push (d.codeValue, d.codeValue, .digit v)
    | some n@(.numeric _ _) =>
      t := t.push (d.codeValue, d.codeValue, n)
    | _ => continue
  return t

def mkOtherAlphabetic : Array (UInt32 × UInt32) :=
  PropList.data.otherAlphabetic.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkOtherLowercase : Array (UInt32 × UInt32) :=
  PropList.data.otherLowercase.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkOtherMath : Array (UInt32 × UInt32) :=
  PropList.data.otherMath.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkOtherUppercase : Array (UInt32 × UInt32) :=
  PropList.data.otherUppercase.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def mkAlphabetic : IO <| Array (UInt32 × UInt32) := do
  let mut t := #[]
  for (c₀, c₁, gc) in ← mkGeneralCategory do
    match gc with
    | .LC | .Ll | .Lu | .Lt | .Lm | .Lo | .Nl =>
      match t.back? with
      | some (a₀, a₁) =>
        if c₀ == a₁ + 1 then
          t := t.pop.push (a₀, c₁)
        else
          t := t.push (c₀, c₁)
      | none =>
        t := t.push (c₀, c₁)
    | _ => continue
  return mergeProp #[t, mkOtherAlphabetic]

def mkCased : IO <| Array (UInt32 × UInt32) := do
  let t := (← mkGeneralCategory).filterMap fun d =>
    if d.2.2 ∈ [.LC, .Ll, .Lu, .Lt] then
      some (d.1, d.2.1)
    else
      none
  return mergeProp #[t, mkOtherLowercase, mkOtherUppercase]

def mkMath : IO <| Array (UInt32 × UInt32) := do
  let t := (← mkGeneralCategory).filterMap fun
    | (c₀, c₁, .Sm) => some (c₀, c₁)
    | _ => none
  return mergeProp #[t, mkOtherMath]

def mkLowercase : IO <| Array (UInt32 × UInt32) := do
  let mut t := #[]
  for gc in ← mkGeneralCategory do
    match gc with
    | (c₀, c₁, .Ll) =>
      t := t.push (c₀, c₁)
    | (c₀, c₁, .LC) =>
      for c in [c₀.toNat:c₁.toNat+1] do
        if c % 2 != 0 then t := t.push (c.toUInt32, c.toUInt32)
    | _ => continue
  return mergeProp #[t, mkOtherLowercase]

def mkTitlecase : IO <| Array (UInt32 × UInt32) := do
  let mut t := #[]
  for gc in ← mkGeneralCategory do
    match gc with
    | (c₀, c₁, .Lt) =>
      t := t.push (c₀, c₁)
    | _ => continue
  return t

def mkUppercase : IO <| Array (UInt32 × UInt32) := do
  let mut t := #[]
  for gc in ← mkGeneralCategory do
    match gc with
    | (c₀, c₁, .Lu) =>
      t := t.push (c₀, c₁)
    | (c₀, c₁, .LC) =>
      for c in [c₀.toNat:c₁.toNat+1] do
        if c % 2 == 0 then t := t.push (c.toUInt32, c.toUInt32)
    | _ => continue
  return mergeProp #[t, mkOtherUppercase]

def mkWhiteSpace : IO <| Array (UInt32 × UInt32) :=
  return PropList.data.whiteSpace.map fun
    | (c₀, some c₁) => (c₀, c₁)
    | (c₀, none) => (c₀, c₀)

def main (args : List String) : IO UInt32 := do
  let args := if args != [] then args else [
    "Alphabetic",
    "Bidi_Class",
    "Bidi_Mirrored",
    "Canonical_Combining_Class",
    "Canonical_Decomposition_Mapping",
    "Case_Mapping",
    "Cased",
    "Decomposition_Mapping",
    "Lowercase",
    "Math",
    "Name",
    "Titlecase",
    "Uppercase",
    "Numeric_Value",
    "General_Category",
    "White_Space"]
  let tableDir : System.FilePath := "." / "UnicodeBasic" / "Table"
  IO.FS.createDirAll tableDir
  for arg in args do
    match arg with
    | "Alphabetic" =>
      IO.println s!"Generating table Alphabetic"
      IO.FS.withFile (tableDir/"Alphabetic.lean") .write fun file => do
        file.putStrLn "-- Generated from Unicode data -- Do not edit!"
        file.putStrLn "import UnicodeBasic.Types"
        file.putStrLn "protected def Unicode.Table.Alphabetic : Array (UInt32 × UInt32) :="
        file.putStrLn <| toString <| repr (← mkAlphabetic)
    | "Bidi_Class" =>
      IO.println s!"Generating table BidiClass"
      IO.FS.withFile (tableDir/"BidiClass.lean") .write fun file => do
        file.putStrLn "-- Generated from Unicode data -- Do not edit!"
        file.putStrLn "import UnicodeBasic.Types"
        file.putStrLn "set_option maxHeartbeats 400000"
        file.putStrLn "protected def Unicode.Table.BidiClass : Array (UInt32 × UInt32 × BidiClass) :="
        file.putStrLn <| toString <| repr (← mkBidiClass)
    | "Bidi_Mirrored" =>
      IO.println "Generating table BidiMirrored"
      IO.FS.withFile (tableDir/"BidiMirrored.lean") .write fun file => do
        file.putStrLn "-- Generated from Unicode data -- Do not edit!"
        file.putStrLn "import UnicodeBasic.Types"
        file.putStrLn "protected def Unicode.Table.BidiMirrored : Array (UInt32 × UInt32) :="
        file.putStrLn <| toString <| repr (← mkBidiMirrored)
    | "Canonical_Combining_Class" =>
      IO.println "Generating table CanonicalCombiningClass"
      IO.FS.withFile (tableDir/"CanonicalCombiningClass.lean") .write fun file => do
        file.putStrLn "-- Generated from Unicode data -- Do not edit!"
        file.putStrLn "import UnicodeBasic.Types"
        file.putStrLn "protected def Unicode.Table.CanonicalCombiningClass : Array (UInt32 × UInt32 × Nat) :="
        file.putStrLn <| toString <| repr (← mkCanonicalCombiningClass)
    | "Canonical_Decomposition_Mapping" =>
      IO.println "Generating table CanonicalDecompositionMapping"
      IO.FS.withFile (tableDir/"CanonicalDecompositionMapping.lean") .write fun file => do
        file.putStrLn "-- Generated from Unicode data -- Do not edit!"
        file.putStrLn "import UnicodeBasic.Types"
        file.putStrLn "set_option maxHeartbeats 400000"
        file.putStrLn "protected def Unicode.Table.CanonicalDecompositionMapping : Array (UInt32 × List Char) :="
        file.putStrLn <| toString <| repr (← mkCanonicalDecompositionMapping)
    | "Case_Mapping" =>
      IO.println "Generating table CaseMapping"
      IO.FS.withFile (tableDir/"CaseMapping.lean") .write fun file => do
        file.putStrLn "-- Generated from Unicode data -- Do not edit!"
        file.putStrLn "import UnicodeBasic.Types"
        file.putStrLn "set_option maxHeartbeats 400000"
        file.putStrLn "protected def Unicode.Table.CanonicalDecompositionMapping : Array (UInt32 × UInt32 × UInt32 × UInt32 × UInt32) :="
        file.putStrLn <| toString <| repr (← mkCaseMapping)
    | "Cased" =>
      IO.println "Generating table Cased"
      IO.FS.withFile (tableDir/"Cased.lean") .write fun file => do
        file.putStrLn "-- Generated from Unicode data -- Do not edit!"
        file.putStrLn "import UnicodeBasic.Types"
        file.putStrLn "protected def Unicode.Table.Cased : Array (UInt32 × UInt32) :="
        file.putStrLn <| toString <| repr (← mkCased)
    | "Decomposition_Mapping" =>
      IO.println "Generating table DecompositionMapping"
      IO.FS.withFile (tableDir/"DecompositionMapping.lean") .write fun file => do
        file.putStrLn "-- Generated from Unicode data -- Do not edit!"
        file.putStrLn "import UnicodeBasic.Types"
        file.putStrLn "set_option maxHeartbeats 400000"
        file.putStrLn "protected def Unicode.Table.DecompositionMapping : Array (UInt32 × String) :="
        file.putStrLn <| toString <| repr (← mkDecompositionMapping)
    | "General_Category" =>
      IO.println "Generating table GeneralCategory"
      IO.FS.withFile (tableDir/"GeneralCategory.lean") .write fun file => do
        file.putStrLn "-- Generated from Unicode data -- Do not edit!"
        file.putStrLn "import UnicodeBasic.Types"
        file.putStrLn "set_option maxHeartbeats 1000000"
        file.putStrLn "protected def Unicode.Table.GeneralCategory : Array (UInt32 × UInt32 × GeneralCategory) :="
        file.putStrLn <| toString <| repr (← mkGeneralCategory)
    | "Lowercase" =>
      IO.println "Generating table Lowercase"
      IO.FS.withFile (tableDir/"Lowercase.lean") .write fun file => do
        file.putStrLn "-- Generated from Unicode data -- Do not edit!"
        file.putStrLn "import UnicodeBasic.Types"
        file.putStrLn "protected def Unicode.Table.Lowercase : Array (UInt32 × UInt32) :="
        file.putStrLn <| toString <| repr (← mkLowercase)
    | "Math" =>
      IO.println "Generating table Math"
      IO.FS.withFile (tableDir/"Math.lean") .write fun file => do
        file.putStrLn "-- Generated from Unicode data -- Do not edit!"
        file.putStrLn "import UnicodeBasic.Types"
        file.putStrLn "protected def Unicode.Table.Math : Array (UInt32 × UInt32) :="
        file.putStrLn <| toString <| repr (← mkMath)
    | "Name" =>
      IO.println "Generating table Name"
      IO.FS.withFile (tableDir/"Name.lean") .write fun file => do
        file.putStrLn "-- Generated from Unicode data -- Do not edit!"
        file.putStrLn "import UnicodeBasic.Types"
        file.putStrLn "set_option maxHeartbeats 400000"
        file.putStrLn "protected def Unicode.Table.Name : Array (UInt32 × String) :="
        file.putStrLn <| toString <| repr (← mkName)
    | "Numeric_Value" =>
      IO.println "Generating table NumericValue"
      IO.FS.withFile (tableDir/"NumericValue.lean") .write fun file => do
        file.putStrLn "-- Generated from Unicode data -- Do not edit!"
        file.putStrLn "import UnicodeBasic.Types"
        file.putStrLn "set_option maxHeartbeats 400000"
        file.putStrLn "protected def Unicode.Table.NumericalValue : Array (UInt32 × UInt32 × NumericType) :="
        file.putStrLn <| toString <| repr (← mkNumericValue)
    | "Titlecase" =>
      IO.println "Generating table Titlecase"
      IO.FS.withFile (tableDir/"Titlecase.lean") .write fun file => do
        file.putStrLn "-- Generated from Unicode data -- Do not edit!"
        file.putStrLn "import UnicodeBasic.Types"
        file.putStrLn "protected def Unicode.Table.Titlecase : Array (UInt32 × UInt32) :="
        file.putStrLn <| toString <| repr (← mkTitlecase)
    | "Uppercase" =>
      IO.println "Generating table Uppercase"
      IO.FS.withFile (tableDir/"Uppercase.lean") .write fun file => do
        file.putStrLn "-- Generated from Unicode data -- Do not edit!"
        file.putStrLn "import UnicodeBasic.Types"
        file.putStrLn "protected def Unicode.Table.Uppercase : Array (UInt32 × UInt32) :="
        file.putStrLn <| toString <| repr (← mkUppercase)
    | "White_Space" =>
      IO.println "Generating table WhiteSpace"
      IO.FS.withFile (tableDir/"WhiteSpace.lean") .write fun file => do
        file.putStrLn "-- Generated from Unicode data -- Do not edit!"
        file.putStrLn "import UnicodeBasic.Types"
        file.putStrLn "protected def Unicode.Table.WhiteSpace : Array (UInt32 × UInt32) :="
        file.putStrLn <| toString <| repr (← mkWhiteSpace)
    | _ => IO.println s!"Unknown property {arg}"
  return 0
