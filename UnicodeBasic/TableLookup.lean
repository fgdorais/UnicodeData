/-
Copyright © 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import UnicodeBasic.CharacterDatabase
import UnicodeBasic.Hangul
import UnicodeBasic.Table.Alphabetic
import UnicodeBasic.Table.BidiClass
import UnicodeBasic.Table.BidiMirrored
import UnicodeBasic.Table.CanonicalCombiningClass
import UnicodeBasic.Table.CanonicalDecompositionMapping
import UnicodeBasic.Table.Cased
import UnicodeBasic.Table.GeneralCategory
import UnicodeBasic.Table.Lowercase
import UnicodeBasic.Table.Math
import UnicodeBasic.Table.NumericValue
import UnicodeBasic.Table.Titlecase
import UnicodeBasic.Table.Uppercase
import UnicodeBasic.Table.Util
import UnicodeBasic.Table.WhiteSpace
import UnicodeBasic.Types

namespace Unicode

/-- Binary search -/
@[specialize]
private partial def find (c : UInt32) (t : USize → UInt32) (lo hi : USize) : USize :=
  let mid := (lo + hi) / 2
  if lo = mid then
    lo
  else if c < t mid then
    find c t lo mid
  else
    find c t mid hi

/-- Get bidirectional class using lookup table

  Unicode property: `Bidi_Class` -/
def lookupBidiClass (c : UInt32) : BidiClass :=
  let table := Table.BidiClass
  if c < table[0]!.1 then .BN else
    match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
    | (_, v, bc) => if c ≤ v then bc else .BN

/-- Get canonical combining class using lookup table

  Unicode property: `Canonical_Combining_Class` -/
def lookupCanonicalCombiningClass (c : UInt32) : Nat :=
  let table := Table.CanonicalCombiningClass
  if c < table[0]!.1 then 0 else
    match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
    | (_, v, n) => if c ≤ v then n else 0

/-- Get canonical decomposition mapping using lookup table

  Unicode properties:
    `Decomposition_Mapping`
    `Decomposition_Type=Canonical` -/
def lookupCanonicalDecompositionMapping (c : UInt32) : List UInt32 :=
  -- Hangul syllables
  if Hangul.Syllable.base ≤ c && c ≤ Hangul.Syllable.last then
    let s := Hangul.getSyllable! c
    match s.getTChar? with
    | some t => [s.getLChar.val, s.getVChar.val, t.val]
    | none => [s.getLChar.val, s.getVChar.val]
  else
    let table := Table.CanonicalDecompositionMapping
    if c < table[0]!.1 then [c] else
      match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
      | (v, l) => if c == v then l.map Char.val else [c]

/-- Get simple case mappings of a code point using lookup table

  Unicode properties:
    `Simple_Lowercase_Mapping`
    `Simple_Uppercase_Mapping`
    `Simple_Titlecase_Mapping` -/
def lookupCaseMapping (c : UInt32) : UInt32 × UInt32 × UInt32 :=
  let table := table.get
  if c < table[0]!.1 then (c, c, c) else
    match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
    | (_, v, mu, ml, mt) => if c ≤ v then (mu.getD c, ml.getD c, mt.getD (mu.getD c)) else (c, c, c)
where
  str : String := include_str "../data/table/Case_Mapping.txt"
  table : Thunk <| Array (UInt32 × UInt32 × Option UInt32 × Option UInt32 × Option UInt32) :=
    parseDataTable str fun _ _ a =>
      match a with
      | #[mu, ml, mt] =>
        let mu := if mu.isEmpty then none else some <| ofHexString! mu
        let ml := if ml.isEmpty then none else some <| ofHexString! ml
        let mt := if mt.isEmpty then none else some <| ofHexString! mt
        (mu, ml, mt)
      | _ => panic! "invalid table data"

/-- Get decomposition mapping using lookup table

  Unicode properties:
    `Decomposition_Mapping`
    `Decomposition_Type` -/
def lookupDecompositionMapping? (c : UInt32) : Option DecompositionMapping :=
  -- Hangul syllables
  if Hangul.Syllable.base ≤ c && c ≤ Hangul.Syllable.last then
    let s := Hangul.getSyllable! c
    match s.getTChar? with
    | some t => some ⟨none, [s.getLVChar, t]⟩
    | none => some ⟨none, [s.getLChar, s.getVChar]⟩
  else
    let table := table.get
    if c < table[0]!.1 then none else
      match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
      | (v, t, l) =>
        if c == v then
          some <| .mk t (l.map fun c => Char.ofNat c.toNat).toList
        else
          none
where
  str : String := include_str "../data/table/Decomposition_Mapping.txt"
  table : Thunk <| Array (UInt32 × Option CompatibilityTag × Array UInt32) :=
    parseTable str fun _ x =>
      let tag :=
        if x[0]! == "" then none
        else if x[0]! == "<font>" then some .font
        else if x[0]! == "<noBreak>" then some .noBreak
        else if x[0]! == "<initial>" then some .initial
        else if x[0]! == "<medial>" then some .medial
        else if x[0]! == "<final>" then some .final
        else if x[0]! == "<isolated>" then some .isolated
        else if x[0]! == "<circle>" then some .circle
        else if x[0]! == "<super>" then some .super
        else if x[0]! == "<sub>" then some .sub
        else if x[0]! == "<vertical>" then some .vertical
        else if x[0]! == "<wide>" then some .wide
        else if x[0]! == "<narrow>" then some .narrow
        else if x[0]! == "<small>" then some .small
        else if x[0]! == "<square>" then some .square
        else if x[0]! == "<fraction>" then some .fraction
        else if x[0]! == "<compat>" then some .compat
        else panic! s!"invalid compatibility tag {x[0]!}"
      (tag, x[1:].toArray.map ofHexString!)

/-- Get general category of a code point using lookup table

  Unicode property: `General_Category` -/
def lookupGeneralCategory (c : UInt32) : GeneralCategory :=
  let table := Table.GeneralCategory
  if c < table[0]!.1 then .Cn else
    match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
    | (_, v, gc) =>
      if c ≤ v then
        if gc == .LC then
          if c &&& 1 == 0 then .Lu else .Ll
        else if gc == .PG then
          if c &&& 1 == 0 then .Ps else .Pe
        else if gc == .PQ then
          if c &&& 1 == 0 then .Pi else .Pf
        else gc
      else GeneralCategory.Cn

/-- Get name of a code point using lookup table

  Unicode property: `Name` -/
def lookupName (c : UInt32) : String :=
  let table := table.get
  if c < table[0]!.1 then unreachable! else
    match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
    | (_, v, d) =>
      if c ≤ v then
        if d.get 0 == '<' then
          if d == "<Control>" then
            s!"<control-{toHexStringAux c}>"
          else if d == "<Private Use>" then
            s!"<private-use-{toHexStringAux c}>"
          else if d == "<Reserved>" then
            s!"<reserved-{toHexStringAux c}>"
          else if d == "<Surrogate>" then
            s!"<surrogate-{toHexStringAux c}>"
          else if d == "<CJK Unified Ideograph>" then
            "CJK UNIFIED IDEOGRAPH-" ++ toHexStringAux c
          else if d == "<CJK Compatibility Ideograph>" then
            "CJK COMPATIBILITY IDEOGRAPH-" ++ toHexStringAux c
          else if d == "<Hangul Syllable>" then
            "HANGUL SYLLABLE " ++ (Hangul.getSyllable! c).getShortName
          else if d == "<Khitan Small Script Character>" then
            "KHITAN SMALL SCRIPT CHARACTER-" ++ toHexStringAux c
          else if d == "<Nushu Character>" then
            "NUSHU CHARACTER-" ++ toHexStringAux c
          else if d == "<Tangut Component>" then
            let i := toString <| c.toNat - 0x18800 + 1
            let i :=
              if i.length == 1 then "00" ++ i
              else if i.length == 2 then "0" ++ i
              else i
            "TANGUT COMPONENT-" ++ i
          else if d == "<Tangut Ideograph>" then
            "TANGUT IDEOGRAPH-" ++ toHexStringAux c
          else panic! s!"unknown name range {d}"
        else d.toString
      else s!"<noncharacter-{toHexStringAux c}>"
where
  str : String := include_str "../data/table/Name.txt"
  table : Thunk <| Array (UInt32 × UInt32 × Substring) :=
    parseDataTable str fun _ _ x => x[0]!

/-- Get numeric value of a code point using lookup table

  Unicode properties:
    `Numeric_Type`
    `Numeric_Value` -/
def lookupNumericValue (c : UInt32) : Option NumericType :=
  let table := Table.NumericalValue
  if c < table[0]!.1 then none else
    match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
    | (c₀, _, .decimal _) =>
      let val := c.toNat - c₀.toNat
      if h : val < 10 then
        some <| NumericType.decimal ⟨val, h⟩
      else
        none
    | (c₀, c₁, .digit i) =>
      if c ≤ c₁ then
        let val := c.toNat - c₀.toNat + i.val
        if h : val < 10 then
          some <| NumericType.digit ⟨val, h⟩
        else
          panic! "invalid `Numeric_Value` table"
      else
        none
    | ⟨v, _, n⟩ =>
      if c == v then some n else none

/-! Properties -/

/-- Check if code point is alphabetic using lookup table

  Unicode property: `Alphabetic` -/
def lookupAlphabetic (c : UInt32) : Bool :=
  let table := Table.Alphabetic
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
    | (_, v) => c ≤ v

/-- Check if code point is bidi mirrored using lookup table

  Unicode property: `Bidi_Mirrored`
-/
def lookupBidiMirrored (c : UInt32) : Bool :=
  let table := Table.BidiMirrored
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
    | (_, v) => c ≤ v

/-- Check if code point is a cased letter using lookup table

  Unicode property: `Cased` -/
def lookupCased (c : UInt32 ) : Bool :=
  let table := Table.Cased
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
    | (_, v) => c ≤ v

/-- Check if code point is a lowercase letter using lookup table

  Unicode property: `Lowercase` -/
def lookupLowercase (c : UInt32) : Bool :=
  let table := Table.Lowercase
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
    | (_, v) => c ≤ v

/-- Check if code point is a mathematical symbol using lookup table

  Unicode property: `Math` -/
def lookupMath (c : UInt32) : Bool :=
  let table := Table.Math
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
    | (_, v) => c ≤ v

/-- Check if code point is a titlecase letter using lookup table

  Unicode property: `Titlecase` -/
def lookupTitlecase (c : UInt32) : Bool :=
  let table := Table.Titlecase
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
    | (_, v) => c ≤ v

/-- Check if code point is a uppercase letter using lookup table

  Unicode property: `Uppercase` -/
def lookupUppercase (c : UInt32) : Bool :=
  let table := Table.Uppercase
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
    | (_, v) => c ≤ v

/-- Check if code point is a white space character using lookup table

  Unicode property: `White_Space` -/
def lookupWhiteSpace (c : UInt32) : Bool :=
  let table := Table.WhiteSpace
  if c < table[0]!.1 then false else
    match table[find c (fun i => table[i]!.1) 0 table.size.toUSize]! with
    | (_, v) => c ≤ v

end Unicode
