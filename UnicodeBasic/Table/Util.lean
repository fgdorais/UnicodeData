/-
Copyright © 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import UnicodeBasic.CharacterDatabase
import UnicodeBasic.Types

namespace Unicode

/-- Parse a simple table -/
def parseTable (s : String) (f : UInt32 → Array Substring → α) : Thunk <| Array (UInt32 × α) := Id.run do
  let mut r := #[]
  let mut stream := UCDStream.ofString s
  for record in stream do
    let start := ofHexString! record[0]!
    let val := f start record[1:]
    r := r.push (start, val)
  return r

/-- Parse a range compressed data table -/
def parseDataTable (s : String) (f : UInt32 → UInt32 → Array Substring → α) : Thunk <| Array (UInt32 × UInt32 × α) := Id.run do
  let mut r := #[]
  let mut stream := UCDStream.ofString s
  for record in stream do
    let start := ofHexString! record[0]!
    let stop := if record[1]!.isEmpty then start else ofHexString! record[1]!
    let val := f start stop record[2:]
    r := r.push (start, stop, val)
  return r

/-- Parse a range compressed property table -/
def parsePropTable (s : String) : Thunk <| Array (UInt32 × UInt32) := Id.run do
  let mut r := #[]
  let mut stream := UCDStream.ofString s
  for record in stream do
    let start := ofHexString! record[0]!
    let stop := if record[1]!.isEmpty then start else ofHexString! record[1]!
    r := r.push (start, stop)
  return r
