/-
Copyright © 2023-2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lake
open Lake DSL

package UnicodeBasic where
  version := v!"1.1.0"
  description := "Basic Unicode support for Lean 4"
  keywords := #["unicode"]
  reservoir := true

@[default_target]
lean_lib UnicodeBasic

lean_lib UnicodeData

lean_exe lookup

lean_exe leanTables

lean_exe makeTables

@[test_driver]
lean_exe testTables

/-- Download datafile from the Unicode Character Database (UCD) -/
script downloadUCD (args) do
  let dir : System.FilePath := "./data"
  let url := "https://www.unicode.org/Public/UCD/latest/ucd/"
  let mut err : ExitCode := 0
  for file in args do
    IO.print s!"Downloading UCD/{file} ... "
    match ← download (url ++ file) (dir/file) |>.run with
    | .ok _ _ => IO.println "Done."
    | .error _ _ => IO.println "Failed!"; err := err + 1
  return err

/-- Update data files from the Unicode Character Database (UCD) -/
script updateUCD do downloadUCD ["ReadMe.txt", "UnicodeData.txt", "PropList.txt"]
