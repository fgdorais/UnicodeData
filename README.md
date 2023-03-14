# Lean 4 / Unicode Basic

Lightweight Unicode support for Lean 4.

Unicode properties that are currently supported are:

* `Bidi_Class` and `Bidi_Mirrored`
* `Canonical_Combining_Class`
* `Decomposition_Type` and `Decomposition_Mapping`
* `General_Category`
* `Name`
* `Numeric_Type` and `Numeric_Value`
* `Simple_Lowercase_Mapping`, `Simple_Uppercase_Mapping`, and `Simple_Titlecase_Mapping`

To keep the library lightweight, only properties that can be derived exclusively from `UnicodeData.txt` using a minimum of additional data are supported.

## Installation

Add the following dependency to your project's `lakefile.lean`:

```lean
require UnicodeBasic from git
  "https://github.com/fgdorais/lean4-unicode-basic" @ "main"
```

Then add `import UnicodeBasic` at the top of any Lean file where you plan to use this library.

-----

* The Lean 4 Unicode Basic library is copyright © 2023 François G. Dorais. The library is released under the [Apache 2.0 license](http://www.apache.org/licenses/LICENSE-2.0). See the file LICENSE for additional details.
* The `UnicodeData.txt` file is copyright © 1991-2023 Unicode, Inc. The file is distributed under the [Unicode® Copyright and Terms of Use](https://www.unicode.org/copyright.html). See the file UNICODE-LICENSE for additional details.
