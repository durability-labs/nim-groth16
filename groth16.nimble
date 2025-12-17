version     = "0.1.0"
author      = "Balazs Komuves"
description = "Groth16 proof system"
license     = "MIT OR Apache-2.0"

skipDirs    = @["groth16/example"]
binDir      = "build"
namedBin    = {"cli/cli_main": "nim-groth16"}.toTable()

requires "https://github.com/status-im/nim-taskpools"
requires "https://github.com/durability-labs/constantine#v0.2.0-fix-nimble-windows"
