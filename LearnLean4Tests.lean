-- Import all test modules here
import LSpec
import Tests.«00_BasicTests»

open LSpec

-- Entry point: `lake test`
def main := lspecIO $ .ofList [
    ("00_BasicTests", [basicTests])
  ]
