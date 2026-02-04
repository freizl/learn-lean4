import LearnLean4
import LSpec

open LSpec

def basicTests : TestSeq :=
  group "Test.test2" $
    test "doubles 5 to 10" (Test.test2 5 = 10) $
    test "doubles 0 to 0" (Test.test2 0 = 0) $
    test "doubles 1 to 2" (Test.test2 1 = 2) $
    .done
