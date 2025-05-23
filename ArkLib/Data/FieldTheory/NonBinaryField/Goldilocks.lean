/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.NumberTheory.PrattCertificate

/-!
  # Goldilocks prime field `2^{64} - 2^{32} + 1`

  This is the field used in Plonky2/3.
-/

namespace Goldilocks

-- 2^{64} - 2^{32} + 1
notation "FIELD_SIZE" => 18446744069414584321

abbrev Field := ZMod FIELD_SIZE

theorem is_prime : Nat.Prime FIELD_SIZE := by pratt

end Goldilocks
