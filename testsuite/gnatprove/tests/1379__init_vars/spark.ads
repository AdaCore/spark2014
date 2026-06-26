--
--  Copyright (C) 2016-2026, AdaCore
--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

pragma Ada_2022;
pragma Assertion_Level (SPARKlib_Defensive);
--  Level for preconditions that can be enabled for runtime testing
pragma Assertion_Level (SPARKlib_Logic);
--  Level for ghost entities that are not executable in the light runtime
pragma Assertion_Level (SPARKlib_Full, Depends => [SPARKlib_Logic, Static]);
--  Level for postconditions and lemmas that have no reason to be enabled

package SPARK
  with SPARK_Mode, Pure
is

end SPARK;
