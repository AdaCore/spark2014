--
--  Copyright (C) 2004-2026, Free Software Foundation, Inc.
--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

--  This package is the root of the model-free implementation layer of the
--  bounded formal containers. Each child Impl.<Container> carries the bare
--  data-structure implementation of the corresponding SPARK.Containers.Formal
--  container, in SPARK_Mode => On and proved at silver level (absence of
--  run-time errors), without the model-based gold contracts. The public
--  Formal.<Container> packages delegate to these units. See IMPL_SILVER_PLAN.md
--  for the overall design.

package SPARK.Containers.Formal.Impl
  with SPARK_Mode, Pure
is
end SPARK.Containers.Formal.Impl;
