--
--  Copyright (C) 2004-2026, Free Software Foundation, Inc.
--
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--

pragma Ada_2022;

package body SPARK.Containers.Formal.Impl.Vectors
  with SPARK_Mode
is

   ------------
   -- Delete --
   ------------

   procedure Delete (Container : in out Vector; Index : Extended_Index) is
   begin
      Delete (Container, Index, 1);
   end Delete;

   procedure Delete
     (Container : in out Vector; Index : Extended_Index; Count : Count_Type)
   is
   begin
      null;
   end Delete;

end SPARK.Containers.Formal.Impl.Vectors;
