--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--  Extracted and modified from BWT for this regression test.
--  Upstream repository: https://github.com/kanigsson/BWT
--  Upstream commit: 6de077aae657ca6057fb26056bb71b10a676f96f
--  See LICENSE.

package body BWT
  with SPARK_Mode
is
   subtype Rotation_Table is BWT.Table;

   function Initial_Rows (S : String) return Rotation_Table
   with
     Global => null,
     Pre    => Supported (S),
     Post   =>
       Initial_Rows'Result'First = 1
       and then Initial_Rows'Result'Last = S'Length
       and then (for all I in Initial_Rows'Result'Range =>
                   Initial_Rows'Result (I) = (1, S'Length, I - 1));

   function Initial_Rows (S : String) return Rotation_Table is
      Rows : Rotation_Table (1 .. S'Length);
   begin
      for I in Rows'Range loop
         Rows (I) := (First => 1, Length => S'Length, Offset => I - 1);
      end loop;
      return Rows;
   end Initial_Rows;

end BWT;
