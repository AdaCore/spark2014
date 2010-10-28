------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2SPARK COMPONENTS                          --
--                                                                          --
--                             B A C K _ E N D                              --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010, AdaCore                        --
--                                                                          --

-- gnat2spark is  free  software;  you can redistribute it and/or modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnat2spark is distributed in the hope that it will  be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- gnat2spark is maintained by AdaCore (http://www.adacore.com)             --
--                                                                          --
------------------------------------------------------------------------------

--  This is the SPARK target-dependent version of the Back_End package

with Gnat2SPARK.Driver;
with Adabkend;
with Stringt;
with Namet;

package body Back_End is

   package GNAT2SPARK is new Adabkend
     (Product_Name       => "GNAT2SPARK",
      Copyright_Years    => "2010",
      Driver             => Gnat2SPARK.Driver.GNAT_To_SPARK,
      Is_Back_End_Switch => Gnat2SPARK.Driver.Is_Back_End_Switch);

   -----------------------------
   -- Scan_Compiler_Arguments --
   -----------------------------

   procedure Scan_Compiler_Arguments is
   begin
      GNAT2SPARK.Scan_Compiler_Arguments;
   end Scan_Compiler_Arguments;

   -------------------
   -- Call_Back_End --
   -------------------

   procedure Call_Back_End (Mode : Back_End_Mode_Type) is
      pragma Unreferenced (Mode);
   begin
      --  Since the back end is called with all tables locked,
      --  first unlock any tables that we need to change.

      Stringt.Unlock;
      Namet.Unlock;

      GNAT2SPARK.Call_Back_End;

      --  Make sure to lock any unlocked tables again before returning

      Namet.Lock;
      Stringt.Lock;
   end Call_Back_End;

end Back_End;
