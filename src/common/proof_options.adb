------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                         P R O O F _ O P T I O N S                        --
--                                                                          --
--                                  B o d y                                 --
--                                                                          --
--                     Copyright (C) 2026, AdaCore                          --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnatprove is distributed in the hope that it will be useful,   --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for more details. You should have received a copy of the GNU      --
-- General Public License distributed with gnatprove; see file COPYING3. If --
-- not, go to http://www.gnu.org/licenses for a complete copy of the         --
-- license.                                                                 --
--                                                                          --
-- gnatprove is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

package body Proof_Options is

   Level_Settings : constant array (Proof_Level) of Proof_Level_Settings :=
     [0 =>
        (Provers         => CVC5_Only,
         Timeout         => 1,
         Steps           => 0,
         Memlimit        => 1_000,
         Counterexamples => False),
      1 =>
        (Provers         => Main_Automatic_Provers,
         Timeout         => 1,
         Steps           => 0,
         Memlimit        => 1_000,
         Counterexamples => False),
      2 =>
        (Provers         => Main_Automatic_Provers,
         Timeout         => 5,
         Steps           => 0,
         Memlimit        => 1_000,
         Counterexamples => True),
      3 =>
        (Provers         => Main_Automatic_Provers,
         Timeout         => 20,
         Steps           => 0,
         Memlimit        => 2_000,
         Counterexamples => True),
      4 =>
        (Provers         => Main_Automatic_Provers,
         Timeout         => 60,
         Steps           => 0,
         Memlimit        => 2_000,
         Counterexamples => True)];

   -----------------
   -- Provers_For --
   -----------------

   function Provers_For
     (Set : Prover_Set) return String_Utils.String_Lists.List
   is
      Result : String_Utils.String_Lists.List;
   begin
      Result.Append ("cvc5");

      if Set = Main_Automatic_Provers then
         Result.Append ("z3");
         Result.Append ("altergo");
      end if;

      return Result;
   end Provers_For;

   ------------------------
   -- Settings_For_Level --
   ------------------------

   function Settings_For_Level
     (Level : Proof_Level) return Proof_Level_Settings is
   begin
      return Level_Settings (Level);
   end Settings_For_Level;

end Proof_Options;
