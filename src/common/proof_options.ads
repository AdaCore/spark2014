------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                         P R O O F _ O P T I O N S                        --
--                                                                          --
--                                  S p e c                                 --
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

with String_Utils;

package Proof_Options is

   Default_Steps : constant Natural := 100;
   --  Default step limit used when neither --steps nor --timeout is set

   subtype Proof_Level is Natural range 0 .. 4;

   type Prover_Set is (CVC5_Only, Main_Automatic_Provers);

   type Proof_Level_Settings is record
      Provers         : Prover_Set;
      Timeout         : Natural;
      Steps           : Natural;
      Memlimit        : Natural;
      Counterexamples : Boolean;
   end record;

   function Settings_For_Level
     (Level : Proof_Level) return Proof_Level_Settings;
   --  Return the proof settings implied by --level

   function Provers_For
     (Set : Prover_Set) return String_Utils.String_Lists.List;
   --  Return the prover names for Set, in command-line order

end Proof_Options;
