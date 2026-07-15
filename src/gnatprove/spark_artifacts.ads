------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                       S P A R K _ A R T I F A C T S                      --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2026, AdaCore                          --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnatprove is distributed  in the hope that  it will be useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General Public License  distributed with  gnatprove;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnatprove is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

with GPR2; use GPR2;
with GPR2.Build.Compilation_Unit;

package SPARK_Artifacts is

   --  Helpers mapping a compilation unit to the artifact files that
   --  gnatprove's analysis actions produce for it. Keeping the derivation in
   --  one place lets the analysis actions and the consumers of their output
   --  (such as the proof manifest generator) agree on file locations.

   function Artifacts_Base_Name
     (Unit : GPR2.Build.Compilation_Unit.Object) return Simple_Name;
   --  Base name (without extension) shared by the artifact files gnatprove
   --  produces for Unit. This accounts for the multi-unit object separator
   --  when Unit is one of several units in a single source file.

   function SPARK_File_For_Unit
     (Unit : GPR2.Build.Compilation_Unit.Object) return String;
   --  Full path of the .spark file that the analysis action produces for Unit,
   --  namely Artifacts_Base_Name (Unit) & ".spark" under the object directory
   --  of Unit's owning view. The file may be absent if the action has not run
   --  or failed; callers must check existence before use.

end SPARK_Artifacts;
