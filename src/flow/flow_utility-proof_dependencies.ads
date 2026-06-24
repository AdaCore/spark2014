------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--      F L O W _ U T I L I T Y . P R O O F _ D E P E N D E N C I E S       --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2024-2026, AdaCore                     --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
------------------------------------------------------------------------------

--  This package contains utilities related to proof dependencies.

with SPARK_Util.Types; use SPARK_Util.Types;

package Flow_Utility.Proof_Dependencies is

   procedure Process_Proof_Dependencies
     (Proof_Dependencies : Proof_Dependencies_Sets;
      Result             : out Node_Sets.Set);
   --  Run several analyses on entities contained in Proof_Dependencies to
   --  determine the final set of proof dependencies.

   procedure Process_Access_To_Subprogram_Contracts
     (Typ                : Entity_Id;
      Scop               : Flow_Scope;
      Proof_Dependencies : in out Proof_Dependencies_Sets;
      Generating_Globals : Boolean)
   with
     Pre => Is_Access_Subprogram_Type (Typ) and then No (Parent_Retysp (Typ));
   --  Fill Proof_Dependencies by analyzing the Pre and Post contracts from
   --  an access-to-subprogram type definition.

   procedure Process_Type_Contracts
     (Typ                : Entity_Id;
      Scop               : Flow_Scope;
      Include_Invariant  : Boolean;
      Proof_Dependencies : in out Proof_Dependencies_Sets);
   --  Fill Proof_Dependencies by analyzing predicate and invariant expressions
   --  that apply to Typ. This also pulls contracts in access-to-subprograms
   --  types. Include_Invariant is used to determine whether a type invariant
   --  is pulled.
end Flow_Utility.Proof_Dependencies;
