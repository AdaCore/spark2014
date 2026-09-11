------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--        F L O W . A N A L Y S I S . C O N T R A C T _ S A N I T Y         --
--                                                                          --
--                                S p e c                                   --
--                                                                          --
--                 Copyright (C) 2026, Capgemini Engineering                --
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

--  This package implements sanity checks that only depend on the declaration
--  of a subprogram and not on its body. Contrary to the checks in
--  Flow.Analysis.Sanity, they do not need a flow graph and so they also apply
--  to subprograms whose body is not in SPARK, which are never analysed by
--  flow.

private package Flow.Analysis.Contract_Sanity is

   procedure Check_User_Defined_Equality_Globals (E : Entity_Id)
   with
     Pre => Ekind (E) in E_Function | E_Procedure | Entry_Kind | E_Task_Type;
   --  Check that a user-defined primitive equality operation on a record type
   --  has a Global aspect of null, unless the record type has only limited
   --  views. This enforces SPARK RM 6.6(1).

   procedure Check_Inputs_Of_Contract_Expressions (E : Entity_Id)
   with
     Pre => Ekind (E) in E_Function | E_Procedure | Entry_Kind | E_Task_Type;
   --  Check that everything read at subprogram entry by a contract of E is an
   --  input of E, i.e. a formal of mode "in" or "in out" or a global of mode
   --  Input, In_Out or Proof_In. A precondition is evaluated once, on entry,
   --  before any statement of the body, and so is the prefix of a 'Old in a
   --  postcondition; reading anything else there means the profile or the
   --  Global contract does not describe E correctly.
   --
   --  When the body of E is in SPARK the same defects are reported from the
   --  flow graph, by Find_Use_Of_Uninitialized_Variables and by
   --  Check_Prefixes_Of_Attribute_Old, so this only runs when it is not. That
   --  covers a body with SPARK_Mode => Off and an imported subprogram, which
   --  has no body at all.

end Flow.Analysis.Contract_Sanity;
