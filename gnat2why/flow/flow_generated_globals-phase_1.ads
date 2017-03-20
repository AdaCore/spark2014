------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--       F L O W . G E N E R A T E D _ G L O B A L S . P H A S E _ 1        --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--               Copyright (C) 2014-2017, Altran UK Limited                 --
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

with Atree;                use Atree;
with Einfo;                use Einfo;
with Sinfo;                use Sinfo;

package Flow_Generated_Globals.Phase_1 is

   -----------------
   -- Registering --
   -----------------

   procedure GG_Register_Direct_Calls (E : Entity_Id; Calls : Node_Sets.Set)
   with Pre  => GG_Mode = GG_Write_Mode and then
                Ekind (E) in Entry_Kind  |
                             E_Function  |
                             E_Package   |
                             E_Procedure |
                             E_Task_Type and then
                (for all C of Calls => Ekind (C) in Entry_Kind
                                                  | E_Function
                                                  | E_Package
                                                  | E_Procedure),
        Post => GG_Mode = GG_Write_Mode;
   --  Register direct calls without caring if they are proof-only, definite or
   --  conditional.

   procedure GG_Register_State_Refinement (Pkg_Body : Entity_Id)
   with Pre  => GG_Mode = GG_Write_Mode and then
                Ekind (Pkg_Body) = E_Package_Body,
        Post => GG_Mode = GG_Write_Mode;
   --  Register information related to state abstractions and their
   --  refinements. This will later be used to return the appropriate view
   --  depending on the caller (as opposed to always returning the most
   --  refined view). It also stores information related to external states.

   procedure GG_Register_Global_Info (GI : Global_Phase_1_Info)
   with Pre  => GG_Mode = GG_Write_Mode,
        Post => GG_Mode = GG_Write_Mode;
   --  Register information needed later to compute globals. It also stores
   --  information related to volatiles and remote states.

   procedure GG_Register_Nonblocking (EN : Entity_Name)
   with Pre  => GG_Mode = GG_Write_Mode,
        Post => GG_Mode = GG_Write_Mode;
   --  Register entity with no potentially blocking statements

   procedure GG_Register_Nonreturning (EN : Entity_Name)
   with Pre  => GG_Mode = GG_Write_Mode,
        Post => GG_Mode = GG_Write_Mode;
   --  Register nonreturning subprogram. This information will be used in
   --  phase 2 to determine termination of subprograms (when calling the
   --  function Is_Potentially_Nonreturning). In particular we register:
   --  * subprograms which contain possibly nonterminating loops
   --  * procedures annotated with No_Return
   --  * subprograms that call predefined procedures with No_Return
   --  * subprograms with body not in SPARK unless if they are:
   --    - predefined
   --    - imported
   --    - intrinsic
   --    - have no body yet and are not procedure annotated with No_Return.

   procedure GG_Register_Terminating (EN : Entity_Name)
   with Pre  => GG_Mode = GG_Write_Mode,
        Post => GG_Mode = GG_Write_Mode;
   --  Register subprograms with the Terminating annotation

   procedure GG_Register_Protected_Object (PO   : Entity_Name;
                                           Prio : Priority_Value)
   with Pre  => GG_Mode = GG_Write_Mode,
        Post => GG_Mode = GG_Write_Mode;
   --  Register protected object and its priority

   procedure GG_Register_Task_Object (Type_Name : Entity_Name;
                                      Object    : Task_Object)
   with Pre  => GG_Mode = GG_Write_Mode,
        Post => GG_Mode = GG_Write_Mode;
   --  Register an instance of a task object

   procedure GG_Register_Tasking_Info (Caller  : Entity_Name;
                                       Entries : Entry_Call_Sets.Set;
                                       Objects : Tasking_Info)
   with Pre  => GG_Mode = GG_Write_Mode,
        Post => GG_Mode = GG_Write_Mode;
   --  Register tasking-related information for entity

   procedure GG_Register_Max_Queue_Length (EN     : Entity_Name;
                                           Length : Nat)
   with Pre  => GG_Mode = GG_Write_Mode,
        Post => GG_Mode = GG_Write_Mode;
   --  Register the value of Max_Queue_Length for an entry

   -------------
   -- Writing --
   -------------

   procedure GG_Write_Initialize (GNAT_Root : Node_Id)
   with Pre  => GG_Mode = GG_No_Mode
        and then Nkind (GNAT_Root) = N_Compilation_Unit,
        Post => GG_Mode = GG_Write_Mode;
   --  Must be called before the first call to GG_Write_Global_Info and
   --  GG_Write_Package_Info.

   procedure GG_Write_Finalize
   with Pre => GG_Mode = GG_Write_Mode;
   --  Appends all collected information to the ALI file

end Flow_Generated_Globals.Phase_1;
