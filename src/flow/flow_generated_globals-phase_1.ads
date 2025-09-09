------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--       F L O W . G E N E R A T E D _ G L O B A L S . P H A S E _ 1        --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--              Copyright (C) 2014-2025, Capgemini Engineering              --
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

with Flow_Generated_Globals.Partial; use Flow_Generated_Globals.Partial;
with Flow_Visibility;                use Flow_Visibility;
with Sinfo.Nodes;                    use Sinfo.Nodes;
with SPARK_Util;                     use SPARK_Util;

with Flow_Generated_Globals.ALI_Serialization;
use Flow_Generated_Globals.ALI_Serialization;
with SPARK_Atree.Entities;

package Flow_Generated_Globals.Phase_1 is

   -----------------
   -- Registering --
   -----------------

   procedure GG_Register_Constant_Calls
     (E : Entity_Id; Calls : Node_Lists.List)
   with
     Pre  =>
       GG_Mode = GG_Write_Mode
       and then Ekind (E) = E_Constant
       and then (for all C of Calls =>
                   Ekind (C) in E_Function | E_Procedure
                   and then not Is_In_Analyzed_Files (C)),
     Post => GG_Mode = GG_Write_Mode;

   procedure GG_Register_Calls
     (E : Entity_Id; Calls : Node_Sets.Set; Kind : ALI_Entry_Kind)
   with
     Pre  =>
       GG_Mode = GG_Write_Mode
       and then Ekind (E)
                in Entry_Kind
                 | E_Function
                 | E_Package
                 | E_Procedure
                 | E_Task_Type
       and then (for all C of Calls =>
                   Ekind (C)
                   in Entry_Kind | E_Function | E_Package | E_Procedure)
       and then Kind in EK_Direct_Calls | EK_Proof_Dependencies,
     Post => GG_Mode = GG_Write_Mode;
   --  Register Calls as direct calls or proof dependencies depending on Kind,
   --  without caring if they are proof-only, definite or conditional.

   procedure GG_Register_Locking_Calls
     (E : Entity_Id; Calls : Tasking_Info_Ext)
   with
     Pre  =>
       GG_Mode = GG_Write_Mode
       and then Ekind (E)
                in Entry_Kind
                 | E_Function
                 | E_Package
                 | E_Procedure
                 | E_Task_Type
       and then (for all C in Calls.Iterate =>
                   (declare
                      PO     : constant Entity_Id :=
                        Locking_Target_Maps.Key (C).Object;
                      PT     : constant Entity_Id :=
                        Locking_Target_Maps.Key (C).Typ;
                      Callee : Entity_Id renames Calls (C);
                    begin
                      Ekind (PO) = E_Variable
                      and then SPARK_Atree.Entities.Is_Protected_Type (PT)
                      and then Scope (Callee) = PT)),
     Post => GG_Mode = GG_Write_Mode;
   --  Register locking calls made from E as one or more entries of the
   --  following form:
   --  * Caller     - The entity E
   --  * Obj        - The object or (in case of a record object) a protected
   --                 component that is being locked
   --  * Typ        - Type of the locked object or its protected component that
   --                 is locked
   --  * Operation  - The protected operation that belongs to Typ and is called
   --                 by E

   procedure GG_Register_Global_Info
     (E                 : Entity_Id;
      Local             : Boolean;
      Is_Protected      : Boolean;
      Is_Library_Level  : Boolean;
      Origin            : Globals_Origin_T;

      Globals           : Flow_Nodes;

      Local_Packages    : Node_Sets.Set;
      Local_Variables   : Node_Sets.Set;

      Entries_Called    : Entry_Call_Sets.Set;
      Tasking           : Tasking_Info;
      Tasking_Ext       : Tasking_Info_Ext;

      Always_Terminates : Boolean;
      Has_Subp_Variant  : Boolean;
      No_Body           : Boolean;
      Nonreturning      : Boolean;
      Nonblocking       : Boolean;
      Calls_Via_Access  : Boolean)
   with Pre => GG_Mode = GG_Write_Mode, Post => GG_Mode = GG_Write_Mode;
   --  Register information needed later to compute globals. It also stores
   --  information related to volatiles and remote states.

   procedure GG_Register_State_Refinement (E : Entity_Id)
   with
     Pre  => GG_Mode = GG_Write_Mode and then Ekind (E) = E_Package,
     Post => GG_Mode = GG_Write_Mode;
   --  Register information related to state abstractions and their
   --  refinements. This will later be used to return the appropriate view
   --  depending on the caller (as opposed to always returning the most
   --  refined view). It also stores information related to external states.

   procedure GG_Register_Task_Object
     (Typ : Entity_Id; Object : Entity_Id; Instances : Instance_Number)
   with Pre => GG_Mode = GG_Write_Mode, Post => GG_Mode = GG_Write_Mode;
   --  Register an instance of a task object

   procedure GG_Register_Flow_Scope (E : Entity_Id; Info : Hierarchy_Info_T)
   with Pre => GG_Mode = GG_Write_Mode, Post => GG_Mode = GG_Write_Mode;
   --  Register information about a flow scope of E

   -------------
   -- Writing --
   -------------

   procedure GG_Write_Initialize (GNAT_Root : Node_Id)
   with
     Pre  =>
       GG_Mode = GG_No_Mode and then Nkind (GNAT_Root) = N_Compilation_Unit,
     Post => GG_Mode = GG_Write_Mode;
   --  Must be called before the first call to GG_Write_Global_Info and
   --  GG_Write_Package_Info.

   procedure GG_Write_Finalize
   with Pre => GG_Mode = GG_Write_Mode, Post => GG_Mode = GG_No_Mode;
   --  Appends all collected information to the ALI file

   -------------
   -- Queries --
   -------------

   function Protected_Type_Priority (Typ : Entity_Id) return Priority_Value
   with Pre => SPARK_Atree.Entities.Is_Protected_Type (Typ);
   --  Return the priority associated to the protected type Typ

end Flow_Generated_Globals.Phase_1;
