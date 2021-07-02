------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        C H E C K E D _ T Y P E S                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                Copyright (C) 2016-2021, Altran UK Limited                --
--                     Copyright (C) 2016-2021, AdaCore                     --
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

--  This package contains wrapper types around some of the front-end types (in
--  particular Node_Id and Entity_Id) with predicates that enforce various
--  assumptions.

with Atree;          use Atree;
with Einfo.Entities; use Einfo.Entities;
with Sinfo.Nodes;    use Sinfo.Nodes;
with Types;          use Types;

package Checked_Types is

   -----------------------
   -- Subtypes of nodes --
   -----------------------

   subtype Opt_N_Entry_Body_Id is Node_Id with
     Predicate => No (Opt_N_Entry_Body_Id)
       or else Opt_N_Entry_Body_Id in N_Entry_Body_Id;

   subtype Opt_N_Pragma_Id is Node_Id with
     Predicate => No (Opt_N_Pragma_Id)
       or else Opt_N_Pragma_Id in N_Pragma_Id;

   subtype Opt_N_Protected_Body_Id is Node_Id with
     Predicate => No (Opt_N_Protected_Body_Id)
       or else Opt_N_Protected_Body_Id in N_Protected_Body_Id;

   subtype Opt_N_Protected_Definition_Id is Node_Id with
     Predicate => No (Opt_N_Protected_Definition_Id)
       or else Opt_N_Protected_Definition_Id in N_Protected_Definition_Id;

   subtype Opt_N_Subexpr_Id is Node_Id with
     Predicate => No (Opt_N_Subexpr_Id)
       or else Opt_N_Subexpr_Id in N_Subexpr_Id;

   subtype Opt_N_Task_Body_Id is Node_Id with
     Predicate => No (Opt_N_Task_Body_Id)
       or else Opt_N_Task_Body_Id in N_Task_Body_Id;

   subtype Opt_N_Task_Definition_Id is Node_Id with
     Predicate => No (Opt_N_Task_Definition_Id)
       or else Opt_N_Task_Definition_Id in N_Task_Definition_Id;

   subtype N_Aggregate_Kind_Id is Node_Id with
     Predicate => N_Aggregate_Kind_Id in N_Aggregate_Id
                                       | N_Delta_Aggregate_Id
                                       | N_Extension_Aggregate_Id;

   subtype N_Call_Id is Node_Id with
     Predicate => N_Call_Id in N_Entry_Call_Statement_Id
                             | N_Subprogram_Call_Id;

   --------------------------
   -- Subtypes of entities --
   --------------------------

   subtype Opt_Object_Kind_Id is Entity_Id with
     Predicate => No (Opt_Object_Kind_Id)
       or else Opt_Object_Kind_Id in Object_Kind_Id;

   subtype Opt_Entry_Kind_Id is Entity_Id with
     Predicate => No (Opt_Entry_Kind_Id)
       or else Opt_Entry_Kind_Id in Entry_Kind_Id;

   subtype Opt_E_Package_Id is Entity_Id with
     Predicate => No (Opt_E_Package_Id)
       or else Opt_E_Package_Id in E_Package_Id;

   subtype Opt_Record_Field_Kind_Id is Entity_Id with
     Predicate => No (Opt_Record_Field_Kind_Id)
       or else Opt_Record_Field_Kind_Id in Record_Field_Kind_Id;

   subtype Opt_E_Task_Body_Id is Entity_Id with
     Predicate => No (Opt_E_Task_Body_Id)
       or else Opt_E_Task_Body_Id in E_Task_Body_Id;

   subtype Opt_E_Enumeration_Literal_Id is Entity_Id with
     Predicate => No (Opt_E_Enumeration_Literal_Id)
       or else Opt_E_Enumeration_Literal_Id in E_Enumeration_Literal_Id;

   subtype Opt_E_Component_Id is Entity_Id with
     Predicate => No (Opt_E_Component_Id)
       or else Opt_E_Component_Id in E_Component_Id;

   subtype Opt_E_Discriminant_Id is Entity_Id with
     Predicate => No (Opt_E_Discriminant_Id)
       or else Opt_E_Discriminant_Id in E_Discriminant_Id;

   subtype Opt_E_Procedure_Id is Entity_Id with
     Predicate => No (Opt_E_Procedure_Id)
       or else Opt_E_Procedure_Id in E_Procedure_Id;

   subtype Opt_Type_Kind_Id is Entity_Id with
     Predicate => No (Opt_Type_Kind_Id)
       or else Opt_Type_Kind_Id in Type_Kind_Id;

   --  Entities which may contain components or discriminants, like record
   subtype Record_Like_Kind_Id is Entity_Id with
     Predicate => Record_Like_Kind_Id in Private_Kind_Id
                                       | Protected_Kind_Id
                                       | Record_Kind_Id
                                       | Task_Kind_Id;

   -----------------
   -- Subprograms --
   -----------------

   --  In SPARK we also consider entries to be subprograms. We do not consider
   --  generics to be subprograms. We also exclude E_Operator here as we will
   --  never get this in SPARK (if the Expander works as intended).

   subtype Subprogram_Like_Kind_Id is N_Entity_Id with
     Predicate => Ekind (Subprogram_Like_Kind_Id) in E_Function
                                                   | E_Procedure
                                                   | Entry_Kind
                                                   | E_Subprogram_Type;

   subtype Opt_Subprogram_Like_Kind_Id is Entity_Id with
     Predicate => No (Opt_Subprogram_Like_Kind_Id)
       or else Opt_Subprogram_Like_Kind_Id in Subprogram_Like_Kind_Id;

end Checked_Types;
