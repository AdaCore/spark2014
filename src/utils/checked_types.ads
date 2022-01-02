------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        C H E C K E D _ T Y P E S                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                Copyright (C) 2016-2022, Altran UK Limited                --
--                     Copyright (C) 2016-2022, AdaCore                     --
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

   subtype N_Aggregate_Kind_Id is Node_Id with
     Predicate => N_Aggregate_Kind_Id in N_Aggregate_Id
                                       | N_Delta_Aggregate_Id
                                       | N_Extension_Aggregate_Id;

   subtype N_Case_Kind_Id is Node_Id with
     Predicate => N_Case_Kind_Id in N_Case_Expression_Id
                                  | N_Case_Statement_Id;

   subtype N_Extended_Subexpr_Id is Node_Id with
     Predicate =>
       N_Extended_Subexpr_Id in N_Defining_Identifier_Id
                              | N_Subexpr_Id;

   subtype Opt_N_Extended_Subexpr_Id is Node_Id with
     Predicate => No (Opt_N_Extended_Subexpr_Id)
       or else Opt_N_Extended_Subexpr_Id in N_Extended_Subexpr_Id;

   subtype N_Identifier_Kind_Id is Node_Id with
     Predicate => N_Identifier_Kind_Id in N_Identifier_Id
                                        | N_Expanded_Name_Id;

   subtype N_Call_Id is Node_Id with
     Predicate => N_Call_Id in N_Entry_Call_Statement_Id
                             | N_Subprogram_Call_Id;

   subtype N_Raise_Kind_Id is Node_Id with
     Predicate => N_Raise_Kind_Id in N_Raise_xxx_Error_Id
                                   | N_Raise_Statement_Id
                                   | N_Raise_Expression_Id;

   --------------------------
   -- Subtypes of entities --
   --------------------------

   --  Entities which may contain components or discriminants, like record
   subtype Record_Like_Kind_Id is Entity_Id with
     Predicate => Record_Like_Kind_Id in Private_Kind_Id
                                       | Protected_Kind_Id
                                       | Record_Kind_Id
                                       | Task_Kind_Id;

   --  Extension of the notion of objects with protected types, which serve as
   --  placeholders for the corresponding "self" object during the analysis of
   --  protected operations.
   subtype Extended_Object_Kind_Id is Entity_Id with
     Predicate => Extended_Object_Kind_Id in Object_Kind_Id
                                           | Protected_Kind_Id;

   -----------------
   -- Subprograms --
   -----------------

   --  In SPARK we also consider entries to be subprograms. We do not consider
   --  generics to be subprograms. We also exclude E_Operator here as we will
   --  never get this in SPARK (if the Expander works as intended).

   subtype Callable_Kind_Id is Entity_Id with
     Predicate => Callable_Kind_Id in E_Function_Id
                                    | E_Procedure_Id
                                    | Entry_Kind_Id
                                    | E_Subprogram_Type_Id;

   subtype Opt_Callable_Kind_Id is Entity_Id with
     Predicate => No (Opt_Callable_Kind_Id)
       or else Opt_Callable_Kind_Id in Callable_Kind_Id;

   --  Runnable entities consist in callable entities plus task types, which
   --  are not directly called, but started during elaboration. These entities
   --  may have a Global/Depends contract.
   subtype Runnable_Kind_Id is Entity_Id with
     Predicate => Runnable_Kind_Id in Callable_Kind_Id
                                    | E_Task_Type_Id;

   subtype Opt_Runnable_Kind_Id is Entity_Id with
     Predicate => No (Opt_Runnable_Kind_Id)
       or else Opt_Runnable_Kind_Id in Runnable_Kind_Id;

   subtype Function_Kind_Id is Entity_Id with
     Predicate => Function_Kind_Id in E_Function_Id
                                    | E_Generic_Function_Id
                                    | E_Subprogram_Type_Id;

   subtype Package_Kind_Id is Entity_Id with
     Predicate => Package_Kind_Id in E_Package_Id
                                   | E_Generic_Package_Id;

   subtype Unit_Kind_Id is Entity_Id with
     Predicate => Unit_Kind_Id in Callable_Kind_Id
                                | E_Package_Id
                                | E_Protected_Type_Id
                                | E_Task_Type_Id;

   subtype Opt_Unit_Kind_Id is Entity_Id with
     Predicate => No (Opt_Unit_Kind_Id)
       or else Opt_Unit_Kind_Id in Unit_Kind_Id;

end Checked_Types;
