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

   subtype Empty_Or_Subexpr_Id is Node_Id with
     Predicate => No (Empty_Or_Subexpr_Id)
       or else Empty_Or_Subexpr_Id in N_Subexpr_Id;

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

   subtype Empty_Or_Object_Kind_Id is Entity_Id with
     Predicate => No (Empty_Or_Object_Kind_Id)
       or else Empty_Or_Object_Kind_Id in Object_Kind_Id;

   subtype Empty_Or_Package_Id is Entity_Id with
     Predicate => No (Empty_Or_Package_Id)
       or else Empty_Or_Package_Id in E_Package_Id;

   subtype Empty_Or_Record_Field_Kind_Id is Entity_Id with
     Predicate => No (Empty_Or_Record_Field_Kind_Id)
       or else Empty_Or_Record_Field_Kind_Id in Record_Field_Kind_Id;

   subtype Empty_Or_Type_Kind_Id is Entity_Id with
     Predicate => No (Empty_Or_Type_Kind_Id)
       or else Empty_Or_Type_Kind_Id in Type_Kind_Id;

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

   subtype Subprogram_Id is N_Entity_Id with
     Predicate => Ekind (Subprogram_Id) in E_Function
                                         | E_Procedure
                                         | Entry_Kind;

   subtype Empty_Or_Subprogram_Kind_Id is Entity_Id with
     Predicate => No (Empty_Or_Subprogram_Kind_Id)
       or else Empty_Or_Subprogram_Kind_Id in Subprogram_Id;

end Checked_Types;
