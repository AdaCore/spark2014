------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         X T R E E _ T A B L E S                          --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010, AdaCore                        --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute it and/or modify it   --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnat2why is distributed in the hope that it will  be  useful,   --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Containers.Doubly_Linked_Lists;
with Why.Sinfo; use Why.Sinfo;

package Xtree_Tables is

   type String_Access is access Wide_String;

   type Field_Info is record
      Field_Name     : String_Access;
      Field_Type     : String_Access;
      Is_Why_Node_Id : Boolean;
      Is_List        : Boolean;
      Maybe_Null     : Boolean;
   end record;

   package Node_Lists is
      new Ada.Containers.Doubly_Linked_Lists (Element_Type => Field_Info,
                                              "=" => "=");

   type Why_Node_Info is record
      Max_Field_Name_Length : Natural := 0;
      Variant_Range_First   : Why_Node_Kind;
      Variant_Range_Last    : Why_Node_Kind;
      Fields                : Node_Lists.List;
   end record;

   Common_Fields : Why_Node_Info := (0,
                                     Why_Node_Kind'First,
                                     Why_Node_Kind'Last,
                                     Node_Lists.Empty_List);

   Why_Tree_Info : array (Why_Node_Kind) of Why_Node_Info;

   procedure New_Field (NI : in out Why_Node_Info; FI : Field_Info);

   function Max_Param_Length (Kind : Why_Node_Kind) return Natural;

   function Mixed_Case_Name (Kind : Why_Node_Kind) return Wide_String;
   function Builder_Name (Kind : Why_Node_Kind) return Wide_String;
   function Id_Type_Name (Kind : Why_Node_Kind) return Wide_String;
   function Id_Type_Name (Kind : Wide_String) return Wide_String;
   function List_Type_Name (Kind : Why_Node_Kind) return Wide_String;
   function List_Type_Name (Kind : Wide_String) return Wide_String;
   function Param_Name (Field_Name : Wide_String) return Wide_String;

   type Output_Record is private;

   function Open_Output return Output_Record;

   procedure Library_Level (O : in out Output_Record);
   procedure Relative_Indent (O : in out Output_Record; Diff : Integer);

   procedure P  (O : in out Output_Record; S : Wide_String);
   procedure PL (O : in out Output_Record; S : Wide_String);
   procedure NL (O : in out Output_Record);

private

   type Output_Record is record
      Indent   : Natural := 0;
      New_Line : Boolean := False;
   end record;

end Xtree_Tables;
