------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                       X T R E E _ B U I L D E R S                        --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2021, AdaCore                     --
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
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Why.Sinfo;     use Why.Sinfo;
with Xtree_Tables;  use Xtree_Tables;
with Xkind_Tables;  use Xkind_Tables;

package body Xtree_Builders is

   New_Node      : constant String := "New_Node";
   New_Node_Id   : constant String := "New_Id";

   procedure Print_Builder_Declaration
     (O           : in out Output_Record;
      Kind        : Why_Node_Kind;
      IK          : Id_Kind;
      Return_Type : String);
   --  Print builder declaration for the given node kind

   procedure Print_Builder_Specification
     (O           : in out Output_Record;
      Kind        : Why_Node_Kind;
      IK          : Id_Kind;
      Return_Type : String);
   --  Ditto, but with a return type that is different from the
   --  default one.

   procedure Print_Builder_Body
     (O    : in out Output_Record;
      Kind : Why_Node_Kind;
      IK   : Id_Kind);
   --  Print builder body for the given node kind

   procedure Print_Builder_Body
     (O           : in out Output_Record;
      Kind        : Why_Node_Kind;
      IK          : Id_Kind;
      Return_Type : String);
   --  Ditto, but with a return type that is different from the
   --  default one.

   procedure Print_Builder_Implementation
     (O           : in out Output_Record;
      Kind        : Why_Node_Kind;
      IK          : Id_Kind;
      Return_Type : String := "");
   --  Print the handled sequence of statements that implements this builder

   procedure Print_Builder_Local_Declarations
     (O    : in out Output_Record;
      Kind : Why_Node_Kind;
      IK   : Id_Kind);
   --  Print the local declarations in builder body

   ------------------------
   -- Print_Builder_Body --
   ------------------------

   procedure Print_Builder_Body
     (O    : in out Output_Record;
      Kind : Why_Node_Kind;
      IK   : Id_Kind) is
   begin
      Print_Builder_Body (O, Kind, IK, Id_Subtype (Kind, IK));
   end Print_Builder_Body;

   procedure Print_Builder_Body
     (O           : in out Output_Record;
      Kind        : Why_Node_Kind;
      IK          : Id_Kind;
      Return_Type : String)
   is
      BN : constant String := Builder_Name (Kind, IK);
   begin
      Print_Box (O, BN);
      NL (O);

      Print_Builder_Specification (O, Kind, IK, Return_Type);
      NL (O);
      PL (O, "is");
      Relative_Indent (O, 3);
      Print_Builder_Local_Declarations (O, Kind, IK);
      Relative_Indent (O, -3);
      PL (O, "begin");
      Relative_Indent (O, 3);
      Print_Builder_Implementation (O, Kind, IK, Return_Type);
      Relative_Indent (O, -3);
      PL (O, "end " & BN & ";");
   end Print_Builder_Body;

   -------------------------------
   -- Print_Builder_Declaration --
   -------------------------------

   procedure Print_Builder_Declaration
     (O           : in out Output_Record;
      Kind        : Why_Node_Kind;
      IK          : Id_Kind;
      Return_Type : String)
   is
   begin
      Print_Builder_Specification (O, Kind, IK, Return_Type);
      PL (O, ";");
   end Print_Builder_Declaration;

   ----------------------------------
   -- Print_Builder_Implementation --
   ----------------------------------

   procedure Print_Builder_Implementation
     (O           : in out Output_Record;
      Kind        : Why_Node_Kind;
      IK          : Id_Kind;
      Return_Type : String := "")
   is
      use Node_Lists;

      Variant_Part : constant Why_Node_Info := Why_Tree_Info (Kind);

      function K (S : String) return String;
      --  If IK /= Derived, return S. Otherwise, prefix S by a call to
      --  a conversion.

      procedure Print_Record_Initialization (Position : Cursor);

      -------
      -- K --
      -------

      function K (S : String) return String is
      begin
         if IK = Derived then
            return Return_Type & " (" & S & ")";
         else
            return S;
         end if;
      end K;

      ---------------------------------
      -- Print_Record_Initialization --
      ---------------------------------

      procedure Print_Record_Initialization (Position : Cursor) is
         FI : constant Field_Info := Element (Position);
         FN : constant String := Field_Name (FI);

         function K (S : String) return String;
         --  If IK is Derived or FI is a Why Id, prefix S by a call to a
         --  conversion operator ("+").

         -------
         -- K --
         -------

         function K (S : String) return String is
         begin
            if IK = Derived and Is_Why_Id (FI) then
               declare
                  M : constant Id_Multiplicity :=
                        (if Multiplicity (FI) = Id_One
                           or else Multiplicity (FI) = Id_Some
                         then
                           Id_One
                         else
                           Id_Lone);
               begin
                  return "+("
                    & Id_Subtype (Node_Kind (FI), Regular, M)
                    & " (" & S & "))";
               end;
            else
               return S;
            end if;
         end K;

      begin
         if IK = Unchecked or else Field_Kind (FI) = Field_Special then
            PL (O, New_Node & "." & FN & " :=");

            if Has_Default_Value (Kind, FI, IK, In_Builder_Body) then
               P (O, "  " & Default_Value (Kind, FI, IK, In_Builder_Body));
            else
               P (O, "  " & Param_Name (FI));
            end if;

            PL (O, ";");

         elsif Field_Kind (FI) = Field_Domain
           and then Is_Domain (Return_Type)
         then
            PL (O, New_Node & "." & FN & " := "
                & Mixed_Case_Name (Get_Domain (Return_Type)) & ";");

         elsif Field_Kind (FI) = Field_Domain
           and then Get_Domain (Kind) /= EW_Expr
         then
            PL (O, New_Node & "." & FN & " := "
                & Mixed_Case_Name (Get_Domain (Kind)) & ";");

         else
            if Is_List (FI) then
               if not Maybe_Null (FI) then
                  PL (O, "pragma Assert ("
                      & Param_Name (FI) & "'Length > 0);");
               end if;

               PL (O, New_Node & "." & FN & " := New_List;");
               PL (O, "for J in " & Param_Name (FI) & "'Range loop");
               Relative_Indent (O, 3);
               PL (O, "pragma Assert");
               PL (O, "  (" & Kind_Check (Node_Kind (FI), Id_One));
               PL (O, "   (" & K (Param_Name (FI)  & " (J)") & "));");
               PL (O, "pragma Assert");
               PL (O, "  (" & Tree_Check (Node_Kind (FI), Id_One));
               PL (O, "   (" & K (Param_Name (FI)  & " (J)") & "));");
               PL (O, List_Op_Name (Op_Append));
               PL (O, "  (" & New_Node & "." & FN & ",");
               PL (O, "   " & K (Param_Name (FI) & " (J)") & ");");
               Relative_Indent (O, -3);
               PL (O, "end loop;");
            else
               PL (O, New_Node & "." & FN & " :=");
               P (O, "  " & K (Param_Name (FI)));
               PL (O, ";");
            end if;
         end if;

         if Is_Why_Id (FI) then
            PL (O, "Set_Link (" & New_Node & "." & FN
                & ", " & New_Node_Id & ");");
         end if;
      end Print_Record_Initialization;

   --  Start of processing for Print_Builder_Implementation

   begin
      Common_Fields.Fields.Iterate (Print_Record_Initialization'Access);
      Variant_Part.Fields.Iterate (Print_Record_Initialization'Access);
      PL (O, "Set_Node (" & New_Node_Id & ", " & New_Node & ");");
      PL (O, "return " & K (New_Node_Id) & ";");
   end Print_Builder_Implementation;

   --------------------------------------
   -- Print_Builder_Local_Declarations --
   --------------------------------------

   procedure Print_Builder_Local_Declarations
     (O    : in out Output_Record;
      Kind : Why_Node_Kind;
      IK   : Id_Kind) is
   begin
      PL (O, New_Node & " : Why_Node (" & Mixed_Case_Name (Kind)  & ");");
      PL (O, New_Node_Id & " : constant Why_Node_Id :=");
      PL (O, "  New_Why_Node_Id (" & Mixed_Case_Name (Kind)  & ");");
      PL (O, Checked_Default_Value & " : constant Boolean :=");

      if IK = Unchecked then
         PL (O, "  False;");
      else
         PL (O, "  True;");
      end if;
   end Print_Builder_Local_Declarations;

   ---------------------------------
   -- Print_Builder_Specification --
   ---------------------------------

   procedure Print_Builder_Specification
     (O           : in out Output_Record;
      Kind        : Why_Node_Kind;
      IK          : Id_Kind;
      Return_Type : String)
   is
      use Node_Lists;

      Variant_Part  : constant Why_Node_Info :=
                        Why_Tree_Info (Kind);
      Max_Param_Len : Natural;
      Field_Number  : Positive := 1;

      procedure Print_Parameter_Specification (Position : Cursor);

      -----------------------------------
      -- Print_Parameter_Specification --
      -----------------------------------

      procedure Print_Parameter_Specification (Position : Cursor)
      is
         Name_Len : Natural;
         FI       : constant Field_Info := Element (Position);
         PN       : constant String := Param_Name (FI);
      begin
         if Field_Kind (FI) = Field_Special then
            return;
         end if;

         if Field_Kind (FI) = Field_Domain
           and then Is_Domain (Return_Type)
         then
            return;
         end if;

         if Field_Kind (FI) = Field_Domain
           and then Get_Domain (Kind) /= EW_Expr
         then
            return;
         end if;

         if IK = Unchecked then
            if Has_Default_Value (Kind, FI, IK, In_Builder_Spec) then
               return;
            end if;
         end if;

         if Field_Number = 1 then
            P (O, "(");
            Relative_Indent (O, 1);
         else
            PL (O, ";");
         end if;

         P (O, PN);
         Name_Len := PN'Length;

         --  Align columns

         if IK = Unchecked then
            P (O, " ");
         else
            Adjust_Columns (O, Name_Len, Max_Param_Len);
         end if;

         P (O, ": ");

         if IK = Unchecked then
            P (O, Builder_Param_Type (FI, Regular, In_Builder_Spec));
         else
            P (O, Builder_Param_Type (FI, IK, In_Builder_Spec));
         end if;

         if Has_Default_Value (Kind, FI, IK, In_Builder_Spec) then
            P (O, " := ");
            P (O, Default_Value (Kind, FI, IK, In_Builder_Spec));
         end if;

         Field_Number := Field_Number + 1;
      end Print_Parameter_Specification;

   --  Start of processing for Print_Builder_Specification

   begin
      Max_Param_Len := Max_Param_Length (Kind);
      PL (O, "function " & Builder_Name (Kind, IK));
      Relative_Indent (O, 2);

      Common_Fields.Fields.Iterate (Print_Parameter_Specification'Access);
      Variant_Part.Fields.Iterate (Print_Parameter_Specification'Access);

      if Field_Number > 1 then
         PL (O, ")");
         Relative_Indent (O, -1);
      end if;

      P (O, "return " & Return_Type);
      Relative_Indent (O, -2);
   end Print_Builder_Specification;

   -------------------------------------------
   -- Print_Class_Wide_Builder_Declarations --
   -------------------------------------------

   procedure Print_Class_Wide_Builder_Declarations (O : in out Output_Record)
   is
   begin
      for Kind in Valid_Kind'Range loop
         Print_Builder_Declaration (O, Kind, Derived,
                                    Id_Subtype (Kind, Derived));

         for CI of Classes loop
            if Kind in Class_First (CI) .. Class_Last (CI)
              and Class_Name (CI) /= "W_Any_Node"
            then
               NL (O);

               Print_Builder_Declaration (O, Kind, Derived,
                                          Id_Subtype (Class_Name (CI),
                                                      Derived));
            end if;
         end loop;

         if Kind /= Valid_Kind'Last then
            NL (O);
         end if;
      end loop;
   end Print_Class_Wide_Builder_Declarations;

   -------------------------------------
   -- Print_Class_Wide_Builder_Bodies --
   -------------------------------------

   procedure Print_Class_Wide_Builder_Bodies (O : in out Output_Record) is
   begin
      for Kind in Valid_Kind'Range loop
         Print_Builder_Body (O, Kind, Derived,
                             Id_Subtype (Kind, Derived));

         for CI of Classes loop
            if Kind in Class_First (CI) .. Class_Last (CI)
              and Class_Name (CI) /= "W_Any_Node"
            then
               NL (O);
               Print_Builder_Body (O, Kind, Derived,
                                   Id_Subtype (Class_Name (CI), Derived));
            end if;
         end loop;

         if Kind /= Valid_Kind'Last then
            NL (O);
         end if;
      end loop;
   end Print_Class_Wide_Builder_Bodies;

   ------------------------------------
   -- Print_Unchecked_Builder_Bodies --
   ------------------------------------

   procedure Print_Unchecked_Builder_Bodies (O : in out Output_Record) is
      First : Boolean := True;
   begin
      for J in Valid_Kind'Range loop
         if Is_Mutable (J) then
            if First then
               First := False;
            else
               NL (O);
            end if;

            Print_Builder_Body (O, J, Unchecked);
         end if;
      end loop;
   end Print_Unchecked_Builder_Bodies;

   ------------------------------------------
   -- Print_Unchecked_Builder_Declarations --
   ------------------------------------------

   procedure Print_Unchecked_Builder_Declarations
     (O  : in out Output_Record)
   is
      First : Boolean := True;
   begin
      for J in Valid_Kind'Range loop
         if Is_Mutable (J) then
            if First then
               First := False;
            else
               NL (O);
            end if;

            Print_Builder_Declaration (O, J, Unchecked,
                                       Id_Subtype (J, Unchecked));
         end if;
      end loop;
   end Print_Unchecked_Builder_Declarations;

end Xtree_Builders;
