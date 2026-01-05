------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          X T R E E _ D E C L S                           --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2026, AdaCore                     --
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

with GNATCOLL.Utils; use GNATCOLL.Utils;
with Xkind_Tables;   use Xkind_Tables;
with Xtree_Tables;   use Xtree_Tables;
with Why.Sinfo;      use Why.Sinfo;

package body Xtree_Decls is

   function Layout (Fields : Node_Lists.List) return Node_Lists.List;
   --  Layout Fields to minimize memory usage

   ------------
   -- Layout --
   ------------

   function Layout (Fields : Node_Lists.List) return Node_Lists.List is
      type Field_Size is record
         Prefix : not null Xtree_Tables.String_Access;
         Size   : Natural;
      end record;
      --  Relates field with Prefix to its Size

      Field_Sizes : constant array (Positive range <>) of Field_Size :=
        ((Prefix => new String'("Boolean"),         Size =>   7),
         (Prefix => new String'("Node_Id"),         Size =>  31),
         (Prefix => new String'("Source_Ptr"),      Size =>  31),
         (Prefix => new String'("String_Sets.Set"), Size => 255),
         (Prefix => new String'("Uint"),            Size =>  31),
         (Prefix => new String'("Ureal"),           Size =>  31),
         (Prefix => new String'("EW_"),             Size =>   7),
         (Prefix => new String'("W_"),              Size =>  31),
         (Prefix => new String'("Symbol"),          Size => 127),
         (Prefix => new String'("Why_Node_Set"),    Size =>  31));
      --  These values come from switch -gnatR on x86_64 GNU/Linux

      function "<" (Left, Right : Field_Info) return Boolean;
      --  Order fields according to their size

      ---------
      -- "<" --
      ---------

      function "<" (Left, Right : Field_Info) return Boolean is
         Left_Size, Right_Size : Natural := 0;
      begin
         --  Pick fields sizes from the table

         for Pair of Field_Sizes loop
            if Left_Size = 0
              and then Starts_With (Left.Field_Type.all, Pair.Prefix.all)
            then
               Left_Size := Pair.Size;
               exit when Right_Size > 0;
            end if;
            if Right_Size = 0
              and then Starts_With (Right.Field_Type.all, Pair.Prefix.all)
            then
               Right_Size := Pair.Size;
               exit when Left_Size > 0;
            end if;
         end loop;

         pragma Assert (Left_Size > 0 and Right_Size > 0);

         --  Compare the sizes

         if Left_Size = Right_Size then
            return Left.Field_Name.all < Right.Field_Name.all;
         else
            return Left_Size < Right_Size;
         end if;
      end "<";

      package Size_Sorting is new Node_Lists.Generic_Sorting ("<");

      Result : Node_Lists.List := Fields;

   begin
      --  We simply order fields from the smallest to the largest. This might
      --  miss some subtleties of optimal layout wrt to alignment, but is
      --  already better than layout that comes from the API description.

      Size_Sorting.Sort (Result);

      return Result;
   end Layout;

   Node_Kind_Name : constant String := "Why_Node_Kind";
   Node_Type_Name : constant String := "Why_Node";
   Kind_Name      : constant String := "Kind";

   ---------------------
   -- Print_Node_Type --
   ---------------------

   procedure Print_Node_Type (O : in out Output_Record) is
      use Node_Lists;
   begin
      PL (O, "type " & Node_Type_Name
          & " (" & Kind_Name  & " : " & Node_Kind_Name & ")"
          & " is record");
      Relative_Indent (O, 3);

      PL (O, "--  Basic type for nodes in the abstract syntax tree.");

      NL (O);
      Print_Box (O, "Common Fields");
      NL (O);

      PL (O, "--  Fields that are shared amongst all node kinds");
      NL (O);

      for FI of Layout (Common_Fields.Fields) loop
         PL (O, Field_Name (FI)  & " : " & Type_Name (FI, Opaque)  & ";");
         NL (O);
      end loop;

      Print_Box (O, "Variant Part");
      NL (O);

      PL (O, "case " & Kind_Name & " is");
      Relative_Indent (O, 3);

      for Kind in Why_Tree_Info'Range loop
         PL (O, "when " & Mixed_Case_Name (Kind) & " =>");
         Relative_Indent (O, 3);

         if Is_Empty (Why_Tree_Info (Kind).Fields) then
            PL (O, "null;");
         else
            for FI of Layout (Why_Tree_Info (Kind).Fields) loop
               P (O, Field_Name (FI));
               Adjust_Columns (O,
                               Field_Name (FI)'Length,
                               Why_Tree_Info (Kind).Max_Field_Name_Length);
               PL (O, ": " & Type_Name (FI, Opaque)  & ";");
            end loop;
         end if;

         NL (O);
         Relative_Indent (O, -3);
      end loop;

      Relative_Indent (O, -3);
      PL (O, "end case;");
      Relative_Indent (O, -3);
      PL (O, "end record;");
   end Print_Node_Type;

end Xtree_Decls;
