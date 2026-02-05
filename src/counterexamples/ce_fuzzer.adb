------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    G N A T 2 W H Y _ C E _ F U Z Z E R                   --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2022-2026, AdaCore                     --
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

with Ada.Containers;    use Ada.Containers;
with Ada.Containers.Hashed_Maps;
with Ada.Containers.Vectors;
with Ada.Numerics.Discrete_Random;
with CE_RAC;            use CE_RAC;
with Common_Containers; use Common_Containers;
with Einfo.Entities;    use Einfo.Entities;
with SPARK_Atree;       use SPARK_Atree;
with SPARK_Util.Types;  use SPARK_Util.Types;

package body CE_Fuzzer is

   type Index_Type is new Natural;

   package Big_Integer_Vector is new
     Ada.Containers.Vectors
       (Index_Type   => Index_Type,
        Element_Type => Big_Integer);
   --  Vector of Big_Integers, used as collection of possible values.

   type Scalar_Fuzz_Values (K : CE_Values.Scalar_Kind := Integer_K) is record
      case K is
         when Integer_K =>
            Integer_Values : Big_Integer_Vector.Vector;

         when others =>
            null;
      end case;
   end record;
   --  In a similar fashion to Value_Types, distinguish between each kind of
   --  values.

   type Fuzz_Values (K : Value_Kind := Scalar_K) is record
      case K is
         when Scalar_K =>
            Scalar_Values : Scalar_Fuzz_Values;

         when others =>
            null;
      end case;
   end record;
   --  For each kind of Value_Type associate a set of possible values for each
   --  component of the type.

   package Type_To_Fuzz_Values_Map is new
     Ada.Containers.Hashed_Maps
       (Key_Type        => Entity_Id,
        Element_Type    => Fuzz_Values,
        Hash            => Node_Hash,
        Equivalent_Keys => "=");
   --  Associate to each type a set of values a variable of this type can have

   Values_To_Try : Type_To_Fuzz_Values_Map.Map;

   package Random_Index_Generator is new
     Ada.Numerics.Discrete_Random (Index_Type);

   Gen : Random_Index_Generator.Generator;
   --  A vector of values from which to choose is associated to each type. In
   --  order to avoid creating one generator per type, we instead create one
   --  generator to randomly choose a value of Index_Type.

   function Fuzz_Integer_Value (Ty : Entity_Id) return Value_Type is

      function Get_Random_Value
        (Values : Big_Integer_Vector.Vector; Ty : Entity_Id) return Value_Type;
      --  Return random element from the given values
      --
      --  Note: the real purpose of this routine is to repeatedly access the
      --  container with values, which is stored in a discriminant-dependent
      --  component. It would be illegal to create a renaming of this container
      --  and it would be inefficient to create its copy.

      ----------------------
      -- Get_Random_Value --
      ----------------------

      function Get_Random_Value
        (Values : Big_Integer_Vector.Vector; Ty : Entity_Id) return Value_Type
      is
         Nb_Values : constant Index_Type := Index_Type (Values.Length);

         --  Since not all types have the same number of values to choose from
         --  and creating one generator per vector length is impractical,
         --  the index in the vector is the remainder of the euclidean division
         --  of the random Index_Type by the number of possible values.

         Index : constant Index_Type :=
           Random_Index_Generator.Random (Gen) rem Nb_Values;
      begin
         return Integer_Value (Values (Index), Ty);
      end Get_Random_Value;

      Type_Pos : Type_To_Fuzz_Values_Map.Cursor;
      Inserted : Boolean;

   begin
      --  Initialize the variable with a value known to often highlight bugs

      Values_To_Try.Insert
        (Key => Ty, Position => Type_Pos, Inserted => Inserted);

      if Inserted then
         declare
            type Known_Values is array (1 .. 3) of Big_Integer;

            Other_Values : constant Known_Values := (-1, 0, 1);
            Values       : Big_Integer_Vector.Vector;
            Fst, Lst     : Big_Integer;
         begin
            --  Fill the vector with values we know often highlight bugs

            Get_Integer_Type_Bounds (Ty, Fst, Lst);
            Values.Append (Fst);
            Values.Append (Lst);

            for V of Other_Values loop
               if Fst <= V and then V <= Lst then
                  Values.Append (V);
               end if;
            end loop;

            Values_To_Try (Type_Pos) := (Scalar_K, (Integer_K, Values));
         end;
      end if;

      return
        Get_Random_Value
          (Values_To_Try (Type_Pos).Scalar_Values.Integer_Values, Ty);

   end Fuzz_Integer_Value;

   -----------------------
   -- Fuzz_Record_Value --
   -----------------------

   function Fuzz_Record_Value (Ty : Entity_Id) return Value_Type is
      Constrained  : constant Boolean := Has_Discriminants (Ty);
      Field        : Entity_Id := First_Component_Or_Discriminant (Ty);
      Field_Values : Entity_To_Value_Maps.Map;
   begin
      while Present (Field) loop
         declare
            Field_Ty : constant Entity_Id := Etype (Field);
         begin
            if Is_Integer_Type (Field_Ty) then
               Field_Values.Insert
                 (Field,
                  new Value_Type'(Fuzz_Integer_Value (Retysp (Field_Ty))));
            elsif Is_Record_Type (Field_Ty) then
               Field_Values.Insert
                 (Field,
                  new Value_Type'(Fuzz_Record_Value (Retysp (Field_Ty))));
            else
               RAC_Unsupported ("record field not integer or record", Field);
            end if;
            Next_Component_Or_Discriminant (Field);
         end;
      end loop;

      return
        Value_Type'
          (K                => Record_K,
           AST_Ty           => Ty,
           Record_Fields    => Field_Values,
           Constrained_Attr => (Present => True, Content => Constrained));
   end Fuzz_Record_Value;

end CE_Fuzzer;
