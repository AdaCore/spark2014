------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    G N A T 2 W H Y _ C E _ F U Z Z E R                   --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2022, AdaCore                        --
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

with Ada.Containers;               use Ada.Containers;
with Ada.Containers.Hashed_Maps;
with Ada.Containers.Vectors;
with Ada.Numerics.Discrete_Random;
with CE_RAC;                       use CE_RAC;
with Common_Containers;            use Common_Containers;
with Einfo.Entities;               use Einfo.Entities;
with SPARK_Atree;                  use SPARK_Atree;
with SPARK_Util.Types;             use SPARK_Util.Types;

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
      C : Type_To_Fuzz_Values_Map.Cursor := Values_To_Try.Find (Ty);
   begin
      --  Initialize the variable with a value known to often highlight bugs

      if not Type_To_Fuzz_Values_Map.Has_Element (C) then
         declare
            type Known_Values is array (1 .. 3) of Big_Integer;

            Other_Values : constant Known_Values := (-1, 0, 1);
            pragma Annotate
              (CodePeer, False_Positive,
               "access check",
               "there is no visible access type here");
            Values       :          Big_Integer_Vector.Vector;
            Fst, Lst     :          Big_Integer;
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

            Values_To_Try.Insert (Ty, (Scalar_K, (Integer_K, Values)));
            C := Values_To_Try.Find (Ty);
         end;
      end if;

      declare
         Values    : constant Big_Integer_Vector.Vector :=
           Type_To_Fuzz_Values_Map.Element (C).Scalar_Values.Integer_Values;
         Nb_Values : constant Index_Type := Index_Type (Values.Length);

         --  Since not all types have the same number of values to choose from
         --  and creating one generator per vector length is impractical,
         --  the index in the vector is the remainder of the euclidean division
         --  of the random Index_Type by the number of possible values.

         Index     : constant Index_Type :=
           Random_Index_Generator.Random (Gen) rem Nb_Values;

      begin
         return Integer_Value (Values (Index), Ty);
      end;

   end Fuzz_Integer_Value;

   -----------------------
   -- Fuzz_Record_Value --
   -----------------------

   function Fuzz_Record_Value (Ty : Entity_Id) return Value_Type
   is
      Constrained  : constant Boolean := Has_Discriminants (Ty);
      Field        :          Entity_Id :=
        First_Component_Or_Discriminant (Ty);
      Field_Values :          Entity_To_Value_Maps.Map;
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

      return Value_Type'(K                => Record_K,
                         AST_Ty           => Ty,
                         Record_Fields    => Field_Values,
                         Constrained_Attr => (Present => True,
                                              Content => Constrained));
   end Fuzz_Record_Value;

end CE_Fuzzer;
