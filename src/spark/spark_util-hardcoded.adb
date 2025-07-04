------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   S P A R K _ U T I L - H A R D C O D E D                --
--                                                                          --
--                                  B o d y                                 --
--                                                                          --
--                     Copyright (C) 2020-2025, AdaCore                     --
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

with SPARK_Util.Types; use SPARK_Util.Types;
with Stand;            use Stand;

package body SPARK_Util.Hardcoded is

   function Is_Hardcoded_Unit
     (E : Entity_Id; Unit : Hardcoded_Enum) return Boolean;
   --  Return True if E is the package for the hardcoded unit Unit

   function Get_Hardcoded_Unit_Opt (E : Entity_Id) return Opt_Hardcoded_Enum;
   --  Returns the unit in which the hardcoded entity E is defined if any,
   --  No_Unit otherwise.

   -------------------------
   --  Get_Hardcoded_Unit --
   -------------------------

   function Get_Hardcoded_Unit (E : Entity_Id) return Hardcoded_Enum
   is (Get_Hardcoded_Unit_Opt (E));

   -----------------------------
   --  Get_Hardcoded_Unit_Opt --
   -----------------------------

   function Get_Hardcoded_Unit_Opt (E : Entity_Id) return Opt_Hardcoded_Enum is
      package BIN renames Big_Integers_Names;
      use BIN;
      package BRN renames Big_Reals_Names;
      use BRN;
      package COpN renames Cut_Operations_Names;
      use COpN;
      package SSEN renames System_Storage_Elements_Names;
      package RTN renames Real_Time_Names;
      use RTN;

   begin
      if Is_From_Hardcoded_Unit (E, Big_Integers) then
         if Chars (E)
            in Name_Op_Abs
             | Name_Op_Mod
             | Name_Op_Rem
             | Name_Op_Eq
             | Name_Op_Lt .. Name_Op_Subtract
             | Name_Op_Multiply .. Name_Op_Expon
           or else Get_Name_String (Chars (E))
                   in BIN.Big_Integer
                    | BIN.Min
                    | BIN.Max
                    | BIN.To_Big_Integer
                    | BIN.Is_Valid
                    | BIN.To_Integer
                    | BIN.Gcd
                    | BIN.From_String
         then
            return Big_Integers;
         end if;

      elsif Is_From_Hardcoded_Unit (E, Big_Reals) then
         if Chars (E)
            in Name_Op_Abs
             | Name_Op_Eq
             | Name_Op_Lt .. Name_Op_Subtract
             | Name_Op_Multiply .. Name_Op_Expon
           or else Get_Name_String (Chars (E))
                   in BRN.Big_Real
                    | BRN.Min
                    | BRN.Max
                    | BRN.Is_Valid
                    | BRN.From_String
                    | BRN.From_Universal_Image
                    | BRN.From_Quotient_String
         then
            return Big_Reals;
         end if;

      elsif Is_From_Hardcoded_Generic_Unit (E, Big_Integers) then
         if Get_Name_String (Chars (E))
            in BIN.Generic_To_Big_Integer | BIN.Generic_From_Big_Integer
         then
            return Big_Integers;
         end if;

      elsif Is_From_Hardcoded_Generic_Unit (E, Big_Reals) then
         if Get_Name_String (Chars (E)) in BRN.Generic_To_Big_Real then
            return Big_Reals;
         end if;

      elsif Is_From_Hardcoded_Unit (E, Cut_Operations) then
         if Get_Name_String (Chars (E)) in COpN.By | COpN.So then
            return Cut_Operations;
         end if;

      --  All subprograms in elementary functions are hardcoded

      elsif Is_From_Hardcoded_Generic_Unit (E, Elementary_Functions) then
         if Is_Subprogram (E) then
            return Elementary_Functions;
         end if;

      elsif Is_From_Hardcoded_Unit (E, System_Storage_Elements) then
         if Get_Name_String (Chars (E)) in SSEN.To_Address | SSEN.To_Integer
         then
            return System_Storage_Elements;
         end if;

      elsif Is_From_Hardcoded_Unit (E, Real_Time) then
         if Chars (E)
            in Name_Op_Abs
             | Name_Op_Add
             | Name_Op_Subtract
             | Name_Op_Multiply
             | Name_Op_Divide
             | Name_Op_Lt .. Name_Op_Ge
           or else Get_Name_String (Chars (E))
                   in RTN.Time
                    | RTN.Time_Span
                    | RTN.Time_First
                    | RTN.Time_Last
                    | RTN.Time_Span_First
                    | RTN.Time_Span_Last
                    | RTN.Time_Span_Zero
                    | RTN.Time_Span_Unit
                    | RTN.Nanoseconds
                    | RTN.Microseconds
                    | RTN.Milliseconds
                    | RTN.Seconds
                    | RTN.Minutes
                    | RTN.To_Duration
                    | RTN.To_Time_Span
                    | RTN.Time_Of
                    | RTN.Split
         then
            return Real_Time;
         end if;
      end if;

      return No_Unit;
   end Get_Hardcoded_Unit_Opt;

   -----------------------------
   -- Get_Real_Time_Time_Unit --
   -----------------------------

   function Get_Real_Time_Time_Unit (E : Entity_Id) return Ureal is
      Pack : constant E_Package_Id := Scope (E);
      Decl : Node_Id :=
        First (Visible_Declarations (Package_Specification (Pack)));
   begin
      while Present (Decl) loop
         if Nkind (Decl) = N_Number_Declaration
           and then Get_Name_String (Chars (Defining_Identifier (Decl)))
                    = Real_Time_Names.Time_Unit
         then
            return Realval (Expression (Decl));
         end if;
         Next (Decl);
      end loop;
      raise Program_Error;
   end Get_Real_Time_Time_Unit;

   --------------------------------
   -- Has_Imprecise_Precondition --
   --------------------------------

   function Has_Imprecise_Precondition (E : Entity_Id) return Boolean is
   begin
      case Get_Hardcoded_Unit (E) is
         when Big_Integers =>
            return
              Get_Name_String (Chars (E)) = Big_Integers_Names.From_String;

         when Big_Reals =>
            return
              Get_Name_String (Chars (E))
              in Big_Reals_Names.From_String
               | Big_Reals_Names.From_Quotient_String
               | Big_Reals_Names.From_Universal_Image;

         when others =>
            return False;
      end case;
   end Has_Imprecise_Precondition;

   -----------------------
   -- Has_Stoele_Offset --
   -----------------------

   function Has_Stoele_Offset (E : Type_Kind_Id) return Boolean is
      R : Type_Kind_Id := E;
      T : Type_Kind_Id;
   begin
      loop
         if Is_From_Hardcoded_Unit (R, System_Storage_Elements)
           and then Get_Name_String (Chars (R)) = "storage_offset"
         then
            return True;
         end if;
         T := Parent_Type (R);
         if T = R then
            return False;
         end if;
         R := T;
      end loop;
   end Has_Stoele_Offset;

   ------------------------------------
   -- Is_From_Hardcoded_Generic_Unit --
   ------------------------------------

   function Is_From_Hardcoded_Generic_Unit
     (E : Entity_Id; Unit : Hardcoded_Enum) return Boolean
   is
      Par : Node_Id := Parent (Scope (E));
   begin
      --  Special case for top level instances as child units

      if Nkind (Par) = N_Defining_Program_Unit_Name then
         Par := Parent (Par);
      end if;

      --  We need to check first if the scope of E is a package whose
      --  generic parent is defined in Unit.

      if Nkind (Par) not in N_Package_Specification
        or else No (Generic_Parent (Par))
        or else Nkind (Generic_Parent (Par)) not in N_Has_Chars
        or else (not Is_Hardcoded_Unit
                       (E => Generic_Parent (Par), Unit => Unit)
                 and then not Is_From_Hardcoded_Unit
                                (E => Generic_Parent (Par), Unit => Unit))
      then
         return False;
      end if;

      --  Then, we check the name of the generic parent

      case Unit is
         when Big_Integers =>
            return
              Get_Name_String (Chars (Generic_Parent (Par)))
              in "signed_conversions" | "unsigned_conversions";

         when Big_Reals =>
            return
              Get_Name_String (Chars (Generic_Parent (Par)))
              in "fixed_conversions" | "float_conversions";

         when Elementary_Functions =>
            return True;

         when others =>
            raise Program_Error;
      end case;
   end Is_From_Hardcoded_Generic_Unit;

   ----------------------------
   -- Is_From_Hardcoded_Unit --
   ----------------------------

   function Is_From_Hardcoded_Unit
     (E : Entity_Id; Unit : Hardcoded_Enum) return Boolean
   is (Is_Hardcoded_Unit (Scope (E), Unit));

   -------------------------
   -- Is_Hardcoded_Entity --
   -------------------------

   function Is_Hardcoded_Entity (E : Entity_Id) return Boolean
   is (Get_Hardcoded_Unit_Opt (E) /= No_Unit);

   -----------------------
   -- Is_Hardcoded_Unit --
   -----------------------

   function Is_Hardcoded_Unit
     (E : Entity_Id; Unit : Hardcoded_Enum) return Boolean
   is
      S_Ptr : Entity_Id := E;
      --  Scope pointer
   begin
      --  The following case statement is meant to be extended in the future

      case Unit is
         when Big_Integers | Big_Reals =>

            --  First check for the name of the big number unit

            if Unit = Big_Integers then
               if Get_Name_String (Chars (S_Ptr)) /= "big_integers" then
                  return False;
               end if;
            else
               pragma Assert (Unit = Big_Reals);
               if Get_Name_String (Chars (S_Ptr)) /= "big_reals" then
                  return False;
               end if;
            end if;

            --  Then check that we are in the Big_Numbers unit of the
            --  standard library or in the SPARK library.

            S_Ptr := Scope (S_Ptr);

            if Get_Name_String (Chars (S_Ptr)) = "big_numbers" then
               S_Ptr := Scope (S_Ptr);

               if Get_Name_String (Chars (S_Ptr)) /= "numerics" then
                  return False;
               end if;

               S_Ptr := Scope (S_Ptr);

               if Chars (S_Ptr) /= Name_Ada then
                  return False;
               end if;

            elsif Get_Name_String (Chars (S_Ptr)) /= "spark" then
               return False;
            end if;

            return Scope (S_Ptr) = Standard_Standard;

         when Cut_Operations =>
            if Get_Name_String (Chars (S_Ptr)) /= "cut_operations" then
               return False;
            end if;

            S_Ptr := Scope (S_Ptr);

            if Get_Name_String (Chars (S_Ptr)) /= "spark" then
               return False;
            end if;

            S_Ptr := Scope (S_Ptr);

            return S_Ptr = Standard_Standard;

         when Elementary_Functions =>
            if Get_Name_String (Chars (S_Ptr))
              /= "generic_elementary_functions"
            then
               return False;
            end if;

            S_Ptr := Scope (S_Ptr);

            if Get_Name_String (Chars (S_Ptr)) /= "numerics" then
               return False;
            end if;

            S_Ptr := Scope (S_Ptr);

            if Chars (S_Ptr) /= Name_Ada then
               return False;
            end if;

            return Scope (S_Ptr) = Standard_Standard;

         when Real_Time =>
            if Get_Name_String (Chars (S_Ptr)) /= "real_time" then
               return False;
            end if;

            S_Ptr := Scope (S_Ptr);

            if Chars (S_Ptr) /= Name_Ada then
               return False;
            end if;

            return Scope (S_Ptr) = Standard_Standard;

         when System =>
            if Get_Name_String (Chars (S_Ptr)) /= "system" then
               return False;
            end if;

            return Scope (S_Ptr) = Standard_Standard;

         when System_Storage_Elements =>
            if Get_Name_String (Chars (S_Ptr)) /= "storage_elements" then
               return False;
            end if;

            S_Ptr := Scope (S_Ptr);

            if Get_Name_String (Chars (S_Ptr)) /= "system" then
               return False;
            end if;

            return Scope (S_Ptr) = Standard_Standard;
      end case;

   end Is_Hardcoded_Unit;

   ------------------------------
   -- Is_Imprecisely_Hardcoded --
   ------------------------------

   function Is_Imprecisely_Hardcoded (E : Entity_Id) return Boolean is
   begin
      case Get_Hardcoded_Unit (E) is
         when Big_Integers =>
            return
              Get_Name_String (Chars (E)) = Big_Integers_Names.From_String;

         when Big_Reals =>
            return
              Get_Name_String (Chars (E))
              in Big_Reals_Names.From_String
               | Big_Reals_Names.From_Quotient_String
               | Big_Reals_Names.From_Universal_Image;

         when Elementary_Functions =>

            --  All elementary functions are imprecisely hardcoded for now

            return True;

         when others =>
            return False;
      end case;
   end Is_Imprecisely_Hardcoded;

   -------------------------
   -- Is_Literal_Function --
   -------------------------

   function Is_Literal_Function (E : Entity_Id) return Boolean is
      package BIN renames Big_Integers_Names;
      use BIN;
      package BRN renames Big_Reals_Names;
      use BRN;

   begin
      if Is_From_Hardcoded_Unit (E, Big_Integers) then
         return Get_Name_String (Chars (E)) = BIN.From_String;
      elsif Is_From_Hardcoded_Unit (E, Big_Reals) then
         return
           Get_Name_String (Chars (E))
           in BRN.From_String
            | BRN.From_Universal_Image
            | BRN.From_Quotient_String;
      else
         return False;
      end if;
   end Is_Literal_Function;

   -----------------------
   -- Is_System_Address --
   -----------------------

   function Is_System_Address (E : Type_Kind_Id) return Boolean is
      R : constant Type_Kind_Id := Retysp (E);
   begin
      return
        Is_From_Hardcoded_Unit (R, System)
        and then Get_Name_String (Chars (R)) = "address";
   end Is_System_Address;

end SPARK_Util.Hardcoded;
