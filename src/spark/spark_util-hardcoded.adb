------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   S P A R K _ U T I L - H A R D C O D E D                --
--                                                                          --
--                                  B o d y                                 --
--                                                                          --
--                     Copyright (C) 2020-2022, AdaCore                     --
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

with Stand; use Stand;

package body SPARK_Util.Hardcoded is

   function Is_Hardcoded_Unit
     (E    : Entity_Id;
      Unit : Hardcoded_Enum)
      return Boolean;
   --  Return True if E is the package for the hardcoded unit Unit

   -------------------------
   --  Get_Hardcoded_Unit --
   -------------------------

   function Get_Hardcoded_Unit (E : Entity_Id) return Hardcoded_Enum is
   begin

      for Unit in Hardcoded_Enum'Range loop

         if Is_From_Hardcoded_Unit (E, Unit)
           or else Is_From_Hardcoded_Generic_Unit (E, Unit)
         then
            return Unit;
         end if;

      end loop;

      raise Program_Error;
   end Get_Hardcoded_Unit;

   ------------------------------------
   -- Is_From_Hardcoded_Generic_Unit --
   ------------------------------------

   function Is_From_Hardcoded_Generic_Unit
     (E    : Entity_Id;
      Unit : Hardcoded_Enum)
      return Boolean
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
        or else
          (not Is_Hardcoded_Unit
               (E    => Generic_Parent (Par),
                Unit => Unit)
           and then
             not Is_From_Hardcoded_Unit
               (E    => Generic_Parent (Par),
                Unit => Unit))
      then
         return False;
      end if;

      --  Then, we check the name of the generic parent

      case Unit is
         when Big_Integers =>
            return Get_Name_String
                     (Chars
                        (Generic_Parent
                           (Par))) in "signed_conversions"
                                    | "unsigned_conversions";
         when Big_Reals =>
            return Get_Name_String
                     (Chars
                        (Generic_Parent
                           (Par))) in "fixed_conversions"
                                    | "float_conversions";
         when Cut_Operations =>
            return False;

         when Elementary_Functions =>
            return True;

         when System_Storage_Elements =>
            return False;
      end case;
   end Is_From_Hardcoded_Generic_Unit;

   ----------------------------
   -- Is_From_Hardcoded_Unit --
   ----------------------------

   function Is_From_Hardcoded_Unit
     (E    : Entity_Id;
      Unit : Hardcoded_Enum)
      return Boolean
   is (Is_Hardcoded_Unit (Scope (E), Unit));

   -------------------------
   -- Is_Hardcoded_Entity --
   -------------------------

   function Is_Hardcoded_Entity (E : Entity_Id) return Boolean is
      package BIN renames Big_Integers_Names; use BIN;
      package BRN renames Big_Reals_Names; use BRN;
      package COpN renames Cut_Operations_Names; use COpN;
      package SSEN renames System_Storage_Elements_Names;
   begin

      if Is_From_Hardcoded_Unit (E, Big_Integers) then
         return Chars (E) in Name_Op_Abs
                           | Name_Op_Mod
                           | Name_Op_Rem
                           | Name_Op_Eq
                           | Name_Op_Lt .. Name_Op_Subtract
                           | Name_Op_Multiply .. Name_Op_Expon
                  or else
                Get_Name_String (Chars (E)) in BIN.Big_Integer
                                             | BIN.Min
                                             | BIN.Max
                                             | BIN.To_Big_Integer
                                             | BIN.Is_Valid
                                             | BIN.To_Integer
                                             | BIN.Gcd
                                             | BIN.From_String;
      elsif Is_From_Hardcoded_Unit (E, Big_Reals) then
         return Chars (E) in Name_Op_Abs
                           | Name_Op_Eq
                           | Name_Op_Lt .. Name_Op_Subtract
                           | Name_Op_Multiply .. Name_Op_Expon
                  or else
                Get_Name_String (Chars (E)) in BRN.Big_Real
                                             | BRN.Min
                                             | BRN.Max
                                             | BRN.Is_Valid
                                             | BRN.From_String
                                             | BRN.From_Universal_Image;

      elsif Is_From_Hardcoded_Generic_Unit (E, Big_Integers) then
         return Get_Name_String (Chars (E)) in BIN.Generic_To_Big_Integer
                                             | BIN.Generic_From_Big_Integer;

      elsif Is_From_Hardcoded_Generic_Unit (E, Big_Reals) then
         return Get_Name_String (Chars (E)) in BRN.Generic_To_Big_Real;

      elsif Is_From_Hardcoded_Unit (E, Cut_Operations) then
         return Get_Name_String (Chars (E)) in COpN.By | COpN.So;

      --  All subprograms in elementary functions are hardcoded

      elsif Is_From_Hardcoded_Generic_Unit (E, Elementary_Functions) then
         return Is_Subprogram (E);

      elsif Is_From_Hardcoded_Unit (E, System_Storage_Elements) then
         return Get_Name_String (Chars (E)) in SSEN.To_Address
                                             | SSEN.To_Integer
                                             | SSEN.Add
                                             | SSEN.Subtract
                                             | SSEN.Modulus;
      end if;

      return False;
   end Is_Hardcoded_Entity;

   -----------------------
   -- Is_Hardcoded_Unit --
   -----------------------

   function Is_Hardcoded_Unit
     (E    : Entity_Id;
      Unit : Hardcoded_Enum)
      return Boolean
   is
      S_Ptr : Entity_Id := E;
      --  Scope pointer
   begin

      --  The following case statement is meant to be extended in the future

      case Unit is
         when Big_Integers | Big_Reals =>

            --  First check for the name of the big number unit, which
            --  might be either Big_Integers for the Ada standard unit, or
            --  Big_Integers_Ghost as a replacement of the standard unit for
            --  use in the runtime (as it is ghost, cannot be executed, and
            --  does not depend on System and Ada.Finalization).

            if Unit = Big_Integers then
               if Get_Name_String (Chars (S_Ptr)) not in "big_integers"
                                                       | "big_integers_ghost"
               then
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

            --  The special runtime unit System.SPARK.Cut_Operations duplicates
            --  the operations of SPARK.Cut_Operations for use inside the
            --  runtime.
            if Get_Name_String (Chars (S_Ptr)) = "system"
              and then Scope (S_Ptr) = Standard_Standard
            then
               return True;
            end if;

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

   -------------------------
   -- Is_Literal_Function --
   -------------------------

   function Is_Literal_Function (E : Entity_Id) return Boolean is
      package BIN renames Big_Integers_Names; use BIN;
      package BRN renames Big_Reals_Names; use BRN;

   begin
      if Is_From_Hardcoded_Unit (E, Big_Integers) then
         return Get_Name_String (Chars (E)) = BIN.From_String;
      elsif Is_From_Hardcoded_Unit (E, Big_Reals) then
         return Get_Name_String (Chars (E)) in BRN.From_String
                                             | BRN.From_Universal_Image;
      else
         return False;
      end if;
   end Is_Literal_Function;

end SPARK_Util.Hardcoded;
