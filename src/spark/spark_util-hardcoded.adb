------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   S P A R K _ U T I L - H A R D C O D E D                --
--                                                                          --
--                                  B o d y                                 --
--                                                                          --
--                     Copyright (C) 2020-2020, AdaCore                     --
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
   begin

      --  We need to check first if the scope of E is a package whose
      --  generic parent is defined in Unit.

      if Nkind (Parent (Scope (E))) not in N_Package_Specification
           or else
         No (Generic_Parent (Parent (Scope (E))))
           or else
         Nkind (Generic_Parent (Parent (Scope (E)))) not in N_Has_Chars
           or else
         not Is_From_Hardcoded_Unit
               (E    => Generic_Parent (Parent (Scope (E))),
                Unit => Unit)
      then
         return False;
      end if;

      --  Then, we check the name of the generic parent

      case Unit is
         when Big_Integers =>
            return Get_Name_String
                     (Chars
                        (Generic_Parent
                           (Parent
                              (Scope (E))))) in "signed_conversions"
                                              | "unsigned_conversions";
         when Big_Reals =>
            return Get_Name_String
                     (Chars
                        (Generic_Parent
                           (Parent
                              (Scope (E))))) in "fixed_conversions"
                                              | "float_conversions";
      end case;
   end Is_From_Hardcoded_Generic_Unit;

   ----------------------------
   -- Is_From_Hardcoded_Unit --
   ----------------------------

   function Is_From_Hardcoded_Unit
     (E    : Entity_Id;
      Unit : Hardcoded_Enum)
      return Boolean
   is
      S_Ptr : Entity_Id := Scope (E);
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
            --  standard library.

            S_Ptr := Scope (S_Ptr);

            if Get_Name_String (Chars (S_Ptr)) /= "big_numbers" then
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
      end case;

   end Is_From_Hardcoded_Unit;

   -------------------------
   -- Is_Hardcoded_Entity --
   -------------------------

   function Is_Hardcoded_Entity (E : Entity_Id) return Boolean is
      package BIN renames Big_Integers_Names; use BIN;
      package BRN renames Big_Reals_Names; use BRN;
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
                                             | BIN.Gcd;
      elsif Is_From_Hardcoded_Unit (E, Big_Reals) then
         return Chars (E) in Name_Op_Abs
                           | Name_Op_Eq
                           | Name_Op_Lt .. Name_Op_Subtract
                           | Name_Op_Multiply .. Name_Op_Expon
                  or else
                Get_Name_String (Chars (E)) in BRN.Big_Real
                                             | BRN.Min
                                             | BRN.Max
                                             | BRN.Is_Valid;

      elsif Is_From_Hardcoded_Generic_Unit (E, Big_Integers) then
         return Get_Name_String (Chars (E)) in BIN.Generic_To_Big_Integer
                                             | BIN.Generic_From_Big_Integer;

      elsif Is_From_Hardcoded_Generic_Unit (E, Big_Reals) then
         return Get_Name_String (Chars (E)) in BRN.Generic_To_Big_Real;
      end if;

      return False;
   end Is_Hardcoded_Entity;

end SPARK_Util.Hardcoded;
