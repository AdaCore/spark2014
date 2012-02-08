------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - N A M E S                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2012, AdaCore                   --
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
with Atree;  use Atree;
with Einfo;  use Einfo;
with Lib;    use Lib;
with Sinput; use Sinput;

with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Conversions;     use Why.Conversions;
with Why.Inter;           use Why.Inter;

package body Why.Gen.Names is

   function Bool_Cmp_String
     (Rel       : EW_Relation;
      Arg_Types : W_Base_Type_Id) return String;
   --  Return the name of a boolean integer comparison operator

   ---------------------
   -- Bool_Cmp_String --
   ---------------------

   function Bool_Cmp_String
     (Rel       : EW_Relation;
      Arg_Types : W_Base_Type_Id) return String
   is
      Kind : constant EW_Type := Get_Base_Type (Arg_Types);
      Name : constant String :=
               (if Kind = EW_Abstract then
                  Full_Name (Get_Ada_Node (+Arg_Types))
                else
                  EW_Base_Type_Name (Kind));
   begin
      pragma Assert
        (Kind /= EW_Abstract or else Rel = EW_Eq or else Rel = EW_Ne);

      case Rel is
         when EW_None =>
            pragma Assert (False);
            return "always_true_" & Name & "_bool";
         when EW_Eq =>
            return "bool_" & Name & "__eq";
         when EW_Ne =>
            return "bool_" & Name & "__ne";
         when EW_Lt =>
            return "bool_" & Name & "__lt";
         when EW_Le =>
            return "bool_" & Name & "__le";
         when EW_Gt =>
            return "bool_" & Name & "__gt";
         when EW_Ge =>
            return "bool_" & Name & "__ge";
      end case;
   end Bool_Cmp_String;

   ---------------------
   -- Conversion_Name --
   ---------------------

   function Conversion_Name
      (From : W_Base_Type_Id;
       To   : W_Base_Type_Id) return W_Identifier_Id
   is
      From_Kind : constant EW_Type := Get_Base_Type (From);
      To_Kind   : constant EW_Type := Get_Base_Type (To);
   begin
      case From_Kind is
         when EW_Unit | EW_Prop =>
            raise Not_Implemented;

         when EW_Scalar =>
            case To_Kind is
               when EW_Unit | EW_Prop | EW_Array =>
                  raise Not_Implemented;

               when EW_Scalar =>

                  --  Only certain conversions are OK

                  if From_Kind = EW_Int and then To_Kind = EW_Real then
                     return Real_Of_Int.Id;
                  elsif From_Kind = EW_Bool and then To_Kind = EW_Int then
                     return Int_Of_Bool.Id;
                  elsif From_Kind = EW_Int and then To_Kind = EW_Bool then
                     return Bool_Of_Int.Id;

                  --  Either the two objects are of the same type
                  --  (in which case the conversion is useless) or
                  --  they are of incompatible types
                  --  In both cases, it is an error.

                  else
                     raise Program_Error;
                  end if;

               when EW_Abstract =>
                  declare
                     A : constant Node_Id := Get_Ada_Node (+To);
                  begin
                     return
                       Conversion_From.Id (Ada_Node => A,
                                           L_Name   => Full_Name (A),
                                           R_Name   =>
                                             Why_Scalar_Type_Name (From_Kind));
                  end;
            end case;

         when EW_Array =>
            pragma Assert (To_Kind = EW_Abstract);
            declare
               A : constant Node_Id := Get_Ada_Node (+To);
            begin
               return
                 Conversion_From.Id
                   (Ada_Node => A,
                    L_Name   => Full_Name (A),
                    R_Name   =>
                      New_Ada_Array_Name
                        (Number_Dimensions (Underlying_Type (A))));
            end;

         when EW_Abstract =>
            case To_Kind is
               when EW_Unit | EW_Prop =>
                  raise Not_Implemented;

               when EW_Scalar =>
                  declare
                     A : constant Node_Id := Get_Ada_Node (+From);
                  begin
                     return
                       Conversion_To.Id (Ada_Node => A,
                                         L_Name   => Full_Name (A),
                                         R_Name   =>
                                           Why_Scalar_Type_Name (To_Kind));
                  end;
               when EW_Array =>
                  declare
                     A : constant Node_Id := Get_Ada_Node (+From);
                  begin
                     return
                       Conversion_To.Id
                         (Ada_Node => A,
                          L_Name   => Full_Name (A),
                          R_Name   =>
                            New_Ada_Array_Name
                              (Number_Dimensions (Underlying_Type (A))));
                  end;

               when EW_Abstract =>
                  raise Program_Error
                     with "Conversion between arbitrary types attempted";
            end case;
      end case;
   end Conversion_Name;

   -----------------------
   -- EW_Base_Type_Name --
   -----------------------

   function EW_Base_Type_Name (Kind : EW_Basic_Type) return String is
   begin
      case Kind is
         when EW_Unit =>
            return "unit";
         when EW_Prop =>
            return "prop";
         when EW_Real =>
            return "real";
         when EW_Int =>
            return "int";
         when EW_Bool =>
            return "bool";
      end case;
   end EW_Base_Type_Name;

   -------------
   -- New_Abs --
   -------------

   function New_Abs (Kind : EW_Numeric) return W_Identifier_Id is
   begin
      case Kind is
         when EW_Real =>
            return New_Real_Abs.Id;
         when EW_Int =>
            return New_Integer_Abs.Id;
      end case;
   end New_Abs;

   ------------------
   -- New_Bool_Cmp --
   ------------------

   function New_Bool_Cmp
     (Rel       : EW_Relation;
      Arg_Types : W_Base_Type_Id) return W_Identifier_Id
   is
      Kind : constant EW_Type := Get_Base_Type (Arg_Types);
      A    : constant Node_Id :=
        (if Kind = EW_Abstract then Get_Ada_Node (+Arg_Types)
         else Empty);
   begin
      return New_Identifier (Ada_Node => A,
                             Domain   => EW_Pred,
                             Name     => Bool_Cmp_String (Rel, Arg_Types));
   end New_Bool_Cmp;

   ------------------
   -- New_Division --
   ------------------

   function New_Division (Kind : EW_Numeric) return W_Identifier_Id is
   begin
      case Kind is
         when EW_Real =>
            return New_Real_Division.Id;
         when EW_Int =>
            return New_Integer_Division.Id;
      end case;
   end New_Division;

   --------------------
   -- New_Identifier --
   --------------------

   function New_Identifier (Ada_Node : Node_Id := Empty; Name : String)
                            return W_Identifier_Id is
   begin
      return New_Identifier (Ada_Node, EW_Term, Name);
   end New_Identifier;

   function New_Identifier
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : String)
     return W_Identifier_Id is
   begin
      return New_Identifier (Ada_Node => Ada_Node,
                             Domain => Domain,
                             Symbol => NID (Name));
   end New_Identifier;

   ---------
   -- NID --
   ---------

   function NID (Name : String) return Name_Id is
   begin
      Name_Len := 0;
      Add_Str_To_Name_Buffer (Name);
      return Name_Find;
   end NID;

   --------------
   -- New_Prog --
   --------------

   function New_Prog (Name : String) return W_Prog_Id is
   begin
      return +New_Identifier (Domain => EW_Prog,
                              Name   => Name);
   end New_Prog;

   -------------------------
   -- New_Temp_Identifier --
   -------------------------

   New_Temp_Identifier_Counter : Natural := 0;

   function New_Temp_Identifier return W_Identifier_Id is
      Counter_Img : constant String :=
                      Natural'Image (New_Temp_Identifier_Counter);
   begin
      New_Temp_Identifier_Counter := New_Temp_Identifier_Counter + 1;
      return New_Identifier
        (Name => "_temp_" & To_String (New_Temp_Identifier_Suffix) & "_"
         & Counter_Img (Counter_Img'First + 1 .. Counter_Img'Last));
   end New_Temp_Identifier;

   function New_Temp_Identifier (N : Node_Id) return String is
      Loc    : constant Source_Ptr := Sloc (N);
      File   : constant String := Full_Name (Main_Unit_Entity);
      Line   : constant Physical_Line_Number := Get_Physical_Line_Number (Loc);
      Column : constant Column_Number := Get_Column_Number (Loc);
   begin
      return File & "__" & Int_Image (Integer (Line)) & "__" &
        Int_Image (Integer (Column));
   end New_Temp_Identifier;

   function New_Temp_Identifier (N : Node_Id) return W_Identifier_Id is
   begin
      return New_Identifier (Name => New_Temp_Identifier (N));
   end New_Temp_Identifier;

   --------------
   -- New_Term --
   --------------

   function New_Term (Name : String) return W_Term_Id is
   begin
      return +New_Identifier (Name => Name);
   end New_Term;

   ----------------------
   -- To_Program_Space --
   ----------------------

   function To_Program_Space (Name : W_Identifier_Id) return W_Identifier_Id is
      Suffix : constant String := "_";
      N_Id   : constant Name_Id := Get_Symbol (Name);
      Img    : constant String := Get_Name_String (N_Id);
   begin
      return New_Identifier (Get_Ada_Node (+Name), EW_Prog, Img & Suffix);
   end To_Program_Space;

   --------------------------
   -- Why_Scalar_Type_Name --
   --------------------------

   function Why_Scalar_Type_Name (Kind : EW_Scalar) return String is
   begin
      case Kind is
         when EW_Bool =>
            return "bool";
         when EW_Int =>
            return "int";
         when EW_Real =>
            return "real";
      end case;
   end Why_Scalar_Type_Name;

end Why.Gen.Names;
