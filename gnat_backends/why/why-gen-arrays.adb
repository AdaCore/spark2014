------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - A R R A Y S                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
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

with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Gen.Decl;       use Why.Gen.Decl;
with Why.Gen.Ints;       use Why.Gen.Ints;
with Why.Gen.Names;      use Why.Gen.Names;
with Why.Gen.Axioms;     use Why.Gen.Axioms;

package body Why.Gen.Arrays is

   -----------------------------------
   -- Declare_Ada_Constrained_Array --
   -----------------------------------

   procedure Declare_Ada_Constrained_Array
     (File      : W_File_Id;
      Name      : String;
      Int_Name  : String;
      Component : String;
      Low       : Uint;
      High      : Uint) is
   begin
      Declare_Ada_Abstract_Signed_Int
        (File,
         Int_Name,
         Low,
         High);

      New_Abstract_Type (File, Name);

      New_Logic
        (File => File,
         Name => Array_Access_Name (Name),
         Args =>
            (1 => New_Abstract_Type (Name => New_Identifier (Int_Name)),
             2 => New_Abstract_Type (Name => New_Identifier (Name))),
         Return_Type =>
            New_Abstract_Type (Name => New_Identifier (Component)));

      New_Logic
        (File => File,
         Name => Array_Update_Name (Name),
         Args =>
            (1 => New_Abstract_Type (Name => New_Identifier (Int_Name)),
             2 => New_Abstract_Type (Name => New_Identifier (Name)),
             3 => New_Abstract_Type (Name => New_Identifier (Component))),
         Return_Type => New_Abstract_Type (Name => New_Identifier (Name)));

      Define_Array_Eq_Axiom
         (File => File,
          Type_Name => Name,
          Index_Type => New_Abstract_Type (Name => New_Identifier (Int_Name)),
          Component_Type =>
            New_Abstract_Type (Name => New_Identifier (Component)));
   end Declare_Ada_Constrained_Array;

   ---------------------------
   -- New_Array_Access_Prog --
   ---------------------------

   function New_Array_Access_Prog
     (Type_Name : String;
      Ar : W_Prog_Id;
      Index : W_Prog_Id) return W_Prog_Id is
   begin
      return
        New_Prog_Call
          (Name => Array_Access_Name (Type_Name),
           Progs => (1 => Index, 2 => Ar));
   end New_Array_Access_Prog;

   ---------------------------
   -- New_Array_Access_Term --
   ---------------------------

   function New_Array_Access_Term
     (Type_Name : String;
      Ar : W_Term_Id;
      Index : W_Term_Id) return W_Term_Id is
   begin
      return
        New_Operation
          (Name => Array_Access_Name (Type_Name),
           Parameters => (1 => Index, 2 => Ar));
   end New_Array_Access_Term;

   ---------------------------
   -- New_Array_Update_Prog --
   ---------------------------

   function New_Array_Update_Prog
      (Type_Name : String;
       Ar        : W_Identifier_Id;
       Index     : W_Prog_Id;
       Value     : W_Prog_Id) return W_Prog_Id
   is
   begin
      return
         New_Assignment
           (Name => Duplicate_Identifier (Id => Ar),
            Value =>
               New_Prog_Call
                 (Name => Array_Update_Name (Type_Name),
                  Progs =>
                   (1 => Index,
                    2 => New_Deref (Ref => Ar),
                    3 => Value)));
   end New_Array_Update_Prog;

   ---------------------------
   -- New_Array_Update_Term --
   ---------------------------

   function New_Array_Update_Term
      (Type_Name : String;
       Ar        : W_Term_Id;
       Index     : W_Term_Id;
       Value     : W_Term_Id) return W_Term_Id
   is
   begin
      return
        New_Operation
          (Name => Array_Update_Name (Type_Name),
           Parameters => (1 => Index, 2 => Ar, 3 => Value));
   end New_Array_Update_Term;

end Why.Gen.Arrays;
