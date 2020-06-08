package body Example with SPARK_Mode
is
   pragma Warnings (Off, "* has no effect");

   -- This test is for checking external printer/parser. Transformations are
   -- registered in the session that use the external printing/parsing. If
   -- this is broken, this test should break too

   -- Printing/parsing checked by this file:
   -- - for all i in a .. b => d
   -- - record support: A.B.C
   -- - arrays support: M(C)
   -- - attributes support: A'First, A'Last

   ---------------------
   --  Standard types --
   ---------------------

   type Unsigned_Byte is range 0 .. 255;

   -- Check for the parser on "for all ...."
   procedure Mult_Range (A, B : in out Unsigned_Byte) with
     Pre  => A < B,
     Post => B * A = A'Old
   is
   begin
      B := A + B;
      A := B / A;
      B := A - B;
      A := B * A;
   end Mult_Range;

   type Char_Map2 is array (Character range <>) of Character;

   -- Check parser for usage of arrays "M (C)" and M'Last
   function Is_Id (M : in Char_Map2;
                     C : in Character)
                    return Boolean
     with Post => Is_Id'Result = (M (C) = C)
   is
   begin
      return M (C) = 'a';
   end Is_Id;

   type Var_Rec (I : Integer := 0) is
      record
         case I is
            when 0 =>
               A0 : Unsigned_Byte;
               B0 : Unsigned_Byte;
            when 1 =>
               A1 : Unsigned_Byte;
            when others =>
               null;
         end case;
      end record;

   --  Check parser for usage of "A.B.C.D.E" for records
   procedure Disc_Rec (A, B : in out Var_Rec) with
     Pre =>  B.I = 0 and A.I = 0,
     Post => (if A.I = 0 then
                B.I = 1 and B.A1 = 42
              else
                A.A0 = B.A1)
   is
   begin
      A := (I => 0, A0 => 5, B0 => 50);
      B := (I => 1, A1 => 55);
   end Disc_Rec;

   pragma Warnings (On, "* has no effect");
end Example;
