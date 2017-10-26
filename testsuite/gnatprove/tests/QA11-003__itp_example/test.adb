package body Test
is
   type Unsigned_Byte is range 0..255;
   type Byte is range -128..127;

   function Test_1 (A: Unsigned_Byte) return Unsigned_Byte
     with
       Pre => A > 0,
       Post => (for some X in Unsigned_Byte'Range =>
                  A = X + X or else A = X + X + 1)
   is
   begin
      return A;
   end Test_1;

   function Test_2 (A : String) return Character
   with Post => Test_2'Result = 'a'
   is
   begin
      return A (1);
   end Test_2;

   type W is record
      F : Integer;
      G : Integer;
   end record;

   function Test_3 (A : W) return Integer
   with Post => Test_3'Result = 2
   is
   begin
      return A.F;
   end Test_3;

   function Test_4 (A : Integer) return Integer
   with Post => Test_4'Result = 5
   is
      B : Integer := A;
   begin
      B := B + 1;
      return B;
   end Test_4;

   type N is mod 256;

   function Test_5 (A : N) return N
   with Post => Test_5'Result = 5
   is
      B : N := A;
   begin
      B := B + 1;
      return B;
   end Test_5;

   function Test_6 (A : Float) return Float
   with Post => Test_6'Result = 0.1
   is
      B : Float := A;
   begin
      B := B + 1.1;
      return B;
   end Test_6;


   type  M is array (Integer range 0 .. 10,
                     Integer range 2 .. 3) of Integer;

   function Test_7 (Mat : M) return Integer
   with Post => Test_7'Result = 1
   is
   begin
      return Mat(1,2);
   end Test_7;

   --  forall x, (x ^ 3 - x) mod 3 = 0
   procedure Little_Fermat3 (X: Long_Integer)
     with Ghost,
     -- We want it to work on any 32 bits machine not only on 64 bits. That's
     -- why we use 2**10.
       Pre => 0 <= X and X <= 2**10,
       Post => (X ** 3 - X) mod 3 = 0
   is
   begin
      null;
   end Little_Fermat3;



end Test;
