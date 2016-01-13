procedure AConv
with
   SPARK_Mode
is
   type M64_Type is mod 2**64;
   type M32_Type is mod 2**32;
   type Byte is mod 2**8;

   type A_Type is array (M64_Type range 1000 .. 1999) of Byte;
   type B_Type is array (M32_Type range    0 ..  999) of Byte;

   procedure Foo (B : in out B_Type)
   with Pre => True
   is
   begin
      for I in B'Range loop
         B (I) := B (I) + 1;
      end loop;
   end Foo;

   A : A_Type := (others => 42);

begin
   Foo (B_Type (A));
end AConv;
