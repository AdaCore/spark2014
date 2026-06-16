procedure Main with SPARK_Mode is

   --  Test that the dynamic property of the array is provable after a conversion

   type A is array (Positive range <>) of Integer;

   function F (X : A) return Integer with
     Global => null,
     Import,
     Post => F'Result > 42;

   subtype Int2 is Integer;
   type A2 is array (Positive range <>) of Int2;

   procedure P (X : A2)
   is
   begin
      pragma Assert (F (A (X)) > 42); -- @ASSERT:PASS
   end P;

   --  Same with the implicit conversion for Relaxed_Init

   procedure P (X : A) with
     Relaxed_Initialization => X,
     Pre => X'Initialized
   is
   begin
      pragma Assert (F (X) > 42); -- @ASSERT:PASS
   end P;

begin
   null;
end Main;
