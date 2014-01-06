procedure Foo with SPARK_Mode => On
is
   pragma Warnings (Off, "unused initial value*");
   pragma Warnings (Off, "statement has no effect");
   procedure P (A, B, C : Long_Float)
   with Pre => ((A + B) + C <= Long_Float'Last)
   is
   begin
      null;
   end P;
begin
   P (Long_Float'Last, Long_Float'Last, Long_Float'First);
end Foo;
