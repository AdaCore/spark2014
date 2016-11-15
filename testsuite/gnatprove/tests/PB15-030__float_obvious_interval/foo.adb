package body Foo is

   type    FT is digits 15 range -1234567890.0 .. 1234567890.0;
   subtype IT is Integer   range -1234567890   .. 1234567890;

   procedure Test_01 (A : FT;
                      B : out IT)
   with Global => null
   is
   begin
      B := IT (A);
   end Test_01;

end Foo;
