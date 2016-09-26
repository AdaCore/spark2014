package body Nested is

   package P1 with Abstract_State => S1, Initializes => S1 is
      procedure Fiddle with Global => (In_Out => S1);
   end P1;

   package body P1 with Refined_State => (S1 => G) is
      G : Boolean := False;
      procedure Fiddle with Refined_Global => (In_Out => G) is
      begin
         G := not G;
      end Fiddle;
   end P1;

   procedure Test_01 with Global => P1.S1 is  --  should be in_out
   begin
      P1.Fiddle;
   end Test_01;

   procedure Test_02 with Global => null is
      package P2 with Abstract_State => S2 is
         procedure Fiddle;
      end P2;

      package body P2 with Refined_State => (S2 => G) is
         G : Boolean := False;
         procedure Fiddle is
         begin
            G := not G;
         end Fiddle;
      end P2;

      procedure Foo with Global => P2.S2 is  --  should be in_out
      begin
         P2.Fiddle;
      end Foo;
   begin
      Foo;
   end Test_02;

end Nested;
