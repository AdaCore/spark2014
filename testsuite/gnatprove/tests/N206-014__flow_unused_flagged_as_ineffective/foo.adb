package body Foo
is

   procedure Test_01_E (X : in out String)
   is
   begin
      X := (others => 'x');
   end Test_01_E;

   procedure Test_02_Ok (X : out String)
   is
   begin
      X := (others => 'x');
   end Test_02_Ok;

end Foo;
