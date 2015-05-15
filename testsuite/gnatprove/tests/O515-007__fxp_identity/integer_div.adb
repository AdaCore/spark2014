procedure Integer_Div is

   --  identity function

   function ID (TS : Integer) return Integer is (TS);

   --  the division will never overflow because right is positive

   function Foo (Right : Integer) return Boolean with
     Pre => Right > 0
   is
   begin
      return ID (Integer'First) / Right <= 0;
   end Foo;

begin
   null;
end Integer_Div;
