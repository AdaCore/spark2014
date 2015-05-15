procedure Duration_Div is

   --  identity function

   function ID (TS : Duration) return Duration is (TS);

   --  the division will never overflow because right is positive

   function Foo (Right : Integer) return Boolean with
     Pre => Right > 0
   is
   begin
      return ID (Duration'First) / Right <= Duration (0.0);
   end Foo;

begin
   null;
end Duration_Div;
