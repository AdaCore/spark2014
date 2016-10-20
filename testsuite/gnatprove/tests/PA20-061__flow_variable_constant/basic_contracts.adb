package body Basic_Contracts is

   function Average (Numerator : Natural;
                     Denominator : Positive) return Float
   is
      Num : constant Float := Float (Numerator);
      Den : constant Float := Float'Succ (0.0);
      pragma Assert (Den > 1.0);
   begin
      return Num / Den;
   end Average;

end Basic_Contracts;
