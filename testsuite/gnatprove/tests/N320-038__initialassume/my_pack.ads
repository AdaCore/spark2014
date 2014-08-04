package My_Pack
   with SPARK_Mode
is

   Z : Integer;

   procedure Bump (X : in out Integer)
      with Pre => X < Integer'Last,
           Post => X = X'Old + 1;

   procedure Use_Bump
      with Global => (In_Out => Z),
           Pre    => Z = 0,
           Post   => Z > 0;
end My_Pack;
