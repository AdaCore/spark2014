package My_Pack
   with SPARK_Mode
is

   Z : Integer;

   function Id (X : Integer) return Integer;

   procedure Bump (X : in out Integer)
      with Pre => X < Integer'Last,
           Post => X = Id(X'Old) + 1;

   procedure Use_Bump
      with Global => (In_Out => Z),
           Pre    => Z = 0,
           Post   => Z = Id(Z'Old) + 1;
end My_Pack;
