package Full
   with SPARK_Mode
is

   Z : Integer;

   function Id (X : Integer) return Integer;

   function Bump (X : Integer) return Integer
      with Pre => X < Integer'Last,
           Post => Bump'Result = X + 1;

   procedure Use_Bump
      with Global => (In_Out => Z),
           Pre    => Z = 0,
           Post   => Id(Z) > 0;
end Full;
