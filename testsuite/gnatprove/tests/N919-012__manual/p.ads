package P
   with SPARK_Mode
is

   X : Integer;

   procedure Q (Z : Integer)
      with Global => (Output => X),
           Pre    => Z < Integer'Last,
           Post   => (X = Z and
                      X = Z + 1);
end P;
