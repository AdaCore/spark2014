package body Nested is

   function Search return Integer is
      X : Integer := 0;
   begin

      Outer:
      for I in 1 .. 10 loop
         pragma Loop_Invariant (X = (I - 1) * 10);
         X := 0;
         for J in 1 ..10 loop
            pragma Loop_Invariant (X = I * (J - 1));
            X := I * J;
            exit Outer when X >= 45;
         end loop;
      end loop Outer;
      return X;

   end Search;

end Nested;
