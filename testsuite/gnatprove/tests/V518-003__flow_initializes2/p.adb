package body P with
  SPARK_Mode => On
is
   package body Q with
     SPARK_Mode => Off,
     Refined_State => (S1 => X1, S2 => X2)
   is
      X1, X2 : Boolean := True;
      function Valid return Boolean is
      begin
         return X1 and X2;
      end;
   end;
end P;
