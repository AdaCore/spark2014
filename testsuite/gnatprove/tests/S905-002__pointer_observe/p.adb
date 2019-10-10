package body P with SPARK_Mode is

   function With_Side_Effect (X : List_Acc) return access constant List
   is
      C : access constant List := X;
   begin
      C.N.V := 3;
      return C;
   end With_Side_Effect;

end P;
