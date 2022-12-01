package body String_Problem
with Spark_Mode
is
   procedure String_Equal
     (A : String)
   is
      X1 : Integer;
      X2 : Integer;
   begin
      X1 := Integer'Value (A);
      pragma Annotate
        (Gnatprove, False_Positive, "precondition might fail", "we only call on valid integer strings");
      X2 := Integer'Value (A);
      pragma Annotate
        (Gnatprove, False_Positive, "precondition might fail", "we only call on valid integer strings");
      pragma Assert (X1 = X2);
   end String_Equal;
end String_Problem;
