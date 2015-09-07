package body Unused_Parameter with SPARK_Mode => On is

   procedure Avg (A : in  Natural;
                  B : in  Natural;
                  C : out Natural) is
   begin
      C := (A + A) / 2;
   end Avg;

end Unused_Parameter;
