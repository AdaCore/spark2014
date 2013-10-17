package body Refined_Post_Illegal_3
  with SPARK_Mode
is
   procedure P1 (Par : out Integer)
     with Refined_Post => Par = 2
   is
   begin
      Par := 10;
   end P1;


   procedure P2 (Par : out Integer) is
   begin
      Par := 10;
   end P2;
end Refined_Post_Illegal_3;
