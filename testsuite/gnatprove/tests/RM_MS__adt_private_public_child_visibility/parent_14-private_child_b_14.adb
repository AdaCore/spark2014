package body Parent_14.Private_Child_B_14
  with SPARK_Mode
is
   function H (X : Integer) return Integer is
     (if X <= 10 then 10
      else Parent_14.F (X));  -- Legal in SPARK 2014
end Parent_14.Private_Child_B_14;
