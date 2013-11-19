package body Parent_14.Public_Child_A_14
  with SPARK_Mode
is
   function G (X : Integer) return Integer is
     (if X <= 0 then 0
      else Parent_14.F (X));  -- OK
end Parent_14.Public_Child_A_14;
