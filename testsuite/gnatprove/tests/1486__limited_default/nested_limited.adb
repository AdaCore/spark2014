package body nested_limited with SPARK_Mode is
   function Fresh (A, B, C : Positive) return State is
     ((A => A, B => B, C => C, others => <>));
end nested_limited;
