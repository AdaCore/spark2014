package body Glob with SPARK_Mode is

   V : constant T := (A => True);

   function F (X : T) return Boolean is (X = V);
end;
