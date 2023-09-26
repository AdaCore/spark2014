package Bad_Traversal with SPARK_Mode is

   function F (X : access Integer) return access Integer
     with Side_Effects;

end;
