package Q with SPARK_Mode is
   package Mixed with SPARK_Mode is
      type T is private;
   private
      pragma SPARK_Mode (Off);
      type T is access Integer with Predicate => T /= null;
   end;

   subtype T1 is Mixed.T with Predicate => True;
end;
