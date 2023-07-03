package Q with SPARK_Mode is
   type T is private;
private
   type T is access function return Boolean with Predicate => T.all;
end;
