package P with SPARK_Mode is
   type T is private;
private
   type T is access function return Boolean with Type_Invariant => T.all;
end;
