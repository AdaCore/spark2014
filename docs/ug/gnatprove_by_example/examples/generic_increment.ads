generic
   type T is range <>;
procedure Generic_Increment (X : in out T) with
  SPARK_Mode,
  Pre  => X < T'Last,
  Post => X = X'Old + 1;
