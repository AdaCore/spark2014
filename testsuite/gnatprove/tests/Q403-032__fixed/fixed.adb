procedure Fixed with SPARK_Mode is
   type T is delta 0.1 range 0.0 .. 1.0;
   X : T := 0.5;
   Y : T;
begin
   Y := T'Min (X, T'Max (X, X));
end Fixed;
