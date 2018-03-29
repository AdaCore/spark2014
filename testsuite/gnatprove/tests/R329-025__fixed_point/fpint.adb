procedure Fpint with SPARK_Mode is
   C : constant := 2.0/5.0;
   type T is delta C range -1.0 .. 1.0 with Small => C;
   X : Integer := 0;
   Y : T;
begin
   Y := T(X);
   X := Integer(Y);
end Fpint;
