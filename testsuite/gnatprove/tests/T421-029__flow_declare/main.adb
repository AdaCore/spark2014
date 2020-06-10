procedure Main with SPARK_Mode is
   X : Boolean;

   Y : Positive :=
     (declare
        Z : constant Boolean := X;  --  read of uninitialized data
      begin
        123);
begin
   X := True;  --  dummy assignment, too late
end;
