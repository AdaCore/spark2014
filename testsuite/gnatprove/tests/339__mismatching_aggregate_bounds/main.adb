procedure Main with SPARK_Mode is
   type A is array (Natural range <>, Natural range <>) of Integer;
   function F return Integer is (0);
   Y : constant Integer := F;
   X : A := (0 => (Y .. Y + 3 => 0),
             1 => (Y + 1 .. Y + 2 => 1)); --@INDEX_CHECK:FAIL
begin
   null;
end Main;
