procedure Main with SPARK_Mode is
   type R is record
      C : not null access procedure (X : in out Natural);
   end record;
   type A is array (Integer range 1 .. 1) of access procedure (X : in out Natural);
begin
   null;
end;
