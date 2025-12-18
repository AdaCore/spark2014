procedure Main with SPARK_Mode is
   package P1 is
      type R is record
         F : access function return Boolean;
      end record;
      X : R;
      Y : Integer with Address => X.F'Address, Import;
   end P1;

   package P2 is
      type I is range 0 .. 2;
      type R is record
         F :I'Base;
      end record;
      X : R;
      Y : Integer with Address => X.F'Address, Import;
   end P2;

   package P3 is
      type J is range 0 .. 10;
      type I is new J range 0 .. 10;
      type R is access constant I'Base range 1 .. 3;
      X : R with Import;
      Y : constant Integer with Address => X.all'Address, Import;
   end P3;
begin
   null;
end Main;
