procedure Foo with SPARK_Mode is
   type R is record
      Cell : Integer;
   end record;
   type AR is access R;
   type R2 is record
      Cell : AR;
   end record;
   type AR2 is access R2;
   function Self (X : access constant R2) return access constant R2 is (X);
   procedure Test (X : AR2) with Global => null;
   procedure Test (X : AR2) is
      Y : access R := Self (X).Cell;
   begin
      null;
   end Test;
begin
   null;
end Foo;
