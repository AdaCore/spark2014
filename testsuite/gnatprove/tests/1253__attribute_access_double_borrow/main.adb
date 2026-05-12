procedure Main with SPARK_Mode is
   type AInt is access Integer;
   type AAInt is access AInt;
   type R is record
      X : AAInt;
      Y : AInt;
   end record;
   Z : aliased R := (X => new AInt'(new Integer'(0)), Y => new Integer'(0));
   U : access AInt := Z.X.all'Access;
   W : access constant R := Z'Access;
   V : access constant Integer := Z.X.all.all'Access;
begin
   null;
end Main;
