procedure Nested_Packages with SPARK_Mode is
   package Outer is
      X : Integer := 0;
      Y : Integer := 1 with Address => X'Address;
      package Inner is
      end Inner;
   end Outer;
begin
   null;
end Nested_Packages;
