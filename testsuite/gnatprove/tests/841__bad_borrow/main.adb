procedure Main with SPARK_Mode is

   X : access Integer := new Integer'(12);

begin
  X.all := 13;
end Main;
