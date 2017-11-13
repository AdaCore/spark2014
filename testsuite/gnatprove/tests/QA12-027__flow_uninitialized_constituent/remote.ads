package Remote
  with SPARK_Mode => Off
is
   type B is private with Default_Initial_Condition;

private
   type B is record
      X : Integer := 0;
   end record;
end;
