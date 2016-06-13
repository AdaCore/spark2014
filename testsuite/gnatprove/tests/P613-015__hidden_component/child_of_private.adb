package body Child_Of_Private with SPARK_Mode is
   procedure P is
      C : Child;
   begin
      C.Hidden_G := 1;
   end P;
end Child_Of_Private;
