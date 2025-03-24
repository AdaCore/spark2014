procedure Main with SPARK_Mode is
   X : aliased Integer := 0;
   type Int_Acc is access all Integer;
   Y : Int_Acc;
   function Random return Boolean with Import;
begin
   if Random then
      Y := X'Access;
   else
      Y := X'Access;
   end if;
end Main;
