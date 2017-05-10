package body P with
  SPARK_Mode => Off
is

   protected body Suspension_Object is

      function Get_Open return Boolean is
      begin
         return True;
      end Get_Open;

   end Suspension_Object;

   function Get_Current_State (SO : in out Suspension_Object) return Boolean
   is
   begin
      return SO.Get_Open;
   end;

end;
