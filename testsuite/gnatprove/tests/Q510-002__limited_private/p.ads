package P with
  SPARK_Mode
is
   type Suspension_Object is limited private;

private
   pragma SPARK_Mode (Off);

   protected type Suspension_Object is
      function Get_Open return Boolean;
   end Suspension_Object;

end;
