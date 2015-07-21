procedure Not_A_Suspension_Object
  with SPARK_Mode
is
   package Ada is

      package Synchronous_Task_Control is

         type Suspension_Object is (A,B,C);

      end;

   end;

   SO : Ada.Synchronous_Task_Control.Suspension_Object := Ada.Synchronous_Task_Control.A;
begin
   null;
end;
