with System; use System;

procedure Main with
   SPARK_Mode
is
   procedure Set_Boolean
     (Variable_To_Set  :    out Boolean;
      Address_Of_Value : in Address) with Depends => (Variable_To_Set => Address_Of_Value)
   is
      Value_In_Spark : Boolean with
         Address => Address_Of_Value,
         Import;
   begin
      Variable_To_Set := Value_In_Spark;
   end Set_Boolean;
begin
   null;
end Main;
