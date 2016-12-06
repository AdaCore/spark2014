with My_Types; use My_Types;
package body Discr_Checks with SPARK_Mode is

   procedure Check_Subtype_Rec is
      subtype Fail is Rec (Bad); --@RANGE_CHECK:FAIL
   begin
      null;
   end Check_Subtype_Rec;

   procedure Check_Derived_Rec is
      type Fail is new Rec (Bad); --@RANGE_CHECK:FAIL
   begin
      null;
   end Check_Derived_Rec;

   procedure Check_Subtype_Priv is
      subtype Fail is Priv (Bad); --@RANGE_CHECK:FAIL
   begin
      null;
   end Check_Subtype_Priv;

   procedure Check_Derived_Priv is
      type Fail is new Priv (Bad); --@RANGE_CHECK:FAIL
   begin
      null;
   end Check_Derived_Priv;

   procedure Check_Subtype_Prot is
      subtype Fail is Prot (Bad); --@RANGE_CHECK:FAIL
   begin
      null;
   end Check_Subtype_Prot;

   --  Not handled correctly by the frontend

   procedure Check_Derived_Prot with SPARK_Mode => Off is
      type Fail is new Prot (Bad);
   begin
      null;
   end Check_Derived_Prot;

   procedure Check_Subtype_Task is
      subtype Fail is T (Bad); --@RANGE_CHECK:FAIL
   begin
      null;
   end Check_Subtype_Task;

   --  Not handled correctly by the frontend

   procedure Check_Derived_Task with SPARK_Mode => Off is
      type Fail is new T (Bad);
   begin
      null;
   end Check_Derived_Task;
end Discr_Checks;
