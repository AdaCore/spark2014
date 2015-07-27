with Ada.Synchronous_Task_Control;

package body P is

   --  protected type

   protected body PT is

      entry Dummy when True is
      begin
         null;
      end;

      procedure Proc is
      begin
         X := not X;
      end;

      function Func return Boolean is
      begin
         return (if Func2 then X else not X);
      end;

      function Func2 return Boolean is
      begin
         return X;
      end;

   end;

   --  protected object
   PO : PT;

   --  suspension object
   SO : Ada.Synchronous_Task_Control.Suspension_Object;

   procedure Call is
      X : Boolean := PO.Func;
   begin
      PO.Dummy;
      PO.Proc;
      --  Ada.Synchronous_Task_Control.Suspend_Until_True (SO);
   end;

end;

