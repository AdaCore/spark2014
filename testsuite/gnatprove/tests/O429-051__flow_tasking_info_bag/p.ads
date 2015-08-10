with Ada.Synchronous_Task_Control;

package P is

   protected type PT is
      entry Dummy;
      procedure Proc;
      function Func return Boolean;
      function Func2 return Boolean;
   private
      X : Boolean := True;
   end;

   --  protected object
   PO : PT;

   --  suspension object
   SO : Ada.Synchronous_Task_Control.Suspension_Object;

   --  unsynchronized object
   type Rec is
      record
         X, Y, Z : Integer;
      end record;

   R : Rec;

   Nonatomic_Int : Integer;

   Atomic_Int : Integer
     with Atomic;

   --  constant after elaboration and not
   CAE : Integer := 1
     with Constant_After_Elaboration => True;

   CAE_Not : Integer := 2
     with Constant_After_Elaboration => False;

   procedure Call;

end;
