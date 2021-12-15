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

   procedure Call is
      X : Boolean := PO.Func;
   begin
      PO.Dummy;
      PO.Proc;
      R.X := 1;

      Nonatomic_Int := Atomic_Int;
      Atomic_Int := Nonatomic_Int;
      --  Call to suspension object is now not allowed
      --  Ada.Synchronous_Task_Control.Suspend_Until_True (SO);

      CAE_Not := CAE;
   end;

end;
