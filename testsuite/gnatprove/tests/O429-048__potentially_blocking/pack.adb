package body Pack is

   protected body PO_Proc is

      procedure Proc is
      begin
         null;
      end;

      entry E_Proc when True is
      begin
          Unrelated_Proc;
      end;

   end;

   protected body PO_Func is

      function Func return Boolean is
      begin
         return True;
      end;

      entry E_Func when True is
      begin
         Unrelated_Func;
      end;

   end;

   procedure Unrelated_Proc is
   begin
      PO_Proc.Proc;
   end;

   procedure Unrelated_Func is
      X : constant Boolean := PO_Func.Func;
   begin
      null;
   end;

   protected body PO_Safe is

      function Func return Boolean is
      begin
         return True;
      end;

      procedure Proc is
      begin
         null;
      end;

      entry E_Safe when True is
         X : constant Boolean := Func;
      begin
         Unrelated_Proc;
         PO_Safe.Proc;
         Proc;
      end;

   end;

end;
