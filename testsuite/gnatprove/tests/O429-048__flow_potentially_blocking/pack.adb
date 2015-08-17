package body Pack is

   protected body PO_Proc is

      procedure Proc is
      begin
         null;
      end;

      --  POTENTIALLY BLOCKING:
      --  Call to external procedure that in turn
      --  calls the same protected object.
      entry E_Proc when True is
      begin
          External_Call_To_Protected_Proc;
      end;

   end;

   protected body PO_Func is

      function Func return Boolean is
      begin
         return True;
      end;

      --  POTENTIALLY BLOCKING:
      --  Call to external function that in turn
      --  calls the same protected object.
      entry E_Func when True is
      begin
         External_Call_To_Protected_Func;
      end;

   end;

   procedure External_Call_To_Protected_Proc is
   begin
      -- rewritten from N_Procedure_Call_Statement to N_Entry_Call_Statement
      -- with different Node_Ids; Convention (Entity ( Selector_name( Name))) =
      -- Convention_Protected
      PO_Proc.Proc;
   end;

   procedure External_Call_To_Protected_Func is
      -- N_Function_Call; Convention (Entity ( Selector_name( Name))) =
      -- Convention_Protected
      X : constant Boolean := PO_Func.Func;
   begin
      null;
   end;

   --  No potentially blocking operations for this PO
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
         --  Internal call to protected function (without prefix)
         X : constant Boolean := Func;
         --  Internal call to protected function (with prefix)
         Y : constant Boolean := PO_Safe.Func;
      begin
         --  Internal call to protected procedure (without prefix)
         Proc;
         --  Internal call to protected procedure (with prefix)
         PO_Safe.Proc;

         --  Directs calls to protected subprograms of other POs
         PO_Proc.Proc;
         declare
            Dummy : constant Boolean := PO_Func.Func;
         begin
            null;
         end;

         --  External (indirect) calls to protected subprograms of other POs
         External_Call_To_Protected_Proc;
         External_Call_To_Protected_Func;
      end;

   end;

end;
