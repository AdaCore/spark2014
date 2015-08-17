package body internal_protected_call is

   --  potentially blocking
   protected body Mutual_Entry_Proc_Calls is
      entry E when True is
      begin
         Mutual_Entry_Proc_Calls.P;
         P;
      end;

      procedure P is
      begin
         Mutual_Entry_Proc_Calls.E;
         E;
      end;
   end;

   --  safe
   protected body Entry_Calls_Proc is
      entry E when True is
      begin
         Entry_Calls_Proc.P;
         P;
      end;

      procedure P is
      begin
         null;
      end;
   end;

   --  potentially blocking
   protected body Proc_Calls_Entry is
      procedure P1 is
      begin
         Proc_Calls_Entry.E;
      end;

      procedure P2 is
      begin
         E;
      end;

      entry E when True is
      begin
         null;
      end;
   end;

end;
