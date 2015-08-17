package internal_protected_call is
   protected type Mutual_Entry_Proc_Calls is
      entry E;
      procedure P;
   end;

   protected type Entry_Calls_Proc is
      entry E;
      procedure P;
   end;

   protected type Proc_Calls_Entry is
      procedure P1;
      procedure P2;
      entry E;
   end;

   PT : Proc_Calls_Entry;
end;
