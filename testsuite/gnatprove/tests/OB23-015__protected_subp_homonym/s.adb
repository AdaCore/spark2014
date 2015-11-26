package body S is

   protected body PT is separate;

   procedure Proc is
   begin
      PO.Set (0);
      PO.Set (True);
   end Proc;

end;
