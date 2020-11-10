package body P is

   protected body Sync is
      procedure Proc is
      begin
         Sem.Release;
      end Proc;
   end Sync;

end P;
