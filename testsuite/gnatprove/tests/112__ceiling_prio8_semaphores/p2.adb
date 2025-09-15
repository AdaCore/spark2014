package body P2 is

   package body Nested is

      protected body SyncA is
         procedure Proc is
         begin
            Sem.Release;
         end Proc;
      end;

      protected body SyncB_Type is
         procedure Proc is
         begin
            Sem.Release;
         end Proc;
      end;

   end;

end;
