with GNAT.Semaphores;

package P2 is

   package Nested is

      --  Anonymous protected type
      protected SyncA is
         procedure Proc; --@CEILING_PRIORITY_PROTOCOL:FAIL
      end;

      --  Explicit protected type
      protected type SyncB_Type is
         procedure Proc; --@CEILING_PRIORITY_PROTOCOL:FAIL
      end;

      Sem :
        GNAT.Semaphores.Binary_Semaphore
          (Initially_Available => False,
           Ceiling => GNAT.Semaphores.Default_Ceiling);

   end;

end;
