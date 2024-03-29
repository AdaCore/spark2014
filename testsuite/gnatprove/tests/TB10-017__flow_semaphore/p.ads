with GNAT.Semaphores;

package P is

   protected Sync is
      procedure Proc; --@CEILING_PRIORITY_PROTOCOL:FAIL
   end Sync;

   Sem : GNAT.Semaphores.Binary_Semaphore
     (Initially_Available => False,
      Ceiling => GNAT.Semaphores.Default_Ceiling);

end P;
