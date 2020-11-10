with GNAT.Semaphores;

package P is

   protected Sync is
      procedure Proc;
   end Sync;

   Sem : GNAT.Semaphores.Binary_Semaphore
     (Initially_Available => False,
      Ceiling => GNAT.Semaphores.Default_Ceiling);

end P;
