with Synchronous_Barriers;

package body Barrier is

   SB : Synchronous_Barriers.Synchronous_Barrier (1);

   procedure Wait is
      Notified : Boolean;
   begin
      Synchronous_Barriers.Wait_For_Release (SB, Notified);
   end;

end;
