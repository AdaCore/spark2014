with Ada.Synchronous_Barriers;

package body p is

   SB : Ada.Synchronous_Barriers.Synchronous_Barrier (2);

   task body T1 is
      Notified : Boolean;
   begin
      Ada.Synchronous_Barriers.Wait_For_Release (SB, Notified);
   end;

   task body T2 is
      Notified : Boolean;
   begin
      Ada.Synchronous_Barriers.Wait_For_Release (SB, Notified);
   end;

end;
