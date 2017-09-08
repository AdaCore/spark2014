procedure Rendezvous is

   task T1 is
      entry Start;
   end T1;

   task body T1 is
   begin
      accept Start;
   end T1;

begin
   T1.Start;
end Rendezvous;
