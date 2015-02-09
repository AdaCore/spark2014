package body Parent.Pub_Child is
   overriding procedure Initialize (E : out Extended_T) is
   begin
      Root_T (E).X := 1;  --  Not really needed but shouldn't hurt either...
      E.Y := 1;
   end Initialize;
end Parent.Pub_Child;
