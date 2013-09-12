procedure P is 
   generic
        type Bool is (<>);
        F, T : Bool;
   procedure Q;

   procedure Q is
   begin
      null;
   end Q;

   procedure NP1 is new Q ( Bool => Boolean, F => False, T => True );
begin
   null;

end P;
