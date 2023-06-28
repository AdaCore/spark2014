procedure Effect is
   Check_Failure : exception;

   procedure Check (Condition : Boolean) with
     Exceptional_Cases => (Check_Failure => not Condition);

   procedure Check (Condition : Boolean) is
   begin
      if not Condition then
         raise Check_Failure;
      end if;
   end Check;
begin
   null;
end Effect;
