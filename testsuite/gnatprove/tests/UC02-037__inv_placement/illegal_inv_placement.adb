procedure Illegal_Inv_Placement with SPARK_Mode is
   Found : exception;
   function Prop (I : Integer) return Boolean with
     Global => null,
     Import;
begin
   for I in 1 .. 100 loop
      begin
         if Prop (I) then
            raise Found;
         end if;
         pragma Loop_Invariant (for all K in 1 .. I => not Prop (K));
      exception
         when Found => null;
      end;
   end loop;
end Illegal_Inv_Placement;
