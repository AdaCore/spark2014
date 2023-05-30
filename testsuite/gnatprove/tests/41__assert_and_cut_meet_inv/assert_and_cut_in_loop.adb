procedure Assert_and_cut_in_loop with SPARK_Mode is
   X : Boolean := True;
   procedure Shutoff_Warnings
     with Import, Global => (In_Out => X), Annotate => (GNATprove, Always_Return);
begin
   while X loop
      pragma Loop_Invariant (True);
      pragma Assert_And_Cut (True); -- Supported (special case)
      Shutoff_Warnings;
   end loop;
   while not X loop
      pragma Assert_And_Cut (True); -- Unsupported;
      pragma Loop_Invariant (True);
      Shutoff_Warnings;
   end loop;
   while X loop
      pragma Assert_And_Cut (True); -- Unsupported
      begin
         pragma Loop_Invariant (True);
      end;
      pragma Assert_And_Cut (True); -- Unsupported
   end loop;
   while not X loop
      begin
         begin
            pragma Assert_And_Cut (True); -- Fine
         end;
         pragma Loop_Invariant (True);
         begin
            pragma Assert_And_Cut (True); -- Fine
         end;
         Shutoff_Warnings;
         if X then
            pragma Assert_And_Cut (True); -- Fine
         end if;
      end;
   end loop;
   while X loop
      pragma Assert_And_Cut (True); -- Unsupported
      pragma Loop_Invariant (True);
      pragma Assert_And_Cut (True); -- Fine (special case)
   end loop;
end Assert_and_cut_in_loop;
