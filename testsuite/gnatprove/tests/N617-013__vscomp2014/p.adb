procedure P (F : in out My_Array)
is
   Saved : constant My_Array := F;
begin
   for J in Index loop
      for I in Index loop
         F(I) := J;
         pragma Loop_Invariant (F'Loop_Entry = Saved);
      end loop;
   end loop;
end P;
