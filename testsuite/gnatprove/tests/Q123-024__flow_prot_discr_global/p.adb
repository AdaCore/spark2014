package body P is

   task body TT is
      procedure Inner_TT with Pre => True, Global => X is
      begin
         pragma Assert (X > 0);
      end;
   begin
      loop
         Inner_TT;
      end loop;
   end TT;

   protected body PT is
      procedure Proc is
         procedure Inner_PT with Pre => True, Global => X is
         begin
            pragma Assert (X > 0);
         end Inner_PT;
      begin
         Inner_PT;
      end Proc;
   end PT;

end P;
