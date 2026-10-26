package body Protected_Owner with SPARK_Mode is
   protected body Cell is
      procedure Inner is
      begin
         if P = null then
            P := new Integer'(0);
         end if;
      end Inner;
      procedure Outer is
      begin
         --  Refresh the owning component through the implicit protected self
         Inner;
      end Outer;
   end Cell;
end Protected_Owner;
