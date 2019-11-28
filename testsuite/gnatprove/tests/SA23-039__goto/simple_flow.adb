procedure Simple_Flow (X : Integer; Y : out Integer)
  with Pre => X in 1 .. 3, Post => Y = X, Global => null
is
begin
   case X is
      when 1 => goto L1;
      when 2 => goto L2;
      when 3 => goto L3;
      when others =>
         case X is
            when 1 => goto L1;
            when 2 => goto L2;
            when 3 => goto L3;
            when others => raise Program_Error;
         end case;
   end case;
   <<L1>> Y := 1; return;
   <<L2>> Y := 2; return;
   <<L3>> Y := 3; return;
   Y := 4;
end;
