package body P is
   protected body PT is
      entry E when X is
      begin
         X := False;
         declare
            package Q with Initial_Condition => X is
            end Q;
         begin
            null;
         end;
      end E;
   end PT;
end P;
