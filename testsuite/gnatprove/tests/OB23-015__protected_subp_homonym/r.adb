package body R is

   protected body PT is
      entry Dummy when True is
         procedure Set (Q : Integer) is
         begin
            P_Int := Q;
         end;

         procedure Set (Q : Boolean) is
         begin
            P_Bool := Q;
         end;
      begin
         Set (0);
         Set (True);
      end;

   end PT;

end R;
