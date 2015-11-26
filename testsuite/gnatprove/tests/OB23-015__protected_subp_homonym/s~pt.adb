separate (S)
protected body PT is
   procedure Set (Q : Integer) is
   begin
      P_Int := Q;
   end;

   procedure Set (Q : Boolean) is
   begin
      P_Bool := Q;
   end;

end PT;
