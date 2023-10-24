package body Local_Global with SPARK_Mode is
   function F (X : T) return Boolean is
      G : T := (A => True);
      procedure P with Pre => True is
      begin
         pragma Assert (G.A);
      end P;
   begin
      P;
      return True;
   end F;
end;
