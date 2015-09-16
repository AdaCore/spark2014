package body Alias is

   G : T;

   procedure Proc (X : in T)
     with Pre => True, Global => (in_out => G)
   is
   begin
      G := X + G;
   end;

   procedure Test is
   begin
      Proc (G);
   end;

end;
