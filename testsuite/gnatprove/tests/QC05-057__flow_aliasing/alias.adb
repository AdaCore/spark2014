package body Alias is

   G : Boolean := True;

   procedure P (X : in out Boolean) with Global => G is
   begin
      X := G and X;
   end P;

   procedure Test1 is
   begin
      P (G);  -- here we detect aliasing
      loop
         null; -- typically we would put some delay here
      end loop;
   end;

   procedure Test2 is
      procedure Neverending with No_Return is
      begin
         loop
            null;
         end loop;
      end;
   begin
      P (G);       -- here we also should detect aliasing
      Neverending; -- this is the same as the loop in Test1
   end;
end Alias;
