procedure Actions (X, Y : in out Integer; B1, B2, B3, B4, B5, B6 : Boolean) is
   type T is array (1 .. 10) of Integer;
   A : T := (others => 0);

   type Barr is array (1 .. 10) of Boolean;
   B : Barr;

begin
   if X not in 1 .. Y
     or else Y not in 5 .. 9
   then
      return;
   end if;

   A(X) := 1;

   if B1 then
      pragma Assert (X <= 5 or else (for some J in 6 .. Y + 1 => A (J) = 1));

   elsif B2 then
      pragma Assert (case X is when 1 .. 5 => True,
                               when others => (for some J in 6 .. Y + 1 => A (J) = 1));

   elsif B3 then
      pragma Assert (if X <= 5 then True else (for some J in 6 .. Y + 1 => A (J) = 1));

   elsif B4 then
      pragma Assert (if X > 5 then (for some J in 6 .. Y + 1 => A (J) = 1));

   elsif B5 then
      if X <= 5 then
         null;
      elsif (for some J in 6 .. Y + 1 => A (J) = 1) then
         null;
      else
         --  encoding of pragma Assert (False), to avoid label problem
         pragma Assert (X < 5 and then X > 6);
      end if;

   elsif B6 then
      while (for some J in 6 .. Y + 1 => A (J) = 1) loop
         exit;
      end loop;

   else
      declare
         V : Integer := 0;
         function F return Integer with Pre => Y in 5 .. 9;
         function F return Integer is
         begin
            return Y + 1;
         end F;
      begin
         -- to be decommented when L309-013 is solved
         --B := (others => (for some J in 6 .. F => A (J) = 1));
         null;
      end;
   end if;

end Actions;
