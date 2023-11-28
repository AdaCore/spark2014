pragma Ada_2022;
procedure Sideeffects is

   function Call return Integer is
      function Increment_And_Return (X : in out Integer) return Integer
        with Side_Effects;

      function Increment_And_Return (X : in out Integer) return Integer is
      begin
         X := X + 1;
         return X;
      end;

      G : Integer := 0;
      function Increment_G_And_Return return Integer
      with
        Side_Effects,
        Global => (In_Out => G),
        Depends => ((G, Increment_G_And_Return'Result) => G),
        Exceptional_Cases => (others => True),
        Always_Terminates => False;

      function Increment_G_And_Return return Integer is
         Y : Integer;
      begin
         Y := Increment_And_Return (G);
         if G < 0 then
            loop
               null;
            end loop;
         elsif G > 10 then
            raise Program_Error;
         end if;
         return Y;
      end;

      X : Integer := 5;
      Y : Integer;
   begin
      Y := Increment_And_Return (X);
      pragma Assert (X = Y);
      Y := Increment_G_And_Return;
      pragma Assert (G = Y);
      declare
         Z : Integer;
      begin
         Z := Increment_And_Return (X);
      end;
      return X;
   end Call;

   H : Integer;

   function Increment_And_Return (X, Y : in out Integer) return Integer
     with Side_Effects;

   function Increment_And_Return (X, Y : in out Integer) return Integer is
   begin
      X := X + 1;
      Y := Y + 1;
      H := H + 1;
      return X + H;
   end;

   procedure Incr (X : in out Integer) is
   begin
      X := X + 1;
      H := H + 1;
   end;

   V1, V2, V3 : Integer;

   T : array(1..3) of Integer;
begin
   V1 := Call + Call;
   V1 := Increment_And_Return (V2, V3); -- @ALIASING:NONE
   Incr (H);
   V1 := Increment_And_Return (H, V2); -- @ALIASING:CHECK
   V1 := Increment_And_Return (V1, V2); -- @ALIASING:CHECK
   T(V1) := Increment_And_Return (V1, V2); -- @ ALIASING:CHECK
   T(V1) := Increment_And_Return (T(V1), T(V2)); -- @ALIASING:CHECK
   pragma Assert (V1 = V2);
end;
