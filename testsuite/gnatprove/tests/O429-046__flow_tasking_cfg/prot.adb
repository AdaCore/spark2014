package body Prot
  with Refined_State => (State => (Hidden, Hidden2))
is
   Hidden  : Integer := 0;
   Hidden2 : Integer;

   protected body P_Int is
      procedure Get (X : out Integer) is
      begin
         if D > 0 then
            X := The_Protected_Int;
         else
            X := Hidden;
         end if;
      end Get;

      function Weird_Get (X : Integer) return Integer is
      begin
         return The_Protected_Int + Visible + X;
      end Weird_Get;

      entry Set (X : Integer) when D > 0 is
      begin
         Hidden := Visible;
         The_Protected_Int := X + D - Hidden;
      end Set;
   end P_Int;

begin
   Hidden2 := 0;
end Prot;
