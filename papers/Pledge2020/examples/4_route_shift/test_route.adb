package body Test_Route with SPARK_Mode is

   procedure Shift_X (P : not null access Point; S : Integer) is
   begin
      P.X := P.X + S;
   end Shift_X;

   function All_X (R : access constant Route) return Int_Seq is
   begin
      return A : Int_Seq do
         for N in 1 .. Length (R) loop
            pragma Loop_Invariant (Last (A) = N - 1);
            pragma Loop_Invariant
              (for all I in 1 .. N - 1 => Get (A, I) = Nth_X (R, I));
            A := Add (A, Nth_X (R, N));
         end loop;
      end return;
   end All_X;

   function Nth_Point (R : access Route; N : My_Pos) return not null access Point is
   begin
      if N = 1 then
         return R.Current;
      else
         return Nth_Point (R.Rest, N - 1);
      end if;
   end Nth_Point;

   procedure Shift_Nth_X (R : access Route; N : My_Pos; S : Integer) is
      P : access Point := Nth_Point (R, N);
   begin
      Shift_X (P, S);
   end Shift_Nth_X;

end Test_Route;
