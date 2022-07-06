package body Test_Route with SPARK_Mode is

   procedure Shift_X (P : not null access Point; S : Integer) is
   begin
      P.X := P.X + S;
   end Shift_X;

   function All_X (R : access constant Route) return Int_Seq is
      C : Big_Natural := 0;
      X : access constant Route := R;
   begin
      return A : Int_Seq do
         while X /= null loop
            pragma Loop_Variant (Structural => X);
            pragma Loop_Invariant (C = Length (R) - Length (X));
            pragma Loop_Invariant (Length (A) = C);
            pragma Loop_Invariant
              (for all I in Interval'(1, Length (A)) => Get (A, I) = Nth_X (R, I));
            pragma Loop_Invariant
              (for all I in Interval'(C + 1, Length (R)) => Nth_X (X, I - C) = Nth_X (R, I));
            A := Add (A, X.Current.X);
            X := X.Rest;
            C := C + 1;
         end loop;
      end return;
   end All_X;

   function Nth_Point (R : access Route; N : Big_Positive) return not null access Point is
   begin
      if N = 1 then
         return R.Current;
      else
         return Nth_Point (R.Rest, N - 1);
      end if;
   end Nth_Point;

   procedure Shift_Nth_X (R : access Route; N : Big_Positive; S : Integer) is
      P : access Point := Nth_Point (R, N);
   begin
      Shift_X (P, S);
   end Shift_Nth_X;

end Test_Route;
