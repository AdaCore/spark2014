with Ada.Containers.Functional_Vectors;
procedure Test_Route with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   type Point is record
      X, Y : Integer;
   end record;
   type Point_Acc is not null access Point;

   procedure Shift_X (P : not null access Point; S : Integer) with
     Pre  => (if S > 0 then P.X <= Integer'Last - S
              else P.X >= Integer'First - S),
     Post => P.X = P.X'Old + S
     and P.Y = P.Y'Old
   is
   begin
      P.X := P.X + S;
   end Shift_X;

   -- List of Points
   type Route;
   type Route_Acc is access Route;
   type Route is record
      Current : Point_Acc;
      Rest    : Route_Acc;
   end record;

   function Length (R : access constant Route) return Natural is
     (if R = null then 0
      else Integer'Min (Integer'Last - 1, Length (R.Rest)) + 1)
   with Annotate => (GNATprove, Terminating);

   function Nth_X (R : access constant Route; N : Positive) return Integer is
     (if N = 1 then R.Current.X else Nth_X (R.Rest, N - 1))
   with Annotate => (GNATprove, Terminating),
     Pre => N <= Length (R);

   package Int_Seqs is new Ada.Containers.Functional_Vectors
     (Index_Type   => Positive,
      Element_Type => Integer);
   type Int_Seq is new Int_Seqs.Sequence;

   function All_X (R : access constant Route) return Int_Seq with
     Post => Last (All_X'Result) = Length (R)
     and (for all N in 1 .. Length (R) =>
              Get (All_X'Result, N) = Nth_X (R, N))
   is
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

   function At_End_Borrow (P : access constant Point) return access constant Point is
     (P)
   with Ghost,
     Annotate => (GNATprove, At_End_Borrow);
   function At_End_Borrow (P : access constant Route) return access constant Route is
     (P)
   with Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   function Nth_Point (R : access Route; N : Positive) return not null access Point
   with
     Pre  => N < Length (R),
     Post =>
        Length (At_End_Borrow (R)) = Length (R)
        and Nth_X (At_End_Borrow (R), N) = At_End_Borrow (Nth_Point'Result).X
        and (for all I in 1 .. Length (At_End_Borrow (R)) =>
               (if I /= N then Nth_X (At_End_Borrow (R), I) = Nth_X (R, I)))
   is
      L1 : constant Natural := Length (R);
   begin
      if N = 1 then
         return R.Current;
      else
         return Nth_Point (R.Rest, N - 1);
      end if;
   end Nth_Point;

   procedure Shift_Nth_X (R : access Route; N : Positive; S : Integer) with
     Pre  => N < Length (R)
     and then (if S > 0 then Nth_X (R, N) <= Integer'Last - S
               else Nth_X (R, N) >= Integer'First - S),
     Post => Length (R) = Length (R)'Old
     and then Nth_X (R, N) = Nth_X (R, N)'Old + S
     and then (for all I in 1 .. Length (R) =>
              (if I /= N then Nth_X (R, I) = Get (All_X (R)'Old, I)))
   is
      P : access Point := Nth_Point (R, N);
   begin
      Shift_X (P, S);
   end Shift_Nth_X;
begin
   null;
end Test_Route;
