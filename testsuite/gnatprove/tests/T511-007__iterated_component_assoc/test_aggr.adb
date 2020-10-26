procedure Test_Aggr with SPARK_Mode is
   type My_Arr is array (Positive range <>) of Integer;
   type My_Matrix is array (Positive range <>, Positive range <> ) of Integer;

   function Rand (X : Integer) return Integer with Import;

   procedure Incr (X : in out My_Arr) with
     Pre => (for all E of X => E <= 100) and X'First = 1 and X'Last = 20,
     Post => X = (for I in 1 .. 10 => X'Old (I) + 1, 11 .. 20 => 0)
   is
   begin
      X := (for I in 1 .. 10 => @ (I) + 1, others => 0);
   end Incr;

   procedure Incr_2 (X : in out My_Arr) with
     Pre => (for all E of X => E <= 100),
     Post => X = (for I in X'First .. X'Last => X'Old (I) + 1)
   is
   begin
      for I in X'Range loop
         X (I) := @ + 1;
         pragma Loop_Invariant (X (X'First .. I) = (for K in X'First .. I => X'Loop_Entry (K) + 1));
      end loop;
   end Incr_2;

   procedure Incr_3 (X : in out My_Arr) with
     Pre => (for all E of X => E <= 100) and X'First = 1 and X'Last >= 10,
     Post => X = (X with delta for I in 2 .. 10 => X (1))
   is
   begin
      X (2 .. 10) := (declare
                        C : constant Integer := 1;
                      begin (for I in 2 .. 10 =>
                               (declare
                                  E : constant Integer := X (C);
                                begin
                                E)));
   end Incr_3;

   C : Integer := 15;

   procedure Set (X : in out My_Arr) with
     Pre => X'First = 1 and X'Last > 11 and C < 100,
     Post => X (12 .. X'Last) = (for I in 12 .. X'Last => X'Old (I))
   is
   begin
      X (1 .. 11) := (1 => 0, 2 | 5 => 1, for I in 3 .. 4 | 6 .. 10 => I + C, 11 => 33);
   end Set;

   A : My_Arr := (for I in 1 .. 15 => I);
   B : My_Arr := (for I in 1 .. 15 => I + Rand (I)); --@OVERFLOW_CHECK:FAIL
   D : My_Arr := (for I in 1 .. Rand (0) + 15 => I); --@OVERFLOW_CHECK:FAIL
   E : My_Matrix := (1 .. 15 => (1 .. Rand (-2) + 12 => 0)); --@OVERFLOW_CHECK:FAIL
begin
   Set (A);
end Test_Aggr;
