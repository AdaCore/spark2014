procedure Main
  with
    SPARK_Mode => On
is

   type Interval is record
      F, L : Integer;
   end record with
     Predicate => F <= L;

   type Intervals is array (Positive range <>) of Interval with
     Predicate =>
       (for all I1 in Intervals'Range =>
          (for all I2 in Intervals'Range =>
             (if I1 < I2 then Intervals (I1).L < Intervals (I2).F)));

   procedure Find_Interval (A : Intervals; V : Integer; R : aliased out Interval) with
     Relaxed_Initialization => R,
     Pre => (for some E of A => V in E.F .. E.L),
     Post => R'Initialized and then V in R.F .. R.L and then (for some E of A => E = R);

   procedure Find_Interval (A : Intervals; V : Integer; R : aliased out Interval) is
   begin
      for K in A'Range loop
         pragma Loop_Invariant (K = A'First or else V > A (K - 1).L);
         if V <= A (K).L then
            R := A (K);
            return;
         end if;
      end loop;
   end Find_Interval;

begin
   null;
end Main;
