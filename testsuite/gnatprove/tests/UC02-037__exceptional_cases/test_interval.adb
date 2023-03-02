procedure Test_Interval with SPARK_Mode is

   type Interval is record
      F, L : Integer;
   end record with
     Predicate => F <= L;

   type Intervals is array (Positive range <>) of Interval with
     Predicate =>
       (for all I1 in Intervals'Range =>
          (for all I2 in Intervals'Range =>
             (if I1 < I2 then Intervals (I1).L < Intervals (I2).F)));

   Not_Found : exception;

   procedure Find_Interval (A : Intervals; V : Integer; R : out Interval) with
     Relaxed_Initialization => R,
     Post => R'Initialized
       and then V in R.F .. R.L
       and then (for some E of A => E = R),
     Exceptional_Cases =>
       (Not_Found => (for all E of A => V not in E.F .. E.L));

   procedure Find_Interval (A : Intervals; V : Integer; R : out Interval) is
      procedure Test_One (I : Interval; Found : out Boolean) with
        Contract_Cases =>
          ((V in I.F .. I.L) => Found and R'Initialized and R = I,
           V < I.F           => False,
           V > I.L           => not Found),
        Exceptional_Cases => (Not_Found => V < I.F);

      procedure Test_One (I : Interval; Found : out Boolean) is
      begin
         if V < I.F then
            raise Not_Found;
         elsif V <= I.L then
            R := I;
            Found := True;
         else
            Found := False;
         end if;
      end Test_One;

   begin
      for K in A'Range loop
         pragma Loop_Invariant (K = A'First or else V > A (K - 1).L);
         declare
            Found : Boolean;
         begin
            Test_One (A (K), Found);
            if Found then
               return;
            end if;
         end;
      end loop;
      raise Not_Found;
   end Find_Interval;

   function Find_Interval (A : Intervals; V : Integer) return Interval with
     Pre  => (for some E of A => V in E.F .. E.L),
     Post => V in Find_Interval'Result.F .. Find_Interval'Result.L
     and then (for some E of A => E = Find_Interval'Result);

   function Find_Interval (A : Intervals; V : Integer) return Interval is
      R : Interval;
   begin
      Find_Interval (A, V, R);
      return R;
   end Find_Interval;

begin
   null;
end;
