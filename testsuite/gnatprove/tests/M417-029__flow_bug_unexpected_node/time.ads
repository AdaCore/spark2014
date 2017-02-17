package Time is pragma SPARK_Mode (On);

  type Minutes_T is range 0 .. 59;
  type Seconds_T is range 0 .. 59;

  type T is record
     Hours   : Natural;
     Minutes : Minutes_T;
     Seconds : Seconds_T;
  end record;

  Zero : constant T :=
    (Hours   => 0,
     Minutes => 0,
     Seconds => 0);

  Max : constant T :=
    (Hours   => Natural'Last,
     Minutes => Minutes_T'Last,
     Seconds => Seconds_T'Last);

  function T_Increment (X : T) return T with
    Global         => null,
    Pre            => X /= Max,
    Contract_Cases =>
      (X.Seconds < Seconds_T'Last
       =>
        T_Increment'Result.Seconds = X.Seconds + 1
         and then T_Increment'Result.Minutes = X.Minutes
         and then T_Increment'Result.Hours = X.Hours,

       X.Seconds = Seconds_T'Last
        and then X.Minutes < Minutes_T'Last
       =>
        T_Increment'Result.Seconds = 0
         and then T_Increment'Result.Minutes = X.Minutes + 1
         and then T_Increment'Result.Hours = X.Hours,

       X.Seconds = Seconds_T'Last
        and then X.Minutes = Minutes_T'Last
       =>
        T_Increment'Result.Seconds = 0
         and then T_Increment'Result.Minutes = 0
         and then T_Increment'Result.Hours = X.Hours + 1);
   --  Provides part of S.count

end Time;
