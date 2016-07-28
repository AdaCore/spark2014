package User_Lemma is

   function Is_Prime (N : Positive) return Boolean is
     (for all J in Positive range 2 .. N - 1 => N mod J /= 0);

   procedure Number_Is_Prime (N : Positive)
   with
     Ghost,
     Global => null,
     Pre  => N in 15486209 | 15487001 | 15487469,
     Post => Is_Prime (N);

   procedure Test;

end User_Lemma;
