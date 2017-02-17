package Const is
   C : constant Integer := 10_000;
   subtype T is Integer range -C .. C;

   function Incr (X : T) return T
      with Pre => (X < T'Last),
           Post => (X <= C);
end Const;
