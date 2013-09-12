package A is 

   function Pgcd (A, B : in Integer) return Integer;
   pragma Precondition (A /= Integer'First);
   pragma Precondition (B /= Integer'First);
   pragma Postcondition
     (Pgcd'Result = 0
     or else Pgcd'Result in 1 .. abs A
     or else Pgcd'Result in 1 .. abs B);

   function Ppcm (A, B : in Integer) return Integer;
   pragma Precondition (A /= Integer'First);
   pragma Precondition (B /= Integer'First);
   pragma Precondition (abs (Long_Integer (A) * Long_Integer (B))
                         <= Long_Integer (Integer'Last));
   pragma Postcondition
     (Ppcm'Result = 0
     or else Ppcm'Result in abs A .. abs (A * B)
     or else Ppcm'Result in abs B .. abs (A * B));

end A;
