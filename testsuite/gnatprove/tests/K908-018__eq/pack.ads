package Pack is

   type Ar is array (1 .. 10) of Integer;

   type Rec is record
      F1 : Integer;
      F2 : Integer;
   end record;

   function Equal (A, B : Ar) return Boolean
     with Post => (Equal'Result = (A = B));

   function Equal (A, B : Rec) return Boolean
     with Post => (Equal'Result = (A = B));

end Pack;
