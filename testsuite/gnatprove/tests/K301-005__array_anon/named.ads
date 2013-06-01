package Named is
   type A is new Short_Short_Integer range 1 .. 10;
   type Ar is array (A) of Integer;
   function L (X : Ar) return A
      with Post => (X'Last < Ar'Last + 117);
   --  replace 117 by 118 to obtain a Constraint_Check Warning
end Named;
