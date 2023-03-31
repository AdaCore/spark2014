package Illegal_Uses_Of_Exc_Cases with SPARK_Mode is

   function F return Integer with
     Import,
     Global => null,
     Exceptional_Cases => (Constraint_Error => True);

   type Root is tagged null record;

   procedure Dispatching_Op (X : Root) with
     Exceptional_Cases => (Constraint_Error => True);

   procedure P with
     Import,
     Global => null,
     Exceptional_Cases => (others => True);

   V : not null access procedure := P'Access;

end Illegal_Uses_Of_Exc_Cases;
