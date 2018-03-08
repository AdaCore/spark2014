package Rec is
   type T is record
      A : Integer;
      B : Integer;
      C : Integer;
   end record;

   O1 : T := (A => 0, others => <>);
   O2 : T := (A => 0, B => 0, others => <>);

   type T2 is record
      D : Integer := 0;
      E : Integer;
   end record;

   O3 : T2 := (others => <>);
   O4 : T2 := (E => 3, others => <>);
end Rec;
