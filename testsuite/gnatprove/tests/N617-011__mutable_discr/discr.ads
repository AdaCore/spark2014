package Discr with SPARK_Mode is
   type No_Default   (C : Natural) is null record;
   type With_Default (C : Natural := 0) is null record;
   type Holder is record
      Content : With_Default;
   end record;

   procedure R1 (C : Natural);

   procedure R2 (C : Natural);

   procedure R3 (C : Natural);

   procedure R4 (C : Natural);

   procedure R5 (C : Natural);

   procedure R6 (C : Natural);

   procedure P1 (C : Natural);

   procedure P2 (C : Natural);

   procedure P3 (C : Natural);

   procedure P4 (C : Natural);

   procedure P5 (C : Natural);

end Discr;
