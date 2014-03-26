package VS
  with SPARK_Mode => On
is
   --  TN N325-022 Test cases for slices of volatile arrays.

   subtype I10 is Positive range 1 .. 10;
   subtype I4  is Positive range 1 .. 4;

   type UA is array (Positive range <>) of Integer;

   subtype A10 is UA (I10);
   subtype A4  is UA (I4);

   type A2 is array (I10) of A10;

   type VR is record
      F1 : Integer;
      F2 : A10;
   end record with Volatile;

   V1 : A10 with Volatile;

   V2 : A2 with Volatile;

   V3 : VR;

   -- CASES

   --   1. read of a 1-D array
   procedure T1 (A : out Integer)
     with Global => (In_Out => V1),
          Depends => ((A, V1) => V1);

   --   2. read of a 2-D array
   procedure T2 (A : out Integer)
     with Global => (In_Out => V2),
          Depends => ((A, V2) => V2);

   --   3. read of a 1-D array, nested inside a record
   procedure T3 (A : out Integer)
     with Global => (In_Out => V3),
          Depends => ((A, V3) => V3);

   --   4. write to a 1-D array
   procedure T4 (A : in Integer)
     with Global => (In_Out => V1),
          Depends => (V1 =>+ A);

   --   5. write to a 2-D array
   procedure T5 (A : in Integer)
     with Global => (In_Out => V2),
          Depends => (V2 =>+ A);

   --   6. write to a 1-D array, nested inside a record
   procedure T6 (A : in Integer)
     with Global => (In_Out => V3),
          Depends => (V3 =>+ A);

end VS;
