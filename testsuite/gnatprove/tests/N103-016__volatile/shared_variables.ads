package Shared_Variables
  with SPARK_Mode => On
is
   type T is new Integer
     with Volatile;  --  OK

   type Colour is (Red, Green, Blue)
     with Volatile;  --  OK

   S : Integer
     with Volatile;  --  OK

   type R is record
      F1 : Integer;
      F2 : Integer with Volatile;  --  illegal, SPARK RM C.6(1)
      F3 : Boolean;
   end record;

   type R2 is record
      F1 : Integer;
      F2 : T;                      --  illegal, SPARK RM C.6(2)
   end record;

   type R3 (D : Colour) is record  --  illegal, SPARK RM C.6(3)
      Intensity : Natural;
   end record;

   type R4 (D : Boolean) is record
      F1 : Integer;
   end record with Volatile;        --  illegal, SPARK RM C.6(4)

   type R5 (D : Boolean := False) is record
      F1 : Integer;
   end record;                      --  legal

   SV : R5 with Volatile;           --  illegal, SPARK RM C.6(4)

   type R6 is tagged record
      F1 : Integer;
   end record with Volatile;        --  illegal, SPARK RM C.6(5)

   type R7 is tagged record
      F1 : Integer;
   end record;                      --  legal

   SV2 : R7 with Volatile;          --  illegal, SPARK RM C.6(5)
end Shared_Variables;
