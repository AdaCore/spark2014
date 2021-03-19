with System.Aux_DEC; use System.Aux_DEC;

procedure Test_Overlays with SPARK_Mode is
   type My_Int is new Integer with Default_Value => 0;

   C1 : constant Integer := 10;
   C2 : constant Integer with  --  OK
     Import,
     Address => C1'Address;
   C3 : constant Integer := 14 with  --  Rejected
     Address => C1'Address;
   C4 : constant Integer with  --  Warning about writes to C4 only
     Import,
     Address => To_Address (12);
   C5 : constant Integer := 14 with  --  Warning about writes to C5 and effects of init
     Address => To_Address (12);

   V1 : Integer := 10;
   V2 : Integer with
     Import,
     Address => V1'Address;  --  OK
   V3 : Integer := 14 with
     Address => V1'Address;  --  OK
   V4 : My_Int with
     Address => V1'Address;  --  OK
   V5 : Integer with
     Address => V1'Address;  --  Rejected
   V6 : Integer with --  Warning about writes to C5 and ignored effects
     Import,
     Address => To_Address (12);
   V7 : Integer := 14 with --  Warning about writes to C5 and ignored effects
     Address => To_Address (12);
begin
   null;
end Test_Overlays;
