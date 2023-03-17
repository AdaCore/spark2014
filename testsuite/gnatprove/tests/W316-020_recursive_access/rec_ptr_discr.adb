procedure Rec_Ptr_Discr with SPARK_Mode is
   function Id (I : Integer) return Integer is (I);

   type R1(D1 : INTEGER);
   type R2(D2 : INTEGER);
   type R3(D3 : POSITIVE);

   type ACC_R1 is access R1;
   type ACC_R2 is access R2;
   type ACC_R3 is access R3;

   type R1(D1 : INTEGER) is
      record
         C1 : ACC_R2(D1);
      end record;

   type R2(D2 : INTEGER) is
      record
         C2 : ACC_R3(D2);
      end record;

   type R3(D3 : POSITIVE) is
      record
         C3 : ACC_R1(D3);
      end record;

   X1 : ACC_R1(ID(0));

begin

   X1 := new R1'(D1 => ID(0),
                 C1 => new R2'(D2 => ID(0),
                               C2 => new R3(ID(0)))); --@RANGE_CHECK:FAIL

end Rec_Ptr_Discr;
