procedure Test_Membership with SPARK_Mode is
   type Int_Array is array (Positive range <>) of Integer;
   subtype S1 is Int_Array (1 .. 5);
   subtype S2 is Int_Array (11 .. 15);
   subtype S3 is String (1 .. 5) with
     Predicate => S3 (1) = 'h';
   subtype S4 is String (1 .. 6) with
     Predicate => S4 (1) = 'h';
   type Acc is access Integer;
   subtype S5 is Acc with
     Predicate => S5 = null or else S5.all /= 0;
   type Acc_Id is access function (X : Integer) return Integer;
   subtype S6 is Acc_Id with
     Predicate => S6 = null or else (for all I in -100 .. 100 => S6 (I) = I);
   function Id (X : Integer) return Integer is (X);

   X : S1 := (others => 0);
begin
   pragma Assert (X not in S2);
   pragma Assert ("hello" in S3);
   pragma Assert ("hello" not in S4);
   pragma Assert (Acc'(new Integer'(0)) not in S5); --@MEMORY_LEAK:FAIL
   pragma Assert (Id'Access in S6);
end Test_Membership;
