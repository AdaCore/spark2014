procedure Test_Loop with SPARK_Mode is
   type Int_Array is array (Positive range <>) of Integer;
   type Int_Array_Acc is access Int_Array;

   procedure P (A : in out Int_Array; I : Integer) with Import;

   procedure Do_Something (A : in out Int_Array_Acc) with
     Pre  => A /= null,
     Post => A'First = A'First'Old;

   procedure Do_Something (A : in out Int_Array_Acc) is
   begin
      for I in 1 .. 100 loop
         P (A.all, I);
      end loop;
   end Do_Something;

   type R1 (B : Boolean) is record
      F : Integer;
   end record;
   type R1_Acc is access R1;

   procedure P (A : in out R1; I : Integer) with Import;

   procedure Do_Something (A : in out R1_Acc) with
     Pre  => A /= null,
     Post => A.B = A.B'Old;

   procedure Do_Something (A : in out R1_Acc) is
   begin
      for I in 1 .. 100 loop
         P (A.all, I);
      end loop;
   end Do_Something;

   type R2 (B : Boolean := False) is record
      F : Integer;
   end record;
   type R2_Acc is access R2;

   procedure P (A : in out R2; I : Integer) with Import;

   procedure Do_Something (A : in out R2_Acc) with
     Pre  => A /= null,
     Post => A.B = A.B'Old; --@POSTCONDITION:FAIL

   procedure Do_Something (A : in out R2_Acc) is
   begin
      for I in 1 .. 100 loop
         P (A.all, I);
      end loop;
   end Do_Something;
begin
   null;
end Test_Loop;
