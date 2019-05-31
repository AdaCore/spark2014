procedure Do_Loops with SPARK_Mode is
   type R is record
      F1 : Integer := 0;
      F2 : Integer := 0;
   end record;

   type U_Array is array (Positive range <>) of R;

   type U_Array_Acc is access U_Array;

   type R_Array_Record is record
      F3 : U_Array_Acc;
      F4 : U_Array_Acc;
   end record;

   type R_Array_Record_Acc is access R_Array_Record;

   procedure P (A : in out U_Array_Acc) with
     Pre  => A /= null,
     Post => A /= null and A'First = A'First'Old and A'Last = A'Last'Old
   is
   begin
      L : for I in A'Range loop
         A (I).F1 := 0;
      end loop L;
   end P;


   D : R_Array_Record_Acc := new R_Array_Record;
   A : U_Array_Acc := new U_Array (1 .. 100);
   B : U_Array_Acc := new U_Array (1 .. 100);
   C : U_Array_Acc := new U_Array (1 .. 100);
begin
   P (A);
   pragma Assert (A'First = 1);
   pragma Assert (A'Last = 100);
   D.F3 := B;
   D.F4 := C;
   L1 : for I in 1 .. 100 loop
      D.F3 (I).F1 := 0;
      pragma Assert (D.F3 (I).F2 = D.F3.all'Loop_Entry (I).F2);
      pragma Assert (D.F4.all = D.F4.all'Loop_Entry);
   end loop L1;

   L2 : for I in 1 .. 100 loop
      D.F3 (I).F1 := 0;
      D.F4 (I).F1 := 0;
      pragma Assert (D.F3 (I).F2 = D.F3.all'Loop_Entry (I).F2);
      pragma Assert (D.F4.all = D.F4.all'Loop_Entry);  --@ASSERT:FAIL
   end loop L2;

   L3 : for I in 1 .. 100 loop
      declare
         D_outer : R_Array_Record_Acc := new R_Array_Record;
         A       : U_Array_Acc := new U_Array (1 .. 100);
         B       : U_Array_Acc := new U_Array (1 .. 100);
      begin
         D_outer.F3 := A;
         D_outer.F4 := B;
         pragma Assert (D /= null); --@ASSERT:FAIL
         pragma Assert (D.F3 /= null); --@ASSERT:FAIL
         pragma Assert (D.F3'First = 1 and D.F3'Last = 100); --@ASSERT:FAIL
         pragma Assert (D.F4 /= null); --@ASSERT:FAIL
         pragma Assert (D.F4'First = 1 and D.F4'Last = 100); --@ASSERT:FAIL
         D.F3 (I).F1 := 0;
         D.F4 (I).F1 := 0;
         D := D_outer;
         pragma Assert (D.F3 (I).F1 = D.F3.all'Loop_Entry (I).F1); --@ASSERT:FAIL
         pragma Assert (D.F3 (I).F2 = D.F3.all'Loop_Entry (I).F2);
      end;
   end loop L3;

   L4 : for I in 1 .. 100 loop
      declare
         D_outer : R;
      begin
         D.F3 (I).F1 := 0;
         D.F4 (I).F1 := 0;
         if I > 1 then
            D.F3 (I - 1) := D_outer;
         end if;
         pragma Assert (D.F3 (I).F1 = D.F3.all'Loop_Entry (I).F1);
         pragma Assert (D.F3 (I).F2 = D.F3.all'Loop_Entry (I).F2); --@ASSERT:FAIL
      end;
   end loop L4;

   L5 : for I in 1 .. 100 loop
      L5_In : for J in 1 .. 100 loop
         if I = J then
            D.F3 (I).F1 := 0;
         end if;
      end loop L5_In;
      pragma Assert (D.F3 (I).F2 = D.F3.all'Loop_Entry (I).F2);
      pragma Assert (D.F4.all = D.F4.all'Loop_Entry);
   end loop L5;

   L6 : for I in 1 .. 100 loop
      declare
         D_outer : R_Array_Record;
         A       : U_Array_Acc := new U_Array (1 .. 100);
         B       : U_Array_Acc := new U_Array (1 .. 100);
      begin
         D_outer.F3 := A;
         D_outer.F4 := B;
         L6_In : for J in 1 .. 100 loop
            declare
               D_inner : R_Array_Record;
               A       : U_Array_Acc := new U_Array (1 .. 100);
               B       : U_Array_Acc := new U_Array (1 .. 100);
            begin
               D_inner.F3 := A;
               D_inner.F4 := B;
               if I = J then
                  D.F3 (I).F1 := 0;
                  D_inner.F3 (I).F1 := 0;
                  D_outer.F3 (I).F1 := 0;
               end if;
            end;
         end loop L6_In;
      end;
      pragma Assert (D.F3 (I).F2 = D.F3.all'Loop_Entry (I).F1); --@ASSERT:FAIL
      pragma Assert (D.F3 (I).F2 = D.F3.all'Loop_Entry (I).F2);
   end loop L6;

   L7 : for I in 1 .. 100 loop
      if I > 1 then
         declare
            D_outer : R;
         begin
            D.F3 (I).F1 := 0;
            D.F4 (I).F1 := 0;
            D.F3 (I - 1) := D_outer;
            D_outer := D.F4 (I);
         end;
      end if;
      pragma Assert (D.F3 (I).F1 = D.F3.all'Loop_Entry (I).F1); --@ASSERT:FAIL
      pragma Assert (D.F3 (I).F2 = D.F3.all'Loop_Entry (I).F2); --@ASSERT:FAIL
      pragma Assert (D.F4 (I).F2 = D.F4.all'Loop_Entry (I).F2);
   end loop L7;
end Do_Loops;
