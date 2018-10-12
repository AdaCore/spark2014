procedure Init_Pred_In_Loop with SPARK_Mode is
   function My_False return Boolean is (False);

   type No_Init is record
      F1 : Integer;
      F2 : Integer;
   end record
     with Predicate => F1 /= 0 and F2 /= 0;

   procedure Test_No_Init_1 is
      X : No_Init;
   begin
      X := (1, 1);
      loop
         pragma Loop_Invariant (True);
         pragma Assert (X.F1 /= 0);
         --  This assertion should hold but we do not know that X is
         --  initialized before the loop so it is not assumed to be initialized
         --  in the implicit invariant.
         X.F1 := 1;
      end loop;
   end Test_No_Init_1;

   procedure Test_No_Init_2 is
      X : No_Init := (1, 1);
   begin
      loop
         pragma Loop_Invariant (True);
         pragma Assert (X.F1 /= 0);
         X.F1 := 1;
      end loop;
   end Test_No_Init_2;

   type Partial_Init is record
      F1 : Integer := 0;
      F2 : Integer;
   end record
     with Predicate => F1 = 0;

   procedure Test_Partial_Init_1 is
      X : Partial_Init;
   begin
      X.F2 := 1;
      loop
         pragma Loop_Invariant (True);
         pragma Assert (X.F1 = 0);
         X.F1 := 0;
      end loop;
   end Test_Partial_Init_1;

   procedure Test_Partial_Init_2 is
      X : Partial_Init := (0, 1);
   begin
      loop
         pragma Loop_Invariant (True);
         pragma Assert (X.F1 = 0);
         X.F1 := 0;
      end loop;
   end Test_Partial_Init_2;

   procedure Test_Partial_Init_3 is
      X : Partial_Init;
   begin
      loop
         pragma Loop_Invariant (True);
         pragma Assert (X.F1 = 0);
         X.F1 := 0;
      end loop;
   end Test_Partial_Init_3;

   type Full_Init is record
      F1 : Integer := 0;
      F2 : Integer := 0;
   end record
     with Predicate => F1 = 0 and F2 = 0;

   procedure Test_Full_Init_1 is
      X : Full_Init;
   begin
      loop
         pragma Loop_Invariant (True);
         pragma Assert (X.F1 = 0);
         X.F1 := 0;
      end loop;
   end Test_Full_Init_1;

   procedure Test_Full_Init_2 is
      X : Partial_Init := (0, 1);
   begin
      loop
         pragma Loop_Invariant (True);
         pragma Assert (X.F1 = 0);
         X.F1 := 0;
      end loop;
   end Test_Full_Init_2;

   type Wrong_No_Init is record
      F1 : Integer;
      F2 : Integer;
   end record
     with Predicate => My_False;

   procedure Test_Wrong_No_Init_1 is
      X : Wrong_No_Init;
   begin
      loop
         pragma Loop_Invariant (True);
         X := (1, 1); -- @PREDICATE_CHECK:FAIL
      end loop;
   end Test_Wrong_No_Init_1;

   procedure Test_Wrong_No_Init_2 is
   begin
      loop
         pragma Loop_Invariant (True);
         declare
            X : Wrong_No_Init;
         begin
            X := (1, 1); -- @PREDICATE_CHECK:FAIL
         end;
      end loop;
   end Test_Wrong_No_Init_2;

   type Wrong_Partial_Init is record
      F1 : Integer := 0;
      F2 : Integer;
   end record
     with Predicate => My_False; -- @PREDICATE_CHECK:FAIL

   procedure Test_Wrong_Partial_Init is
   begin
      loop
         pragma Loop_Invariant (True);
         declare
            X : Wrong_Partial_Init;
         begin
            X := (1, 1);
         end;
      end loop;
   end Test_Wrong_Partial_Init;

   type Wrong_Full_Init is record
      F1 : Integer := 0;
      F2 : Integer := 0;
   end record
     with Predicate => My_False; -- @PREDICATE_CHECK:FAIL

   procedure Test_Wrong_Full_Init is
   begin
      loop
         pragma Loop_Invariant (True);
         declare
            X : Wrong_Full_Init;
         begin
            X := (1, 1);
         end;
      end loop;
   end Test_Wrong_Full_Init;

   type Wrong_Scalar is new Integer
     with Predicate => My_False;

   procedure Test_Wrong_Scalar_1 is
   begin
      loop
         pragma Loop_Invariant (True);
         declare
            X : Wrong_Scalar;
         begin
            X := 1; -- @PREDICATE_CHECK:FAIL
         end;
      end loop;
   end Test_Wrong_Scalar_1;

   procedure Test_Wrong_Scalar_2 is
   begin
      loop
         declare
            X : Wrong_Scalar;
         begin
            pragma Loop_Invariant (True);
            X := 1; -- @PREDICATE_CHECK:FAIL
         end;
      end loop;
   end Test_Wrong_Scalar_2;

   procedure Test_Wrong_Scalar_3 is
   begin
      for I in 1 .. 3 loop
         declare
            X : Wrong_Scalar;
         begin
            X := 1; -- @PREDICATE_CHECK:FAIL
         end;
      end loop;
   end Test_Wrong_Scalar_3;

   type Wrong_Scalar_Def_1 is new Integer
     with Predicate => My_False, -- @PREDICATE_CHECK:FAIL
     Default_Value => 0;

   procedure Test_Wrong_Scalar_Def_1 is
   begin
      loop
         pragma Loop_Invariant (True);
         declare
            X : Wrong_Scalar_Def_1;
         begin
            X := 1;
         end;
      end loop;
   end Test_Wrong_Scalar_Def_1;

   type Wrong_Scalar_Def_2 is new Integer
     with Predicate => My_False, -- @PREDICATE_CHECK:FAIL
     Default_Value => 0;

   procedure Test_Wrong_Scalar_Def_2 is
   begin
      loop
         declare
            X : Wrong_Scalar_Def_2;
         begin
            pragma Loop_Invariant (True);
            X := 1;
         end;
      end loop;
   end Test_Wrong_Scalar_Def_2;

   type Wrong_Scalar_Def_3 is new Integer
     with Predicate => My_False, -- @PREDICATE_CHECK:FAIL
     Default_Value => 0;

   procedure Test_Wrong_Scalar_Def_3 is
   begin
      for I in 1 .. 3 loop
         declare
            X : Wrong_Scalar_Def_3;
         begin
            X := 1;
         end;
      end loop;
   end Test_Wrong_Scalar_Def_3;

   type Intp is new Integer with
     Default_Value => 0; -- predicate check might fail

   type Sub_Intp_Bad is new Intp with
     Predicate => Sub_Intp_Bad /= 0; -- predicate check might fail on default value

   X : Sub_Intp_Bad;
begin
   null;
end Init_Pred_In_Loop;
