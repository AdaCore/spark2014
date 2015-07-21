package body Dynamic_Preds_Array
  with SPARK_Mode
is
   procedure Init_Even (X : in out Integer) is
   begin
      X := 2;
   end Init_Even;

   procedure Init_OK_Even (X : in out Integer) is
   begin
      X := 2;
   end Init_OK_Even;

   procedure Call_Init_Even (X : in out Even) is
   begin
      Init_Even (X);  --  @PREDICATE_CHECK:FAIL
      Init_OK_Even (X);  --  @PREDICATE_CHECK:PASS
   end Call_Init_Even;

   procedure Call2_Init_Even (X : in out Integer) is
   begin
      Call_Init_Even (X);  --  @PREDICATE_CHECK:PASS
      Call_Init_Even (X);  --  @PREDICATE_CHECK:PASS
   end Call2_Init_Even;

   procedure Call3_Init_Even (X : in out Even_Pair) is
   begin
      Init_Even (X(1));  --  @PREDICATE_CHECK:FAIL
      Init_OK_Even (X(2));  --  @PREDICATE_CHECK:PASS
   end Call3_Init_Even;

   procedure Call4_Init_Even (X : in out Ext_Even_Pair) is
   begin
      Init_Even (X(1));  --  @PREDICATE_CHECK:FAIL
      Init_OK_Even (X(2));  --  @PREDICATE_CHECK:PASS
   end Call4_Init_Even;


   procedure Init_Even_Pair (X : out Even_Pair; A, B : Integer) is
      Tmp : Even_Pair := (A, B);   --  @PREDICATE_CHECK:FAIL
   begin
      X := Tmp;
   end Init_Even_Pair;

   procedure Init_Constant_Even_Pair (X : out Even_Pair) is
      Tmp : Even_Pair := (0, 2);   --  @PREDICATE_CHECK:PASS
   begin
      X := Tmp;
   end Init_Constant_Even_Pair;

   procedure Init_Even_Close_Pair (X : out Even_Close_Pair) is
      Tmp : Even_Close_Pair := Get_Constant_Even_Pair;   --  @PREDICATE_CHECK:FAIL
   begin
      X := Tmp;
   end Init_Even_Close_Pair;

   function Get_Even_Pair (A, B : Integer) return Even_Pair is
      Result : Even_Pair;
   begin
      Result(1) := A;  --  @PREDICATE_CHECK:PASS
      Result(2) := B;  --  @PREDICATE_CHECK:FAIL

      return Result;
   end Get_Even_Pair;

   function Get_OK_Even_Pair (A, B : Even) return Even_Pair is
      Result : Even_Pair;
   begin
      Result(1) := A;  --  @PREDICATE_CHECK:NONE
      Result(2) := B;  --  @PREDICATE_CHECK:NONE

      return Result;
   end Get_OK_Even_Pair;

   function Get_Constant_Even_Pair return Even_Pair is
      Result : Even_Pair;
   begin
      Result(1) := 0;  --  @PREDICATE_CHECK:PASS
      Result(2) := 0;  --  @PREDICATE_CHECK:PASS

      return Result;
   end Get_Constant_Even_Pair;

   function Get_Even_Close_Pair (Above : Integer) return Even_Close_Pair is
      Result : Even_Pair;
   begin
      if Above mod 2 = 0 then
         Result(1) := Above;  --  @PREDICATE_CHECK:PASS
      else
         Result(1) := Above + 1;  --  @PREDICATE_CHECK:PASS
      end if;

      Result(2) := Result(1) + 2;  --  @PREDICATE_CHECK:PASS

      return Result;  --  @PREDICATE_CHECK:PASS
   end Get_Even_Close_Pair;

   function Get_Even_Close_Pair_Error (Above : Integer) return Even_Close_Pair is
      Result : Even_Pair := Get_Constant_Even_Pair;
   begin
      if Above mod 2 = 0 then
         Result(1) := Above + 1;  --  @PREDICATE_CHECK:FAIL
      else
         Result(1) := Above + 1;  --  @PREDICATE_CHECK:PASS
      end if;

      Result(2) := Result(1) + 4;  --  @PREDICATE_CHECK:PASS

      return Result;  --  @PREDICATE_CHECK:FAIL
   end Get_Even_Close_Pair_Error;

   function Get_Even_Close_Pair_Wrong (Above : Integer) return Even_Close_Pair is
      Result : Even_Close_Pair;
   begin
      if Above mod 2 = 0 then
         Result(1) := Above;  --  @PREDICATE_CHECK:FAIL
      else
         Result(1) := Above + 1;  --  @PREDICATE_CHECK:FAIL
      end if;

      Result(2) := Result(1) + 2;  --  @PREDICATE_CHECK:PASS

      return Result;
   end Get_Even_Close_Pair_Wrong;

   procedure Update_Even_Pair (X : in out Even_Pair; A, B : Integer) is
   begin
      X(1) := A;  --  @PREDICATE_CHECK:FAIL
      X(2) := B;  --  @PREDICATE_CHECK:FAIL
   end Update_Even_Pair;

   procedure Update_Constant_Even_Pair (X : in out Even_Pair) is
   begin
      X(1) := 0;  --  @PREDICATE_CHECK:PASS
      X(2) := 2;  --  @PREDICATE_CHECK:PASS
   end Update_Constant_Even_Pair;

   procedure Update_Even_Close_Pair (X : in out Even_Close_Pair) is
   begin
      Update_Even_Pair (X, 0, 2);  --  @PREDICATE_CHECK:FAIL
      Update_Constant_Even_Pair (X);  --  @PREDICATE_CHECK:PASS
   end Update_Even_Close_Pair;

   function Get_Even_Close_Pair (X : Even_Close_Pair) return Even_Close_Pair is
   begin
      return X;  --  @PREDICATE_CHECK:NONE
   end Get_Even_Close_Pair;

   procedure Update_Bad_Even_Pair (X : in out Even_Pair) is
   begin
      Update_Even_Close_Pair (X);  --  @PREDICATE_CHECK:FAIL
      Update_Even_Close_Pair (X);  --  @PREDICATE_CHECK:PASS
   end Update_Bad_Even_Pair;

   procedure Update_Bad2_Even_Pair (X : in out Even_Pair) is
   begin
      X := Get_Even_Close_Pair (X);  --  @PREDICATE_CHECK:FAIL
      X := Get_Even_Close_Pair (X);  --  @PREDICATE_CHECK:PASS
   end Update_Bad2_Even_Pair;

end Dynamic_Preds_Array;
