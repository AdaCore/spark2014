procedure Test_Function_Result with spark_mode is

   type R is record
      I : Positive;
   end record;

   function Read (I : Integer) return R with
     Global => null,
     Potentially_Invalid => Read'Result,
     Post => (if I > 0 then Read'Result'Valid_Scalars and then Read'Result.I = I),
     Import;

   function Read_P (I : Integer) return Positive with
     Import,
     Global => null,
     Potentially_Invalid => Read_P'Result,
     Post => (if I > 0 then Read_P'Result'Valid and then Read_P'Result = I);

   --  Test VC generation for potentially invalid function result

   procedure Test_VCs with Global => null is
      function F (X : Integer) return Boolean is (True);
      function Id_OK (X : R) return R with
        Potentially_Invalid => (X, Id_OK'Result),
        Post => F (Id_OK'Result.I);  --  @VALIDITY_CHECK:FAIL

      function Id_OK (X : R) return R is
      begin
         return X;
      end Id_OK;

      function Id_KO (X : R) return R with
        Global => null,
        Potentially_Invalid => X;

      function Id_KO (X : R) return R is
      begin
         return X;  --  @VALIDITY_CHECK:FAIL
      end Id_KO;

      function Id_Ext_OK (X : R) return R with
        Potentially_Invalid => (X, Id_Ext_OK'Result),
        Post => Id_Ext_OK'Result.I = 0;  --  Failed validity check expected when locally invalid objects are support

      function Id_Ext_OK (X : R) return R is
      begin
         return Y : R do  --  no check on return as Id_Ext_OK'Result might be invalid
            Y := X; --  Y is locally potentially invalid
         end return;
      end Id_Ext_OK;

      function Id_Ext_KO (X : R) return R with
        Global => null,
        Potentially_Invalid => X;

      function Id_Ext_KO (X : R) return R is
      begin
         return Y : R do  --  failed validity check on return
            Y := X; --  Y is locally potentially invalid
         end return;
      end Id_Ext_KO;

      function Id_Fun_OK (X : R) return R with
        Potentially_Invalid => (X, Id_Fun_OK'Result),
        Post => F (Id_Fun_OK'Result.I);  --  @VALIDITY_CHECK:FAIL

      function Id_Fun_OK (X : R) return R is (X);

      function F (X : R) return Boolean is (True);
      function Id_Fun_OK_2 (X : R) return R with
        Potentially_Invalid => (X, Id_Fun_OK_2'Result),
        Post => F (Id_Fun_OK_2'Result);  --  @VALIDITY_CHECK:FAIL

      function Id_Fun_OK_2 (X : R) return R is (X);

      function Id_Fun_KO (X : R) return R with
        Global => null,
        Potentially_Invalid => X;

      function Id_Fun_KO (X : R) return R is (X);  --  @VALIDITY_CHECK:FAIL
   begin
      null;
   end Test_VCs;

   --  Test contract generation for potentially invalid function result

   procedure Test_Contracts with Global => null is
      function Read_Post return R with
        Global => null,
        Potentially_Invalid => Read_Post'Result,
        Import,
        Post => Read_Post'Result'Valid_Scalars and then Read_Post'Result.I = 1;
      function Read_Expr_Fun_1 return R with
        Potentially_Invalid => Read_Expr_Fun_1'Result;
      function Read_Expr_Fun_1 return R is (I => 1);
      function Read_Expr_Fun_2 return R with
        Potentially_Invalid => Read_Expr_Fun_2'Result;
      function Read_Expr_Fun_2 return R is (Read (1));
      function Read_Expr_Fun_3 return R with
        Potentially_Invalid => Read_Expr_Fun_3'Result,
	Annotate => (GNATprove, Inline_For_Proof);
      function Read_Expr_Fun_3 return R is (Read (1));
      function Read_CC (B : Boolean) return R with
        Global => null,
        Potentially_Invalid => Read_CC'Result,
        Import,
        Contract_Cases =>
          (B => Read_CC'Result'Valid_Scalars and then Read_CC'Result.I = 1,
           others => True);

      C1 : R := Read_Post with Potentially_Invalid;
      C2 : R := Read_Expr_Fun_1 with Potentially_Invalid;
      C3 : R := Read_Expr_Fun_2 with Potentially_Invalid;
      C4 : R := Read_Expr_Fun_3 with Potentially_Invalid;
      C5 : R := Read_CC (True) with Potentially_Invalid;
      C6 : R := Read (0) with Potentially_Invalid;
   begin
      pragma Assert (C1.I = 1);
      pragma Assert (C2.I = 1);
      pragma Assert (C3.I = 1);
      pragma Assert (C4.I = 1);
      pragma Assert (C5.I = 1);
      pragma Assert (C6.I = 1); --   @VALIDITY_CHECK:FAIL
   end Test_Contracts;

   --  Test calls for potentially invalid function result

   procedure Test_Call with Global => null is
      procedure P1 (X : R; B : out Boolean) with
        Global => null,
        Always_Terminates,
        Potentially_Invalid => X,
        Post => B = X'Valid_Scalars,
        Import;
      procedure P2 (X : R) with
        Global => null,
        Always_Terminates,
        Import;

      procedure Test with Global => null is
         C1 : R := Read (1);
         B  : Boolean := Read (2)'Valid_Scalars;
         pragma Assert (B);
         C2 : R := Read (3) with Potentially_Invalid;
         pragma Assert (C2'Valid_Scalars);
	 I1 : Positive := Read_P (4);
	 I2 : Positive := Read_P (5) with Potentially_Invalid;
         pragma Assert (I2'Valid);

         procedure P_Old_1 (I : Positive) with
           Post => Read (I)'Old'Valid_Scalars;
         procedure P_Old_1 (I : Positive) is null;

         procedure P_Old_2 (I : Positive) with
           Post => Read (I)'Old.I = I;
         procedure P_Old_2 (I : Positive) is null;

         procedure P_Old_3 (I : Positive) with
           Post => Read_P (I)'Old'Valid;
         procedure P_Old_3 (I : Positive) is null;

         procedure P_Old_4 (I : Positive) with
           Post => Read_P (I)'Old = I;
         procedure P_Old_4 (I : Positive) is null;
      begin
         C1 := Read (6);
         C2 := Read (7);
         pragma Assert (C2'Valid_Scalars);
         I1 := Read_P (8);
         I2 := Read_P (9);
         pragma Assert (I2'Valid_Scalars);
         P1 (Read (10), B);
         pragma Assert (B);
         P2 (Read (11));
         P_Old_1 (12);
         P_Old_2 (13);
         P_Old_3 (14);
         P_Old_4 (15);
      end;

      procedure Test_Bad with Global => null is
         C1 : R := Read (0); --  @VALIDITY_CHECK:FAIL
         B  : Boolean := Read (-1)'Valid_Scalars;
         pragma Assert (B);  --  @ASSERT:FAIL
         C2 : R := Read (-2) with Potentially_Invalid;
         pragma Assert (C2'Valid_Scalars);  --  @ASSERT:FAIL
	 I1 : Positive := Read_P (-3); --  @VALIDITY_CHECK:FAIL
	 I2 : Positive := Read_P (-4) with Potentially_Invalid;
         pragma Assert (I2'Valid);  --  @ASSERT:FAIL

         procedure P_Old_1 (I : Integer) with
           Post => Read (I)'Old'Valid_Scalars;  --  @POSTCONDITION:FAIL
         procedure P_Old_1 (I : Integer) is null;

         procedure P_Old_2 (I : Integer) with
           Post => Read (I)'Old.I = I; --  @VALIDITY_CHECK:FAIL
         procedure P_Old_2 (I : Integer) is null;

         procedure P_Old_3 (I : Integer) with
           Post => Read_P (I)'Old'Valid;  --  @VALIDITY_CHECK:FAIL
         procedure P_Old_3 (I : Integer) is null;

         procedure P_Old_4 (I : Integer) with
           Post => (if I > 0 then Read_P (I)'Old = I); --   @VALIDITY_CHECK:PASS
         procedure P_Old_4 (I : Integer) is null;
      begin
         C1 := Read (-5); --  @VALIDITY_CHECK:FAIL
         C2 := Read (-6);
         pragma Assert (C2'Valid_Scalars);  --  @ASSERT:FAIL
         I1 := Read_P (-7); --  @VALIDITY_CHECK:FAIL
         I2 := Read_P (-8);
         pragma Assert (I2'Valid_Scalars);  --  @ASSERT:FAIL
         P1 (Read (-9), B);
         pragma Assert (B);  --  @ASSERT:FAIL
         P2 (Read (-10)); --  @VALIDITY_CHECK:FAIL
         P_Old_1 (-11);
         P_Old_2 (-12);
         P_Old_3 (-13);
         P_Old_4 (-14);
      end;
   begin
      null;
   end Test_Call;

begin
   null;
end;
