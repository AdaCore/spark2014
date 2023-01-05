procedure Test_Scalar_Preds with SPARK_Mode is
   function Rand (X : Integer) return Boolean with
     Import,
     Global => null,
     Annotate => (GNATprove, Always_Return);

   function F (X : Integer) return Boolean with
     Import,
     Global => null,
     Annotate => (GNATprove, Always_Return),
     Post => (if X = 0 then F'Result);

   type T1 is new Integer with
     Relaxed_Initialization,
     Predicate => F (Integer (T1));

   type H1 is record
      C : T1;
   end record;

   --  X is a scalar + has a predicate, even with Relaxed_Initialization on the
   --  type, the object is initialized and predicate holds.

   procedure Read (X : T1) with
     Global => null
   is
   begin
      pragma Assert (F (Integer (X)));
   end Read;

   --  X is a scalar + has a predicate, even with Relaxed_Initialization on the
   --  type, out parameters have to be initialized.

   procedure Write (X : out T1) with  --@INIT_BY_PROOF:FAIL
     Global => null
   is
   begin
      if Rand (0) then
         X := 0;
      end if;
   end Write;

   --  X is a record annotated with Relaxed_Initialization, it might not be
   --  initialized.

   procedure No_Read (X : H1) with
     Relaxed_Initialization => X,
     Global => null
   is
   begin
      pragma Assert (F (Integer (X.C)));  --@ASSERT:FAIL
   end No_Read;

   --  X is a record annotated with Relaxed_Initialization, there is no init
   --  check.

   procedure No_Write (X : out H1) with
     Relaxed_Initialization => X,
     Global => null
   is
   begin
      if Rand (0) then
         X.C := 0;
      end if;
   end No_Write;

   --  The component C of X is annotated with Relaxed_Initialization, it might
   --  not be initialized.

   procedure Read (X : H1) with
     Global => null
   is
   begin
      pragma Assert (F (Integer (X.C)));  --@ASSERT:FAIL
   end Read;

   procedure Write (X : out H1) with
     Global => null
   is
   begin
      if Rand (0) then
         X.C := 0;
      end if;
   end Write;

   --  X.C is initialized

   procedure Read_Init (X : H1) with
     Global => null,
     Pre => X.C'Initialized
   is
   begin
      pragma Assert (F (Integer (X.C)));
   end Read_Init;

   procedure Write_Init (X : out H1) with
     Global => null,
     Post => X.C'Initialized --@POSTCONDITION:FAIL
   is
   begin
      if Rand (0) then
         X.C := 0;
      end if;
   end Write_Init;

   type T2 is new Integer with
     Default_Value => 0,
     Relaxed_Initialization,
     Predicate => F (Integer (T2));

   type H2 is record
      C : T2;
   end record;

   type I2 is record
      C : T2 := 1; --@PREDICATE_CHECK:FAIL
   end record;

   --  X is a scalar + has a predicate, even with Relaxed_Initialization on the
   --  type, the object is initialized and predicate holds.

   procedure Read (X : T2) with
     Global => null
   is
   begin
      pragma Assert (F (Integer (X)));
   end Read;

   --  X is a scalar + has a predicate, even with Relaxed_Initialization on the
   --  type, out parameters have to be initialized.

   procedure Write (X : out T2) with  --@INIT_BY_PROOF:FAIL
     Global => null
   is
   begin
      if Rand (0) then
         X := 0;
      end if;
   end Write;

   --  X is a record annotated with Relaxed_Initialization, it might not be
   --  initialized.

   procedure No_Read (X : H2) with
     Relaxed_Initialization => X,
     Global => null
   is
   begin
      pragma Assert (F (Integer (X.C)));  --@ASSERT:FAIL
   end No_Read;

   --  The component C of X is annotated with Relaxed_Initialization, it might
   --  not be initialized.

   procedure Read (X : H2) with
     Global => null
   is
   begin
      pragma Assert (F (Integer (X.C)));  --@ASSERT:FAIL
   end Read;

   --  X.C is initialized

   procedure Read_Init (X : H2) with
     Global => null,
     Pre => X.C'Initialized
   is
   begin
      pragma Assert (F (Integer (X.C)));
   end Read_Init;

   type T3 is new Integer with
     Default_Value => 2,
     Relaxed_Initialization,
     Predicate => F (Integer (T3));

   type H3 is record
      C : T3; --@PREDICATE_CHECK:FAIL
   end record;

   type I3 is record
      C : T3 := 0;
   end record;

   --  X is a scalar + has a predicate, even with Relaxed_Initialization on the
   --  type, the object is initialized and predicate holds.

   procedure Read (X : T3) with
     Global => null
   is
   begin
      pragma Assert (F (Integer (X)));
   end Read;

   --  X is a scalar + has a predicate, even with Relaxed_Initialization on the
   --  type, out parameters have to be initialized.

   procedure Write (X : out T3) with  --@INIT_BY_PROOF:FAIL
     Global => null
   is
   begin
      if Rand (0) then
         X := 0;
      end if;
   end Write;

   --  X is a record annotated with Relaxed_Initialization, it might not be
   --  initialized.

   procedure No_Read (X : I3) with
     Relaxed_Initialization => X,
     Global => null
   is
   begin
      pragma Assert (F (Integer (X.C)));  --@ASSERT:FAIL
   end No_Read;

   --  X.C is initialized

   procedure Read_Init (X : I3) with
     Global => null,
     Pre => X.C'Initialized
   is
   begin
      pragma Assert (F (Integer (X.C)));
   end Read_Init;

   --  The component C of X is annotated with Relaxed_Initialization, it might
   --  not be initialized.

   procedure Read (X : I3) with
     Global => null
   is
   begin
      pragma Assert (F (Integer (X.C)));  --@ASSERT:FAIL
   end Read;

   type T4 is new Integer with
     Predicate => F (Integer (T4));

   type H4 is record
      C : T4;
   end record;

   procedure Read (X : T4) with
     Global => null
   is
   begin
      pragma Assert (F (Integer (X)));
   end Read;

   procedure Write (X : out T4) with
     Global => null
   is
   begin
      X := 0;
   end Write;

   --  X is a record annotated with Relaxed_Initialization, it might not be
   --  initialized.

   procedure No_Read (X : H4) with
     Relaxed_Initialization => X,
     Global => null
   is
   begin
      pragma Assert (F (Integer (X.C)));  --@ASSERT:FAIL
   end No_Read;

   --  X is a record annotated with Relaxed_Initialization, there is no init
   --  check.

   procedure No_Write (X : out H4) with
     Relaxed_Initialization => X,
     Global => null
   is
   begin
      if Rand (0) then
         X.C := 0;
      end if;
   end No_Write;

   procedure Read (X : H4) with
     Global => null
   is
   begin
      pragma Assert (F (Integer (X.C)));
   end Read;

   procedure Write (X : out H4) with
     Global => null
   is
   begin
      if Rand (0) then
         X.C := 0;
      end if;
   end Write;

   type T5 is new Integer with
     Default_Value => 0,
     Predicate => F (Integer (T5));

   type H5 is record
      C : T5;
   end record;

   type I5 is record
      C : T5 := 3; --@PREDICATE_CHECK:FAIL
   end record;

   procedure Read (X : T5) with
     Global => null
   is
   begin
      pragma Assert (F (Integer (X)));
   end Read;

   procedure Write (X : out T5) with
     Global => null
   is
   begin
      X := 0;
   end Write;

   --  X is a record annotated with Relaxed_Initialization, it might not be
   --  initialized.

   procedure No_Read (X : H5) with
     Relaxed_Initialization => X,
     Global => null
   is
   begin
      pragma Assert (F (Integer (X.C)));  --@ASSERT:FAIL
   end No_Read;

   procedure Read (X : H5) with
     Global => null
   is
   begin
      pragma Assert (F (Integer (X.C)));
   end Read;

   type T6 is new Integer with
     Default_Value => 4,
     Predicate => F (Integer (T6));

   type H6 is record
      C : T6; --@PREDICATE_CHECK:FAIL
   end record;

   type I6 is record
      C : T6 := 0;
   end record;

   procedure Read (X : T6) with
     Global => null
   is
   begin
      pragma Assert (F (Integer (X)));
   end Read;

   procedure Write (X : out T6) with
     Global => null
   is
   begin
      X := 0;
   end Write;

   --  X is a record annotated with Relaxed_Initialization, it might not be
   --  initialized.

   procedure No_Read (X : I6) with
     Relaxed_Initialization => X,
     Global => null
   is
   begin
      pragma Assert (F (Integer (X.C)));  --@ASSERT:FAIL
   end No_Read;

   procedure Read (X : I6) with
     Global => null
   is
   begin
      pragma Assert (F (Integer (X.C)));
   end Read;

   procedure Test_Toplevel with
     Global => null
   is
      X1 : T1;
      X2 : T2;
      X3 : T3; --@PREDICATE_CHECK:FAIL
      X4 : T4 with Relaxed_Initialization;
      X5 : T5 with Relaxed_Initialization;
      X6 : T6 with Relaxed_Initialization; --@PREDICATE_CHECK:FAIL

   begin
      if Rand (0) then
         Read (X1); --@INIT_BY_PROOF:FAIL
      elsif Rand (1) then
         Read (X4); --@INIT_BY_PROOF:FAIL
      elsif Rand (2) then
         Read (X2);
      elsif Rand (3) then
         Read (X5);
      elsif Rand (4) then
         declare
            Y1 : T1 := 0;
            Y3 : T3 := 0;
            Y4 : T4 := 0 with Relaxed_Initialization;
            Y6 : T6 := 0 with Relaxed_Initialization;
         begin
            Read (Y1);
            Read (Y3);
            Read (Y4);
            Read (Y6);
         end;
      elsif Rand (5) then
         Write (X1);
         Read (X1);
      elsif Rand (6) then
         Write (X4);
         Read (X4);
      end if;
   end Test_Toplevel;

   procedure Test_Holder with
     Global => null
   is
      X1 : H1;
      X2 : H2;
      Y2 : I2; -- predicate fail on default value
      Y3 : H3; -- predicate fail on default value
      X3 : I3;
      X4 : H4 with Relaxed_Initialization;
      X5 : H5 with Relaxed_Initialization;
      Y5 : I5 with Relaxed_Initialization; -- predicate fail on default value
      Y6 : H6 with Relaxed_Initialization; -- predicate fail on default value
      X6 : I6 with Relaxed_Initialization;

   begin
      if Rand (0) then
         No_Read (X1);
         Read (X1);
         Read_Init (X1); --@PRECONDITION:FAIL
      elsif Rand (1) then
         No_Read (X2);
         Read (X2);
         Read_Init (X2); --@PRECONDITION:PASS
      elsif Rand (2) then
         No_Read (X3);
         Read (X3);
         Read_Init (X3); --@PRECONDITION:PASS
      elsif Rand (3) then
         No_Read (X4);
         Read (X4); --@INIT_BY_PROOF:FAIL
      elsif Rand (4) then
         No_Read (X5);
         Read (X5); --@INIT_BY_PROOF:PASS
      elsif Rand (5) then
         No_Read (X6);
         Read (X6); --@INIT_BY_PROOF:PASS
      elsif Rand (6) then
         X1.C := 12; --@PREDICATE_CHECK:FAIL
         Read_Init (X1); --@PRECONDITION:PASS
      elsif Rand (7) then
         X4.C := 12; --@PREDICATE_CHECK:FAIL
         Read (X4); --@INIT_BY_PROOF:PASS
      elsif Rand (8) then
         No_Write (X1);
         Read_Init (X1); --@PRECONDITION:FAIL
      elsif Rand (9) then
         Write (X1);
         Read_Init (X1); --@PRECONDITION:FAIL
      elsif Rand (10) then
         Write_Init (X1);
         Read_Init (X1); --@PRECONDITION:PASS
      elsif Rand (11) then
         No_Write (X4);
         Read (X4); --@INIT_BY_PROOF:FAIL
      elsif Rand (12) then
         Write (X4);
         Read (X4); --@INIT_BY_PROOF:PASS
      end if;
   end Test_Holder;

begin
   null;
end Test_Scalar_Preds;
