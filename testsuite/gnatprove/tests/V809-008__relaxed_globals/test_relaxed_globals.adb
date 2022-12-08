procedure Test_Relaxed_Globals (C : Integer)
  with
    SPARK_Mode => On
is

   --  Test scalar global objects with predicates

   type T1 is new Integer with
     Relaxed_Initialization;
   subtype S1 is T1 with
     Predicate => Integer (S1) > C;

   G1 : S1;
   H1 : S1 := 1;

   --  G1 might not be initialized, but Get_G'Result has to be

   function Get_G return T1 is (G1) with -- @INIT_BY_PROOF:FAIL
     Global => (Input => G1, Proof_In => C),
     Post => Integer (Get_G'Result) > C;

   --  G1 is initialized

   function Get_G_Init return T1 is (G1) with -- @INIT_BY_PROOF:PASS
     Global => (Input => G1, Proof_In => C),
     Pre  => G1'Initialized,
     Post => Integer (Get_G_Init'Result) > C;

   --  H1 is a scalar, it cannot be uninitialized

   function Get_H return T1 is (H1) with -- @INIT_BY_PROOF:NONE
     Global => (Input => H1, Proof_In => C),
     Post => Integer (Get_H'Result) > C;

   --  G1 does not have to be written

   procedure Set_G1 with
     Global => (Output => G1, Input => C)
   is
   begin
      if C < 100 then
         G1 := 100;
      end if;
   end Set_G1;

   --  G1 does not have to be initialized on input

   procedure Set_G1_Init with
     Global => (In_Out => G1, Input => C),
     Post => Integer (G1) > C --@INIT_BY_PROOF:FAIL
   is
   begin
      if C < 100 then
         G1 := 100;
      end if;
   end Set_G1_Init;

   --  H1 is a scalar, it cannot be uninitialized

   procedure Set_H1_Init with
     Global => (In_Out => H1, Input => C),
     Post => Integer (H1) > C --@INIT_BY_PROOF:NONE
   is
   begin
      if C < 100 then
         H1 := 100;
      end if;
   end Set_H1_Init;

   --  Test record global objects with predicates that do not enforce
   --  initialization.

   type T2 is record
      F, G : Integer;
   end record with
     Relaxed_Initialization;
   subtype S2 is T2 with
     Predicate =>
       S2.F'Initialized and then S2.G'Initialized and then S2.F < S2.G;

   G2 : S2;
   H2 : S2 := (1, 2);

   --  G2 might not fullfill the predicate, but Get_G'Result has to

   function Get_G return T2 is (G2) with -- @PREDICATE_CHECK:FAIL
     Global => (Input => G2),
     Post => Get_G'Result.F < Get_G'Result.G;

   --  G2 is initialized

   function Get_G_Init return T2 is (G2) with -- @PREDICATE_CHECK:PASS
     Global => (Input => G2),
     Pre  => G2'Initialized,
     Post => Get_G_Init'Result.F < Get_G_Init'Result.G;

   --  H2 is has a predicate, it cannot be broken.
   --  ??? We do not maintain that currently.

   function Get_H return T2 is (H2) with
     Global => (Input => H2),
     Post => Get_H'Result.F < Get_H'Result.G;

   --  G2 does not have to be written

   procedure Set_G2 with
     Global => (Output => G2, Input => C)
   is
   begin
      if C < 100 then
         G2 := (1, 2);
      end if;
   end Set_G2;

   --  The predicate of G2 does not have to hold on input

   procedure Set_G2_Init with
     Global => (In_Out => G2, Input => C),
     Post => G2.F < G2.G --@PREDICATE_CHECK:FAIL
   is
   begin
      if C < 100 then
         G2 := (1, 2);
      end if;
   end Set_G2_Init;

   --  H2 is has a predicate, it cannot be broken.
   --  ??? We do not maintain that currently.

   procedure Set_H2_Init with
     Global => (In_Out => H2, Input => C),
     Post => H2.F < H2.G
   is
   begin
      if C < 100 then
         H2 := (1, 2);
      end if;
   end Set_H2_Init;

   --  Test record global objects with predicates that enforces initialization

   type T3 is record
      F, G : Integer;
   end record;
   subtype S3 is T3 with
     Predicate => S3.F < S3.G;

   G3 : S3 with Relaxed_Initialization;
   H3 : S3 := (1, 2) with Relaxed_Initialization;

   --  G2 might not fullfill the predicate, but Get_G'Result has to

   function Get_G return T3 is (G3) with -- @PREDICATE_CHECK:FAIL
     Global => (Input => G3),
     Post => Get_G'Result.F < Get_G'Result.G;

   --  G3 is initialized

   function Get_G_Init return T3 is (G3) with -- @PREDICATE_CHECK:PASS
     Global => (Input => G3),
     Pre  => G3'Initialized,
     Post => Get_G_Init'Result.F < Get_G_Init'Result.G;

   --  H3 is has a predicate, it cannot be broken.

   function Get_H return T3 is (H3) with
     Global => (Input => H3),
     Post => Get_H'Result.F < Get_H'Result.G;

   --  G3 does not have to be written

   procedure Set_G3 with
     Global => (Output => G3, Input => C)
   is
   begin
      if C < 100 then
         G3 := (1, 2);
      end if;
   end Set_G3;

   --  The predicate of G3 does not have to hold on input

   procedure Set_G3_Init with
     Global => (In_Out => G3, Input => C),
     Post => G3.F < G3.G --@PREDICATE_CHECK:FAIL
   is
   begin
      if C < 100 then
         G3 := (1, 2);
      end if;
   end Set_G3_Init;

   --  H3 is has a predicate, it cannot be broken

   procedure Set_H3_Init with
     Global => (In_Out => H3, Input => C),
     Post => H3.F < H3.G
   is
   begin
      if C < 100 then
         H3 := (1, 2);
      end if;
   end Set_H3_Init;
begin
   null;
end Test_Relaxed_Globals;
