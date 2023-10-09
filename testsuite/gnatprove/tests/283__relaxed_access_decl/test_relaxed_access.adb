procedure Test_Relaxed_Access with SPARK_Mode is

   --  Check that initialization wrappers and predicates are generated
   --  correctly:
   --   * on simple access types
   --   * on recursive structures
   --   * on recursive structures with discriminant constraints

   function Rand (X : Integer) return Boolean with
     Global => null,
     Import;

   type D is record
      A, B : Integer;
   end record;
   type T is access D;
   type RT is new T with Relaxed_Initialization;
   type R is record
      F : T;
   end record with Relaxed_Initialization;

   type List;
   type List_Access is access List;
   type List is record
      Value : T;
      Next  : List_Access;
   end record;

   type List_D (D : Integer);
   type List_D_Access is access List_D;
   type List_D (D : Integer) is record
      Value : T;
      Next  : List_D_Access (D);
   end record;

   U  : D with Relaxed_Initialization;

   X1 : RT;
   Y1 : R;
   Z1 : T with Relaxed_Initialization;
   X2 : RT := new D'(1, 2);
   Y2 : R := (F => new D'(1, 2));
   Z2 : T := new D'(1, 2) with Relaxed_Initialization;
   X3 : RT := new D'(U);
   Y3 : R := (F => new D'(U));
   Z3 : T := new D'(U) with Relaxed_Initialization;

   L1 : List_Access with Relaxed_Initialization;
   L2 : List with Relaxed_Initialization;
   L3 : List := (Value => new D'(U), Next => null) with Relaxed_Initialization;

   K1 : List_D_Access with Relaxed_Initialization;
   K2 : List_D (25) with Relaxed_Initialization;
   K3 : List_D := (D => 15, Value => new D'(U), Next => null) with Relaxed_Initialization;

begin
   if Rand (1) then
      pragma Assert (X1'Initialized);
   elsif Rand (2) then
      pragma Assert (Y1.F = null);
      pragma Assert (Y1'Initialized);
   elsif Rand (3) then
      pragma Assert (Z1'Initialized);
   elsif Rand (4) then
      pragma Assert (X2'Initialized);
   elsif Rand (5) then
      pragma Assert (Y2'Initialized);
   elsif Rand (6) then
      pragma Assert (Z2'Initialized);
   elsif Rand (7) then
      pragma Assert (X3'Initialized); --@ASSERT:FAIL
   elsif Rand (8) then
      pragma Assert (Y3'Initialized); --@ASSERT:FAIL
   elsif Rand (9) then
      pragma Assert (Z3'Initialized); --@ASSERT:FAIL
   elsif Rand (10) then
      pragma Assert (L1'Initialized);
   elsif Rand (11) then
      pragma Assert (L2'Initialized);
   elsif Rand (12) then
      pragma Assert (L3'Initialized); --@ASSERT:FAIL
   elsif Rand (13) then
      pragma Assert (K1'Initialized);
   elsif Rand (14) then
      pragma Assert (K2'Initialized);
   elsif Rand (15) then
      pragma Assert (K3'Initialized); --@ASSERT:FAIL
   end if;
end Test_Relaxed_Access;
