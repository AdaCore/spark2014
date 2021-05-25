procedure Relaxed with SPARK_Mode is
   type U is record
      X : Integer := 0;
   end record with Relaxed_Initialization;

   procedure Inner (V : U) with Global => null is
      type R is record
         X : U := V; --@INIT_BY_PROOF:NONE
      end record with Relaxed_Initialization;

      type P is access R;

      X : P := new R; --@MEMORY_LEAK:FAIL
   begin
      pragma Assert (X.X'Initialized); --@ASSERT:FAIL
   end;

   type I is new Integer with Relaxed_Initialization;

   procedure Inner (V : I) with Global => null is
      type R is record
         X : I := V; --@INIT_BY_PROOF:NONE
      end record with Relaxed_Initialization;

      type P is access R;

      X : P := new R; --@MEMORY_LEAK:FAIL
   begin
      pragma Assert (X.X'Initialized); --@ASSERT:PASS
   end;

   type K is record
      X : Integer := 0;
   end record;

   procedure Inner_1 (V : K)  with Global => null, Relaxed_Initialization => V is
      type R is record
         X : K := V; --  For now we have an init check here. We could consider not
                     --  having it since X has relaxed init, but then the assert
                     --  should fail.
      end record;

      X : R with Relaxed_Initialization;
   begin
      pragma Assert (X'Initialized);
   end;

   procedure Inner_2 (V : K)  with Global => null, Relaxed_Initialization => V is
      type R is record
         X : K := V; --  @INIT_BY_PROOF:FAIL
      end record;

      X : R;
   begin
      null;
   end;

   procedure Inner_3 (V : K) with Global => null is
      type R is record
         X : K := V;
      end record;

      X : R with Relaxed_Initialization;
   begin
      pragma Assert (X'Initialized); --@ASSERT:PASS
   end;
begin
   null;
end;
