pragma SPARK_Mode;
with Ada.Unchecked_Deallocation;

procedure Dealloc is

   type T1 is access Integer;
   type T2 is access T1;
   type T3 is access T2;

   type R is record
      X : T1;
      Y : T2;
      Z : T3;
   end record;

   type R1 is access R;
   type R2 is access R1;
   type R3 is access R2;

   procedure Dealloc is new Ada.Unchecked_Deallocation (Integer, T1);
   procedure Dealloc is new Ada.Unchecked_Deallocation (T1, T2);
   procedure Dealloc is new Ada.Unchecked_Deallocation (T2, T3);

   procedure Dealloc is new Ada.Unchecked_Deallocation (R, R1);
   procedure Dealloc is new Ada.Unchecked_Deallocation (R1, R2);
   procedure Dealloc is new Ada.Unchecked_Deallocation (R2, R3);

begin
   --  correct deallocation

   declare
      A : T1 := new Integer'(42);
      B : T2 := new T1'(A);
      C : T3 := new T2'(B);
   begin
      A := new Integer'(41);
      B := new T1'(A);
      A := new Integer'(40);

      Dealloc (A);
      Dealloc (B.all);
      Dealloc (B);  -- @MEMORY_LEAK:PASS
      Dealloc (C.all.all);
      Dealloc (C.all);  -- @MEMORY_LEAK:PASS
      Dealloc (C);  -- @MEMORY_LEAK:PASS
   end;

   --  incorrect deallocation

   declare
      A : T1 := new Integer'(42);
      B : T2 := new T1'(A);
      C : T3 := new T2'(B);
   begin
      A := new Integer'(41);
      B := new T1'(A);
      A := new Integer'(40);

      Dealloc (B);  -- @MEMORY_LEAK:FAIL
      Dealloc (C.all.all);
      Dealloc (C);  -- @MEMORY_LEAK:FAIL
   end;

   --  correct deallocation

   declare
      A : T1 := new Integer'(42);
      B : T2 := new T1'(A);
      C : T3 := new T2'(B);
      D : R;
      E : R1;
      F : R2;
      G : R3;
   begin
      A := new Integer'(41);
      B := new T1'(A);
      A := new Integer'(40);
      D := (A, B, C);
      E := new R'(D);
      F := new R1'(E);
      G := new R2'(F);

      Dealloc (G.all.all.X);
      Dealloc (G.all.all.Y.all);
      Dealloc (G.all.all.Y);  -- @MEMORY_LEAK:PASS
      Dealloc (G.all.all.Z.all.all);
      Dealloc (G.all.all.Z.all);  -- @MEMORY_LEAK:PASS
      Dealloc (G.all.all.Z);  -- @MEMORY_LEAK:PASS
      Dealloc (G.all.all);  -- @MEMORY_LEAK:PASS
      Dealloc (G.all);  -- @MEMORY_LEAK:PASS
      Dealloc (G);  -- @MEMORY_LEAK:PASS
   end;

   --  incorrect deallocation

   declare
      A : T1 := new Integer'(42);
      B : T2 := new T1'(A);
      C : T3 := new T2'(B);
      D : R;
      E : R1;
      F : R2;
      G : R3;
   begin
      A := new Integer'(41);
      B := new T1'(A);
      A := new Integer'(40);
      D := (A, B, C);
      E := new R'(D);
      F := new R1'(E);
      G := new R2'(F);

      Dealloc (G.all.all.X);
      Dealloc (G.all.all.Y.all);
      Dealloc (G.all.all.Z.all.all);
      Dealloc (G.all.all.Z.all);  -- @MEMORY_LEAK:PASS
      Dealloc (G.all.all.Z);  -- @MEMORY_LEAK:PASS
      Dealloc (G.all.all);  -- @MEMORY_LEAK:FAIL
      Dealloc (G);  -- @MEMORY_LEAK:FAIL
   end;

end Dealloc;
