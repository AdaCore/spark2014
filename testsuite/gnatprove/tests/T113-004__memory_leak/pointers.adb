pragma SPARK_Mode;
with Ada.Unchecked_Deallocation;

procedure Pointers is

   type T is access Integer;

   procedure Dealloc is new Ada.Unchecked_Deallocation (Integer, T);

   procedure Assign (X : out T; B : Boolean := False)
     with Post => X /= null and X.all = 2
   is
   begin
      X := new Integer'(2);  -- @MEMORY_LEAK:PASS
      if B then
         Assign (X, False);
      end if;
   end Assign;

   X : T;  -- @MEMORY_LEAK:PASS
   Y : T;  -- @MEMORY_LEAK:FAIL
   Z : T;  -- @MEMORY_LEAK:PASS

   type Arr is array (1 .. 3) of T;

   XX : Arr;  -- @MEMORY_LEAK:PASS
   YY : Arr;  -- @MEMORY_LEAK:FAIL
   ZZ : Arr;  -- @MEMORY_LEAK:FAIL

   type Unc_Arr is array (Positive range <>) of T;

   procedure Assign (X : in out Unc_Arr)
     with Post => True
   is
      Loc : Unc_Arr(X'Range);  -- @MEMORY_LEAK:PASS
   begin
      X := Loc;  -- @MEMORY_LEAK:FAIL
   end Assign;

begin
   X := new Integer'(1);  -- @MEMORY_LEAK:PASS
   Dealloc (X);
   X := null;  --  workaround until deallocation handled

   Y := new Integer'(1);  -- @MEMORY_LEAK:PASS
   Z := new Integer'(1);  -- @MEMORY_LEAK:PASS

   Y := Z;  -- @MEMORY_LEAK:FAIL

   XX(1) := new Integer'(1);  -- @MEMORY_LEAK:PASS
   YY := XX;
   ZZ(2) := new Integer'(1);  -- @MEMORY_LEAK:PASS

   declare
      X : T;  -- @MEMORY_LEAK:PASS
      Y : T;  -- @MEMORY_LEAK:FAIL
      Z : T;  -- @MEMORY_LEAK:PASS

   begin
      X := new Integer'(1);  -- @MEMORY_LEAK:PASS
      Dealloc (X);
      X := null;  --  workaround until deallocation handled

      Y := new Integer'(1);  -- @MEMORY_LEAK:PASS
      Assign (Y);  -- @MEMORY_LEAK:FAIL

      Z := new Integer'(1);  -- @MEMORY_LEAK:PASS
      Y := Z;  -- @MEMORY_LEAK:FAIL
   end;

   declare
      type Point is record
         X, Y : T;
         Z : Integer;
      end record;

      type Line is record
         P, Q : Point;
      end record;

      type Dim (N : Integer := 1) is record
         case N is
            when 2 =>
               X, Y : T;
            when others =>
               null;
         end case;
      end record;

      type Mesh is record
         P : Dim; Q : Dim(2);
      end record;

      type Table is record
         A : Arr;
         B : Integer;
      end record;

      U : Point;  -- @MEMORY_LEAK:PASS
      V : Point;  -- @MEMORY_LEAK:FAIL
      W : Point;  -- @MEMORY_LEAK:FAIL

      A : Line;
      B : Line;

      E : Dim;
      F : Dim(3);

      H : Mesh;
      K : Mesh;

      R : Table;  -- @MEMORY_LEAK:PASS
      S : Table;  -- @MEMORY_LEAK:FAIL

      procedure Assign (U : out Point)
        with Post => True
      is
      begin
         U.X := new Integer'(2);  -- @MEMORY_LEAK:PASS
         U.Y := new Integer'(2);  -- @MEMORY_LEAK:PASS
         U.Z := 2;
      end Assign;

      function Alloc return T with Volatile_Function is
         Result : T := new Integer'(1);  -- @MEMORY_LEAK:PASS
      begin
         return Result;
      end Alloc;

   begin
      U.X := new Integer'(1);  -- @MEMORY_LEAK:PASS
      U.Y := U.X;  -- @MEMORY_LEAK:PASS
      U.X := null;  -- @MEMORY_LEAK:PASS
      U.Y := null;  -- @MEMORY_LEAK:FAIL

      V.X := Alloc;
      V.Y := new Integer'(1);  -- @MEMORY_LEAK:PASS
      Assign (V);  -- @MEMORY_LEAK:FAIL

      Assign (W.X);  -- @MEMORY_LEAK:PASS
      Assign (W.Y);  -- @MEMORY_LEAK:PASS
      W.Z := 42;
      V := W;  -- @MEMORY_LEAK:FAIL
      pragma Assert (W.Z = 42);  -- @ASSERT:PASS
      pragma Assert (V.Z = 42);  -- @ASSERT:PASS
      Assign (W);  -- @MEMORY_LEAK:PASS

      A.P := A.Q;  -- @MEMORY_LEAK:PASS
      A.Q := (null, null, 0);
      B := A;  -- @MEMORY_LEAK:PASS

      E := F;  -- @MEMORY_LEAK:PASS
      F := E;  -- @MEMORY_LEAK:NONE

      H.P := H.Q;  -- @MEMORY_LEAK:PASS
      H.Q := Dim'(2, null, null);
      K := H;  -- @MEMORY_LEAK:PASS

      R.A(1) := new Integer'(0);  -- @MEMORY_LEAK:PASS
      S.A := R.A;  -- @MEMORY_LEAK:PASS
   end;

end Pointers;
