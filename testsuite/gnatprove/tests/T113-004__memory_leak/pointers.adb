pragma SPARK_Mode;
with Ada.Unchecked_Deallocation;

procedure Pointers is

   type T is access Integer;

   procedure Dealloc is new Ada.Unchecked_Deallocation (Integer, T);

   procedure Assign (X : out T; B : Boolean := False)
     with Post => X /= null and X.all = 2
   is
   begin
      X := new Integer'(2);  -- @RESOURCE_LEAK:PASS
      if B then
         Assign (X, False);
      end if;
   end Assign;

   X : T;  -- @RESOURCE_LEAK:PASS
   Y : T;  -- @RESOURCE_LEAK:FAIL
   Z : T;  -- @RESOURCE_LEAK:PASS

   type Arr is array (1 .. 3) of T;

   XX : Arr;  -- @RESOURCE_LEAK:PASS
   YY : Arr;  -- @RESOURCE_LEAK:FAIL
   ZZ : Arr;  -- @RESOURCE_LEAK:FAIL

   type Unc_Arr is array (Positive range <>) of T;

   procedure Assign (X : in out Unc_Arr)
     with Post => True
   is
      Loc : Unc_Arr(X'Range);  -- @RESOURCE_LEAK:PASS
   begin
      X := Loc;  -- @RESOURCE_LEAK:FAIL
   end Assign;

begin
   X := new Integer'(1);  -- @RESOURCE_LEAK:PASS
   Dealloc (X);
   X := null;  --  workaround until deallocation handled

   Y := new Integer'(1);  -- @RESOURCE_LEAK:PASS
   Z := new Integer'(1);  -- @RESOURCE_LEAK:PASS

   Y := Z;  -- @RESOURCE_LEAK:FAIL
   Y := Y;  -- @RESOURCE_LEAK:PASS

   XX(1) := new Integer'(1);  -- @RESOURCE_LEAK:PASS
   YY := XX;
   ZZ(2) := new Integer'(1);  -- @RESOURCE_LEAK:PASS

   declare
      X : T;  -- @RESOURCE_LEAK:PASS
      Y : T;  -- @RESOURCE_LEAK:FAIL
      Z : T;  -- @RESOURCE_LEAK:PASS

   begin
      X := new Integer'(1);  -- @RESOURCE_LEAK:PASS
      Dealloc (X);
      X := null;  --  workaround until deallocation handled

      Y := new Integer'(1);  -- @RESOURCE_LEAK:PASS
      Assign (Y);  -- @RESOURCE_LEAK:FAIL

      Z := new Integer'(1);  -- @RESOURCE_LEAK:PASS
      Y := Z;  -- @RESOURCE_LEAK:FAIL
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

      U : Point;  -- @RESOURCE_LEAK:PASS
      V : Point;  -- @RESOURCE_LEAK:FAIL
      W : Point;  -- @RESOURCE_LEAK:FAIL

      A : Line;
      B : Line;

      E : Dim;
      F : Dim(3);

      H : Mesh;
      K : Mesh;

      R : Table;  -- @RESOURCE_LEAK:PASS
      S : Table;  -- @RESOURCE_LEAK:FAIL

      procedure Assign (U : out Point)
        with Post => True
      is
      begin
         U.X := new Integer'(2);  -- @RESOURCE_LEAK:PASS
         U.Y := new Integer'(2);  -- @RESOURCE_LEAK:PASS
         U.Z := 2;
      end Assign;

      function Alloc return T is
         Result : T := new Integer'(1);  -- @RESOURCE_LEAK:PASS
      begin
         return Result;
      end Alloc;

   begin
      U.X := new Integer'(1);  -- @RESOURCE_LEAK:PASS
      U.Y := U.X;  -- @RESOURCE_LEAK:PASS
      U.Y := U.Y;  -- @RESOURCE_LEAK:PASS
      U.X := null;  -- @RESOURCE_LEAK:PASS
      U.Y := null;  -- @RESOURCE_LEAK:FAIL

      V.X := Alloc;
      V.Y := new Integer'(1);  -- @RESOURCE_LEAK:PASS
      Assign (V);  -- @RESOURCE_LEAK:FAIL

      Assign (W.X);  -- @RESOURCE_LEAK:PASS
      Assign (W.Y);  -- @RESOURCE_LEAK:PASS
      W.Z := 42;
      V := W;  -- @RESOURCE_LEAK:FAIL
      pragma Assert (W.Z = 42);  -- @ASSERT:PASS
      pragma Assert (V.Z = 42);  -- @ASSERT:PASS
      Assign (W);  -- @RESOURCE_LEAK:PASS

      A.P := A.Q;  -- @RESOURCE_LEAK:PASS
      A.Q := (null, null, 0);
      B := A;  -- @RESOURCE_LEAK:PASS

      E := F;  -- @RESOURCE_LEAK:PASS
      F := E;  -- @RESOURCE_LEAK:NONE

      H.P := H.Q;  -- @RESOURCE_LEAK:PASS
      H.Q := Dim'(2, null, null);
      K := H;  -- @RESOURCE_LEAK:PASS

      R.A(1) := new Integer'(0);  -- @RESOURCE_LEAK:PASS
      S.A := R.A;  -- @RESOURCE_LEAK:PASS
   end;

end Pointers;
