procedure MinMax is
   X : Integer := 1;
   Y : Integer := 127;
   Min : Integer;
   Max : Integer;

   subtype S is Integer range 1 .. 127;

   type T is range 1 .. 127;

   V : T := 1;
   W : T := 127;
   MinT, MaxT : T;

   type E is (A, B, C, D);

   AA : E := A;
   CC : E := C;
   MinE, MaxE : E;

   procedure P_Integer (X, Y : Integer) with
     Global => (Output => (Min, Max)),
     Pre => X < Y;

   procedure P_Integer (X, Y : Integer) is
   begin
      Min := Integer'Min (X, Y);
      Max := Integer'Max (X, Y);
      pragma Assert (Min = X);
      pragma Assert (Max = Y);
   end P_Integer;

   procedure P_S (X, Y : S) with
     Global => (Output => (Min, Max)),
     Pre => X < Y;

   procedure P_S (X, Y : S) is
   begin
      Min := S'Min (X, Y);
      Max := S'Max (X, Y);
      pragma Assert (Min = X);
      pragma Assert (Max = Y);

      Min := S'Min (X, X + Y);
      Max := S'Max (X + Y, Y);
      pragma Assert (Min = X);
      pragma Assert (Max = X + Y);
   end P_S;

   procedure P_T (X, Y : T) with
     Global => (Output => (MinT, MaxT)),
     Pre => X < Y;

   procedure P_T (X, Y : T) is
   begin
      MinT := T'Min (X, Y);
      MaxT := T'Max (X, Y);
      pragma Assert (MinT = X);
      pragma Assert (MaxT = Y);

      --  certain overflow when adding V and W with GNAT, because the base type
      --  of T has range -128..127.

      MinT := T'Min (X, X + Y);
      MaxT := T'Max (X + Y, Y);
      pragma Assert (MinT = X);
      pragma Assert (MaxT = X + Y);
   end P_T;

   procedure P_E (X, Y : E) with
     Global => (Output => (MinE, MaxE)),
     Pre => X < Y;

   procedure P_E (X, Y : E) is
   begin
      MinE := E'Min (X, Y);
      MaxE := E'Max (X, Y);
      pragma Assert (MinE = X);
      pragma Assert (MaxE = Y);
   end P_E;

begin
   P_Integer (X, Y);
   P_S (X, Y);
   P_T (V, W);
   P_E (AA, CC);
end MinMax;
