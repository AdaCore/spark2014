package body Normalize
with SPARK_Mode
is

   function R1 (X : in T_Float32) return T_Float32
   is (T_Float32'Floor(X));

   function R2 (X : in T_Float32) return T_Float32
   is (T_Float32'Floor(X))
   with Pre => ( X >= T_Float32'First + 1.0 );

   function R3 (X : in T_Float32) return T_Float32
   is (T_Float32'Floor(X))
   with Pre => ( X >= T_Float32'First + 1.0 ),
   Post => R3'Result <= X and then R3'Result >= X - 1.0;

   function R4 (X : in T_Float32) return T_Float32
   is (T_Float32'Floor(X))
   with Pre => ( X >= T_Float32'First + 1.0 ),
   Post => R4'Result = T_Float32'Floor(X);

   ---------

   function M01 (X : in T1) return T2 is
   begin
      return T_Float32'Floor(X / C);
   end;

   function M02 (X : in T1) return T2 is
      V1 : T_Float32;
      V2 : T_Float32;
   begin
      V1 := X / C;
      V2 := T_Float32'Floor(V1);
      return V2;
   end;

   function M03 (X : in T1) return T2
   is
      V1 : T_Float32;
      V2 : T_Float32;
   begin
      V1 := X / C;
      pragma Assert (V1 in -2.0 .. 2.0);
      V2 := T_Float32'Floor(V1);
      pragma Assert (V2 <= V1);
      pragma Assert (V2 >= V1-1.0);
      return V2;
   end;

   ---------

   function M11 (X : in T1) return T2 is
   begin
      return R1(X / C);
   end;

   function M12 (X : in T1) return T2 is
      V1 : T_Float32;
      V2 : T_Float32;
   begin
      V1 := X / C;
      V2 := R1(V1);
      return V2;
   end;

   function M13 (X : in T1) return T2
   is
      V1 : T_Float32;
      V2 : T_Float32;
   begin
      V1 := X / C;
      pragma Assert (V1 in -2.0 .. 2.0);
      V2 := R1(V1);
      pragma Assert (V2 <= V1);
      pragma Assert (V2 >= V1-1.0);
      return V2;
   end;

   ---------

   function M21 (X : in T1) return T2 is
   begin
      return R2(X / C);
   end;

   function M22 (X : in T1) return T2 is
      V1 : T_Float32;
      V2 : T_Float32;
   begin
      V1 := X / C;
      V2 := R2(V1);
      return V2;
   end;

   function M23 (X : in T1) return T2
   is
      V1 : T_Float32;
      V2 : T_Float32;
   begin
      V1 := X / C;
      pragma Assert (V1 in -2.0 .. 2.0);
      V2 := R2(V1);
      pragma Assert (V2 <= V1);
      pragma Assert (V2 >= V1-1.0);
      return V2;
   end;

   ---------

   function M31 (X : in T1) return T2 is
   begin
      return R3(X / C);
   end;

   function M32 (X : in T1) return T2 is
      V1 : T_Float32;
      V2 : T_Float32;
   begin
      V1 := X / C;
      V2 := R3(V1);
      return V2;
   end;

   function M33 (X : in T1) return T2
   is
      V1 : T_Float32;
      V2 : T_Float32;
   begin
      V1 := X / C;
      pragma Assert (V1 in -2.0 .. 2.0);
      V2 := R3(V1);
      pragma Assert (V2 <= V1);
      pragma Assert (V2 >= V1-1.0);
      return V2;
   end;

   ---------

   function M41 (X : in T1) return T2 is
   begin
      return R4(X / C);
   end;

   function M42 (X : in T1) return T2 is
      V1 : T_Float32;
      V2 : T_Float32;
   begin
      V1 := X / C;
      V2 := R4(V1);
      return V2;
   end;

   function M43 (X : in T1) return T2
   is
      V1 : T_Float32;
      V2 : T_Float32;
   begin
      V1 := X / C;
      pragma Assert (V1 in -2.0 .. 2.0);
      V2 := R4(V1);
      pragma Assert (V2 <= V1);
      pragma Assert (V2 >= V1-1.0);
      return V2;
   end;

   ---------

end Normalize;
