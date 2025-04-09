pragma Extensions_Allowed (All_Extensions);

procedure Nested_Private
 (I1, I2, I3, I4, I5, I6, I7, I8 : Integer;
  O1, O2, O3, O4, O5, O6, O7     : out Integer)
  with SPARK_Mode,
  Depends =>
    (O1 => (I1, I2),
     O2 => (I2, I3),
     O3 => I4,
     O4 => I5,
     O5 => (I6, I7),
     O6 => (I7, I8),
     O7 => I5)
  --  Imprecision is due to suboptimal handling of nested packages
is

   --  Test aggregates on private records from nested packages

   type V is tagged record
      F1 : Integer;
   end record;

   package Nested is
      type T is tagged private;
      type H1 is tagged private;
      type H2 is tagged record
         G : T;
      end record;
      C1 : constant T;
      C2 : constant T;
      C3 : constant H1;
      C4 : constant H1;
      C5 : constant H2;
      C6 : constant H2;
      C7 : constant V;
      function Get (X : T) return Integer with
        Global => null,
        Import;
      function Get (X : H1) return Integer with
        Global => null,
        Import;
      function Get (X : H2) return Integer with
        Global => null,
        Import;
   private
      type T is tagged record
         F1 : Integer;
         F2 : Integer;
      end record;
      C1 : constant T := (F1 => I1, F2 => I2);
      C2 : constant T := (C1  with delta F1 => I3);
      type H1 is tagged record
         G : V;
      end record;
      C3 : constant H1 := (G => (F1 => I4));
      C4 : constant H1 := (C3 with delta G.F1 =>I5);
      C5 : constant H2 := (G => (F1 => I6, F2 => I7));
      C6 : constant H2 := (C5 with delta G.F1 => I8);
      C7 : constant V := C4.G;
   end;
   use Nested;

   V1 : constant T := C1;
   V2 : constant T := C2;
   V3 : constant H1 := C3;
   V4 : constant H1 := C4;
   V5 : constant H2 := C5;
   V6 : constant H2 := C6;
   V7 : constant V := C7;
begin
   O1 := Get (V1);
   O2 := Get (V2);
   O3 := Get (V3);
   O4 := Get (V4);
   O5 := Get (V5);
   O6 := Get (V6);
   O7 := V7.F1;
end Nested_Private;
