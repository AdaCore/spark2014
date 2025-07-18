procedure Test_Assignment with SPARK_Mode is

   --  Test that assignments into view conversions are correctly handled

   procedure Public is
      type Root is tagged record
         C1, C2 : Integer;
      end record;

      type Child is new Root with record
         C3 : Integer;
      end record;

      procedure P1 (A, B, C : Integer; D, E, F : out Integer) with
        Depends => (D => B, E => C, F => C, null => A);

      procedure P1 (A, B, C : Integer; D, E, F : out Integer) is
         X : Child := (A, B, C);
         Y : Child := (B, C, A);
      begin
         Root (X) := Root (Y);
         D := X.C1;
         E := X.C2;
         F := X.C3;
      end P1;

      procedure P2 (A, B, C : Integer; D, E, F : out Integer) with
        Depends => (D => B, E => C, F => A);

      procedure P2 (A, B, C : Integer; D, E, F : out Integer) is
         X : Child := (A, B, C);
         Y : Child := (B, C, A);
      begin
         Root'Class (X) := Root'Class (Y);
         D := X.C1;
         E := X.C2;
         F := X.C3;
      end P2;

      procedure P3 (A, B, C : Integer; D, E, F : out Integer) with
        Depends => (D => B, E => C, F => C, null => A);

      procedure P3 (A, B, C : Integer; D, E, F : out Integer) is
         X : Root'Class := Child'(A, B, C);
         Y : Root'Class := Child'(B, C, A);
      begin
         Root (X) := Root (Y);
         D := X.C1;
         E := X.C2;
         F := Child (X).C3;
      end P3;

      procedure P4 (A, B, C : Integer; D, E, F : out Integer) with
        Depends => (D => B, E => C, F => A);

      procedure P4 (A, B, C : Integer; D, E, F : out Integer) is
         X : Root'Class := Child'(A, B, C);
         Y : Root'Class := Child'(B, C, A);
      begin
         X := Y;
         D := X.C1;
         E := X.C2;
         F := Child (X).C3;
      end P4;
   begin
      null;
   end;

   procedure Private_Root is
      package Nested is
         type Root is tagged private;
      private
         type Root is tagged record
            C1 : Integer;
         end record;
      end;
      use Nested;

      type Child is new Root with record
         C2 : Integer;
      end record;

      function Create (X : Integer) return Child with
        Global => null,
        Import;
      function Get (X : Root) return Integer with
        Global => null,
        Import;

      procedure P1 (A, B : Integer; D, E : out Integer) with
        Depends => (D => B, E => A);

      procedure P1 (A, B : Integer; D, E : out Integer) is
         X : Child := Create (A);
         Y : Child := Create (B);
      begin
         Root (X) := Root (Y);
         E := X.C2;
         D := Get (Root (X));
      end P1;

      procedure P2 (A, B : Integer; D, E : out Integer) with
        Depends => (D => B, E => B, null => A);

      procedure P2 (A, B : Integer; D, E : out Integer) is
         X : Child := Create (A);
         Y : Child := Create (B);
      begin
         Root'Class (X) := Root'Class (Y);
         E := X.C2;
         D := Get (Root (X));
      end P2;

      procedure P3 (A, B : Integer; D, E : out Integer) with
        Depends => (D => B, E => A);

      procedure P3 (A, B : Integer; D, E : out Integer) is
         X : Root'Class := Create (A);
         Y : Root'Class := Create (B);
      begin
         Root (X) := Root (Y);
         E := Child (X).C2;
         D := Get (Root (X));
      end P3;

      procedure P4 (A, B : Integer; D, E : out Integer) with
        Depends => (D => B, E => B, null => A);

      procedure P4 (A, B : Integer; D, E : out Integer) is
         X : Root'Class := Create (A);
         Y : Root'Class := Create (B);
      begin
         X := Y;
         E := Child (X).C2;
         D := Get (Root (X));
      end P4;
   begin
      null;
   end;

   procedure Private_Child is
      type Root is tagged record
         C1, C2 : Integer;
      end record;
      package Nested is
         type Child is new Root with private;
      private
         type Child is new Root with record
            C3 : Integer;
         end record;
      end;
      use Nested;

      function Create (X : Integer) return Child with
        Global => null,
        Import;
      function Get (X : Child) return Integer with
        Global => null,
        Import;

      procedure P1 (A, B, C : Integer; D, E, F : out Integer) with
        Depends => (D => B, E => C, F => (A, B, C));

      procedure P1 (A, B, C : Integer; D, E, F : out Integer) is
         X : Child := Create (A);
         Y : Child := Create (B);
      begin
         Y.C2 := C;
         Root (X) := Root (Y);
         D := X.C1;
         E := X.C2;
         F := Get (X);
      end P1;

      procedure P2 (A, B, C : Integer; D, E, F : out Integer) with
        Depends => (D => B, E => C, F => (B, C), null => A);

      procedure P2 (A, B, C : Integer; D, E, F : out Integer) is
         X : Child := Create (A);
         Y : Child := Create (B);
      begin
         Y.C2 := C;
         Root'Class (X) := Root'Class (Y);
         D := X.C1;
         E := X.C2;
         F := Get (X);
      end P2;

      procedure P3 (A, B, C : Integer; D, E, F : out Integer) with
        Depends => (D => B, E => C, F => (A, B, C));

      procedure P3 (A, B, C : Integer; D, E, F : out Integer) is
         X : Root'Class := Create (A);
         Y : Root'Class := Create (B);
      begin
         Y.C2 := C;
         Root (X) := Root (Y);
         D := X.C1;
         E := X.C2;
         F := Get (Child (X));
      end P3;

      procedure P4 (A, B, C : Integer; D, E, F : out Integer) with
        Depends => (D => B, E => C, F => (B, C), null => A);

      procedure P4 (A, B, C : Integer; D, E, F : out Integer) is
         X : Root'Class := Create (A);
         Y : Root'Class := Create (B);
      begin
         Y.C2 := C;
         X := Y;
         D := X.C1;
         E := X.C2;
         F := Get (Child (X));
      end P4;
   begin
      null;
   end;

   procedure Private_Private is
      package Nested1 is
         type Root is tagged private;
      private
         type Root is tagged record
            C1 : Integer;
         end record;
      end;
      use Nested1;
      package Nested2 is
         type Child is new Root with private;
      private
         type Child is new Root with record
            C2 : Integer;
         end record;
      end;
      use Nested2;

      function Create (X : Integer) return Child with
        Global => null,
        Import;
      function Get_R (X : Root) return Integer with
        Global => null,
        Import;
      function Get_C (X : Child) return Integer with
        Global => null,
        Import;

      procedure P1 (A, B : Integer; D, E : out Integer) with
        Depends => (D => B, E => (A, B));
      --  Imprecision is expected, private parts are merged

      procedure P1 (A, B : Integer; D, E : out Integer) is
         X : Child := Create (A);
         Y : Child := Create (B);
      begin
         Root (X) := Root (Y);
         D := Get_R (Root (X));
         E := Get_C (X);
      end P1;

      procedure P2 (A, B : Integer; D, E : out Integer) with
        Depends => (D => B, E => B, null => A);

      procedure P2 (A, B : Integer; D, E : out Integer) is
         X : Child := Create (A);
         Y : Child := Create (B);
      begin
         Root'Class (X) := Root'Class (Y);
         D := Get_R (Root (X));
         E := Get_C (X);
      end P2;

      procedure P3 (A, B : Integer; D, E : out Integer) with
        Depends => (D => B, E => (A, B));

      procedure P3 (A, B : Integer; D, E : out Integer) is
         X : Root'Class := Create (A);
         Y : Root'Class := Create (B);
      begin
         Root (X) := Root (Y);
         D := Get_R (Root (X));
         E := Get_C (Child (X));
      end P3;

      procedure P4 (A, B : Integer; D, E : out Integer) with
        Depends => (D => B, E => B, null => A);

      procedure P4 (A, B : Integer; D, E : out Integer) is
         X : Root'Class := Create (A);
         Y : Root'Class := Create (B);
      begin
         X := Y;
         D := Get_R (Root (X));
         E := Get_C (Child (X));
      end P4;
   begin
      null;
   end;
begin
   null;
end Test_Assignment;
