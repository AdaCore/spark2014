with Ada.Containers; use Ada.Containers;
with SPARK.Containers.Functional.Vectors;

procedure Bad_Annotate with SPARK_Mode is
   procedure Do_Something is null
     with Annotate => (GNATprove, Inline_For_Proof);
   procedure Do_Something_2 is null
     with Annotate => (GNATprove, Iterable_For_Proof, "Model");
   function Id (X : Integer) return Integer is (X)
     with Annotate => (GNATprove, Iterable_For_Proof, "Foo");
   function Add (X, Y : Integer) return Integer is (X + Y)
     with Annotate => (GNATprove, Iterable_For_Proof, "Model");
   function Id_2 (X : Integer) return Integer is (X)
     with Annotate => (GNATprove, Iterable_For_Proof, "Model");
   function Id_3 (X : Integer) return Integer is (X)
     with Annotate => (GNATprove, Iterable_For_Proof, "Contains");
   function Add_2 (X, Y : Integer) return Integer is (X + Y)
     with Annotate => (GNATprove, Iterable_For_Proof, "Contains");
   function Eq (X, Y : Integer) return Boolean is (X = Y)
     with Annotate => (GNATprove, Iterable_For_Proof, "Contains");

   type T is record
      F1 : Integer;
      F2 : Integer;
      F3 : Integer;
      F4 : Integer;
   end record
     with Iterable => (First       => First,
                       Next        => Next,
                       Has_Element => Has_Element,
                       Element     => Element);

   type Cursor is mod 5;

   function First (X : T) return Cursor is (1);
   function Next (X : T; C : Cursor) return Cursor is (C + 1);
   function Has_Element (X : T; C : Cursor) return Boolean is (C /= 0);
   function Element (X : T; C : Cursor) return Integer is
     (case C is
         when 0 => raise Program_Error,
         when 1 => X.F1,
         when 2 => X.F2,
         when 3 => X.F3,
         when 4 => X.F4)
   with Pre => Has_Element (X, C);

   function Get_F1 (X : T) return Integer is (X.F1)
     with Annotate => (GNATprove, Iterable_For_Proof, "Model");
   function Id (X : T; Y : Boolean) return Boolean is (Y)
     with Annotate => (GNATprove, Iterable_For_Proof, "Contains");

   function Contains (X : T; Y : Integer) return Boolean is
     (Y in X.F1 | X.F2 | X.F3 | X.F4)
     with Annotate => (GNATprove, Iterable_For_Proof, "Contains");

   package Sequences is new SPARK.Containers.Functional.Vectors (Positive, Integer);

   function Model (X : T) return Sequences.Sequence with
     Annotate => (GNATprove, Iterable_For_Proof, "Model"),
     Post => Sequences.Length (Model'Result) = 4
   is
      M : Sequences.Sequence;
   begin
      M := Sequences.Add (M, X.F1);
      M := Sequences.Add (M, X.F2);
      M := Sequences.Add (M, X.F3);
      M := Sequences.Add (M, X.F4);
      return M;
   end Model;

   type U32 is mod 2 ** 32;
   subtype S is U32 with Annotate => (GNATprove, No_Wrap_Around);
   type My_Int is new Integer with Annotate => (GNATprove, No_Wrap_Around);
   type My_Boolean is new Boolean with Annotate => (GNATprove, Always_Return);

   procedure Do_Something_3 is null
     with Annotate => (GNATprove);
   pragma Annotate (GNATprove, Might_Not_Return, "foo");
   pragma Annotate (GNATprove, Inline_For_Proof, "foo");
   pragma Annotate (GNATprove, Always_Return, "foo");
   pragma Annotate (GNATprove, No_Wrap_Around, "foo");
   pragma Annotate (GNATprove);
begin
   null;
end Bad_Annotate;
