with Private_Ownership;
with Private_No_Reclamation;
with Private_No_Is_Null;
with Private_Tagged;
with Private_In_Out;    use Private_In_Out;
with Private_Tagged_Ext;
with Private_Discriminants;
procedure Test_Ownership_Annotation with SPARK_Mode is

   procedure Test_Private_No_Reclamation with
     Global => null
   is
      use Private_No_Reclamation;
      G : Pool_Specific_Access := Allocate (13); --@RESOURCE_LEAK:NONE
      procedure P1 (X : in out Pool_Specific_Access) with
        Global => null,
        Annotate => (GNATprove, Always_Return),
        Import;
      procedure P2 (X : out Pool_Specific_Access) with
        Global => null,
        Annotate => (GNATprove, Always_Return),
        Import;
      procedure P1 with
        Global => (In_Out => G),
        Annotate => (GNATprove, Always_Return),
        Import;
      procedure P2 with
        Global => (Output => G),
        Annotate => (GNATprove, Always_Return),
        Import;
      A : Pool_Specific_Access;
      B : Pool_Specific_Access;
      C : Pool_Specific_Access; --@RESOURCE_LEAK:NONE
      D : Pool_Specific_Access; --@RESOURCE_LEAK:NONE
      E : Pool_Specific_Access;
   begin
      A := Allocate (13);
      B := Allocate (13);
      D := Allocate (13);
      C := Allocate (13);
      Deallocate (A);
      C := B; --@RESOURCE_LEAK:NONE
      P1 (D);
      P2 (D); --@RESOURCE_LEAK:NONE
      P1;
      P2; --@RESOURCE_LEAK:NONE
   end Test_Private_No_Reclamation;

   procedure Test_Private_No_Is_Null with
     Global => null
   is
      use Private_No_Is_Null;
      G : Pool_Specific_Access := Allocate (13); --@RESOURCE_LEAK:FAIL
      procedure P1 (X : in out Pool_Specific_Access) with
        Global => null,
        Annotate => (GNATprove, Always_Return),
        Import;
      procedure P2 (X : out Pool_Specific_Access) with
        Global => null,
        Annotate => (GNATprove, Always_Return),
        Import;
      procedure P1 with
        Global => (In_Out => G),
        Annotate => (GNATprove, Always_Return),
        Import;
      procedure P2 with
        Global => (Output => G),
        Annotate => (GNATprove, Always_Return),
        Import;
      A : Pool_Specific_Access; --@RESOURCE_LEAK:FAIL A is deallocated but we cannot know that
      B : Pool_Specific_Access;
      C : Pool_Specific_Access; --@RESOURCE_LEAK:FAIL
      D : Pool_Specific_Access; --@RESOURCE_LEAK:FAIL
      E : Pool_Specific_Access; --@RESOURCE_LEAK:FAIL E is null by default but we cannot know that
   begin
      A := Allocate (13); --@RESOURCE_LEAK:FAIL A is null by default but we cannot know that
      B := Allocate (13); --@RESOURCE_LEAK:FAIL B is null by default but we cannot know that
      D := Allocate (13); --@RESOURCE_LEAK:FAIL D is null by default but we cannot know that
      C := Allocate (13); --@RESOURCE_LEAK:FAIL C is null by default but we cannot know that
      Deallocate (A);
      C := B; --@RESOURCE_LEAK:FAIL
      P1 (D);
      P2 (D); --@RESOURCE_LEAK:FAIL
      P1;
      P2; --@RESOURCE_LEAK:FAIL
   end Test_Private_No_Is_Null;

   procedure Test_Private_Tagged with
     Global => null
   is
      use Private_Tagged;
      G : Pool_Specific_Access := Allocate (13); --@RESOURCE_LEAK:FAIL
      procedure P1 (X : in out Pool_Specific_Access) with
        Global => null,
        Annotate => (GNATprove, Always_Return),
        Import;
      procedure P2 (X : out Pool_Specific_Access) with
        Global => null,
        Annotate => (GNATprove, Always_Return),
        Import;
      procedure P1 with
        Global => (In_Out => G),
        Annotate => (GNATprove, Always_Return),
        Import;
      procedure P2 with
        Global => (Output => G),
        Annotate => (GNATprove, Always_Return),
        Import;
      A : Pool_Specific_Access;
      B : Pool_Specific_Access;
      C : Pool_Specific_Access; --@RESOURCE_LEAK:FAIL
      D : Pool_Specific_Access; --@RESOURCE_LEAK:FAIL
      E : Pool_Specific_Access;
   begin
      A := Allocate (13);
      B := Allocate (13);
      D := Allocate (13);
      C := Allocate (13);
      Deallocate (A);
      C := B; --@RESOURCE_LEAK:FAIL
      P1 (D);
      P2 (D); --@RESOURCE_LEAK:FAIL
      P1;
      P2; --@RESOURCE_LEAK:FAIL
   end Test_Private_Tagged;

   procedure Test_Private_Tagged_2 with
     Global => null
   is
      use Private_Tagged_Ext;
      type Holder is record
         A : V;
      end record;
      G : Holder := (A => Allocate (13)); --@RESOURCE_LEAK:FAIL
      procedure P1 (X : in out Holder) with
        Global => null,
        Annotate => (GNATprove, Always_Return),
        Import;
      procedure P2 (X : out Holder) with
        Global => null,
        Annotate => (GNATprove, Always_Return),
        Import;
      procedure P1 with
        Global => (In_Out => G),
        Annotate => (GNATprove, Always_Return),
        Import;
      procedure P2 with
        Global => (Output => G),
        Annotate => (GNATprove, Always_Return),
        Import;
      A : Holder;
      B : Holder;
      C : Holder; --@RESOURCE_LEAK:FAIL
      D : Holder; --@RESOURCE_LEAK:FAIL
      E : Holder;
   begin
      A.A := Allocate (13);
      B.A := Allocate (13);
      D.A := Allocate (13);
      C.A := Allocate (13);
      Deallocate (A.A);
      C := B; --@RESOURCE_LEAK:FAIL
      P1 (D);
      P2 (D); --@RESOURCE_LEAK:FAIL
      P1;
      P2; --@RESOURCE_LEAK:FAIL
   end Test_Private_Tagged_2;

   procedure Test_Private_Discriminants with
     Global => null
   is
      use Private_Discriminants;
      G : Pool_Specific_Access := Allocate (13); --@RESOURCE_LEAK:FAIL
      procedure P1 (X : in out Pool_Specific_Access) with
        Global => null,
        Annotate => (GNATprove, Always_Return),
        Import;
      procedure P2 (X : out Pool_Specific_Access) with
        Global => null,
        Annotate => (GNATprove, Always_Return),
        Import;
      procedure P1 with
        Global => (In_Out => G),
        Annotate => (GNATprove, Always_Return),
        Import;
      procedure P2 with
        Global => (Output => G),
        Annotate => (GNATprove, Always_Return),
        Import;
      A : Pool_Specific_Access;
      B : Pool_Specific_Access;
      C : Pool_Specific_Access; --@RESOURCE_LEAK:FAIL
      D : Pool_Specific_Access; --@RESOURCE_LEAK:FAIL
      E : Pool_Specific_Access;
   begin
      A := Allocate (13);
      B := Allocate (13);
      D := Allocate (13);
      C := Allocate (13);
      Deallocate (A);
      C := B; --@RESOURCE_LEAK:FAIL
      P1 (D);
      P2 (D); --@RESOURCE_LEAK:FAIL
      P1;
      P2; --@RESOURCE_LEAK:FAIL
   end Test_Private_Discriminants;

   procedure Test_Private_Pointer with
     Global => null
   is
      use Private_Ownership;
      G : Pool_Specific_Access := Allocate (13); --@RESOURCE_LEAK:FAIL
      procedure P1 (X : in out Pool_Specific_Access) with
        Global => null,
        Annotate => (GNATprove, Always_Return),
        Import;
      procedure P2 (X : out Pool_Specific_Access) with
        Global => null,
        Annotate => (GNATprove, Always_Return),
        Import;
      procedure P1 with
        Global => (In_Out => G),
        Annotate => (GNATprove, Always_Return),
        Import;
      procedure P2 with
        Global => (Output => G),
        Annotate => (GNATprove, Always_Return),
        Import;
      A : Pool_Specific_Access;
      B : Pool_Specific_Access;
      C : Pool_Specific_Access; --@RESOURCE_LEAK:FAIL
      D : Pool_Specific_Access; --@RESOURCE_LEAK:FAIL
      E : Pool_Specific_Access;
   begin
      A := Allocate (13);
      B := Allocate (13);
      D := Allocate (13);
      C := Allocate (13);
      Deallocate (A);
      C := B; --@RESOURCE_LEAK:FAIL
      P1 (D);
      P2 (D); --@RESOURCE_LEAK:FAIL
      P1;
      P2; --@RESOURCE_LEAK:FAIL
   end Test_Private_Pointer;

   procedure Test_Private_Pointer_2 with
     Global => null
   is
      use Private_Ownership;
      type V is new Pool_Specific_Access with
        Predicate => Is_Null (Pool_Specific_Access (V)) or else Deref (Pool_Specific_Access (V)) > 0;
      type Holder is record
         A : V;
      end record;
      G : Holder := (A => Allocate (13)); --@RESOURCE_LEAK:FAIL
      procedure P1 (X : in out Holder) with
        Global => null,
        Annotate => (GNATprove, Always_Return),
        Import;
      procedure P2 (X : out Holder) with
        Global => null,
        Annotate => (GNATprove, Always_Return),
        Import;
      procedure P1 with
        Global => (In_Out => G),
        Annotate => (GNATprove, Always_Return),
        Import;
      procedure P2 with
        Global => (Output => G),
        Annotate => (GNATprove, Always_Return),
        Import;
      A : Holder;
      B : Holder;
      C : Holder; --@RESOURCE_LEAK:FAIL
      D : Holder; --@RESOURCE_LEAK:FAIL
      E : Holder;
   begin
      A.A := Allocate (13);
      B.A := Allocate (13);
      D.A := Allocate (13);
      C.A := Allocate (13);
      Deallocate (A.A);
      C := B; --@RESOURCE_LEAK:FAIL
      P1 (D);
      P2 (D); --@RESOURCE_LEAK:FAIL
      P1;
      P2; --@RESOURCE_LEAK:FAIL
   end Test_Private_Pointer_2;

   procedure Test_Private_Pointer_3 with
     Global => null
   is
      use Private_Ownership;
      type C_Acc is access constant Pool_Specific_Access;
      type Holder is record
         A : C_Acc;
      end record;
      C : aliased constant Pool_Specific_Access := Allocate (13); --@RESOURCE_LEAK:FAIL
      G : Holder := (A => C'Access); --@RESOURCE_LEAK:NONE
   begin
      G.A := null; --@RESOURCE_LEAK:NONE
   end Test_Private_Pointer_3;

   procedure Test_IO with
     Global => null
   is
      G : File_Descriptor := Open ("g.txt"); --@RESOURCE_LEAK:FAIL
      procedure P1 (X : in out File_Descriptor) with
        Global => null,
        Annotate => (GNATprove, Always_Return),
        Import;
      procedure P2 (X : out File_Descriptor) with
        Global => null,
        Annotate => (GNATprove, Always_Return),
        Import;
      procedure P1 with
        Global => (In_Out => G),
        Annotate => (GNATprove, Always_Return),
        Import;
      procedure P2 with
        Global => (Output => G),
        Annotate => (GNATprove, Always_Return),
        Import;
      A : File_Descriptor;
      B : File_Descriptor;
      C : File_Descriptor; --@RESOURCE_LEAK:FAIL
      D : File_Descriptor; --@RESOURCE_LEAK:FAIL
      E : File_Descriptor;
   begin
      A := Open ("a.txt");
      B := Open ("b.txt");
      D := Open ("d.txt");
      C := Open ("c.txt");
      Close (A);
      C := B; --@RESOURCE_LEAK:FAIL
      P1 (D);
      P2 (D); --@RESOURCE_LEAK:FAIL
      P1;
      P2; --@RESOURCE_LEAK:FAIL
   end Test_IO;

begin
   null;
end Test_Ownership_Annotation;
