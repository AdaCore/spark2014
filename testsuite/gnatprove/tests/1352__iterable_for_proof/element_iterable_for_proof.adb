procedure Element_Iterable_For_Proof with SPARK_Mode is

   --  Test with correct annotation

   package Test_OK is
      type Int_Acc is access Integer;
      type Data_Array is array (Positive range <>) of not null Int_Acc;
      type Container (Max : Natural) is record
         Content : Data_Array (1 .. Max);
      end record with
        Iterable =>
          (First => First,
           Next => Next,
           Has_Element => Has_Element,
           Constant_Reference => Constant_Reference);

      function First (C : Container) return Natural is (1);
      function Next (C : Container; I : Natural) return Natural is
        (if I in 1 .. C.Max - 1 then I + 1 else 0);
      function Has_Element (C : Container; I : Natural) return Boolean is
        (I in 1 .. C.Max);
      function Constant_Reference (C : Container; I : Natural) return not null access constant Integer is
        (C.Content (I))
      with Pre => Has_Element (C, I);

      function Element (C : Container; I : Natural) return Integer is
        (C.Content (I).all)
          with Annotate => (GNATprove, Iterable_For_Proof, "Element"), -- @ITERABLE_ANNOTATION:PASS
          Pre => Has_Element (C, I);
   end Test_OK;

   --  Test with an unprovable precondition on Element

   package Test_Precondition is
      type Int_Acc is access Integer;
      type Data_Array is array (Positive range <>) of not null Int_Acc;
      type Container (Max : Natural) is record
         Content : Data_Array (1 .. Max);
      end record with
        Iterable =>
          (First => First,
           Next => Next,
           Has_Element => Has_Element,
           Constant_Reference => Constant_Reference);

      function First (C : Container) return Natural is (1);
      function Next (C : Container; I : Natural) return Natural is
        (if I in 1 .. C.Max - 1 then I + 1 else 0);
      function Has_Element (C : Container; I : Natural) return Boolean is
        (I in 1 .. C.Max);
      function Constant_Reference (C : Container; I : Natural) return not null access constant Integer is
        (C.Content (I))
          with Pre => Has_Element (C, I);

      function F return Boolean with Import, Global => null;

      function Element (C : Container; I : Natural) return Integer is --  @PRECONDITION:FAIL
        (C.Content (I).all)
          with Annotate => (GNATprove, Iterable_For_Proof, "Element"),
          Pre => Has_Element (C, I) and then F;
   end Test_Precondition;

   --  Test with an Element primitive that does not correspond to Constant_Reference

   package Bad_Element_Primitive is
      type Int_Acc is access Integer;
      type Data_Array is array (Positive range <>) of not null Int_Acc;
      type Container (Max : Natural) is record
         Content : Data_Array (1 .. Max);
      end record with
        Iterable =>
          (First => First,
           Next => Next,
           Has_Element => Has_Element,
           Constant_Reference => Constant_Reference);

      function First (C : Container) return Natural is (1);
      function Next (C : Container; I : Natural) return Natural is
        (if I in 1 .. C.Max - 1 then I + 1 else 0);
      function Has_Element (C : Container; I : Natural) return Boolean is
        (I in 1 .. C.Max);
      function Constant_Reference (C : Container; I : Natural) return not null access constant Integer is
        (C.Content (I))
      with Pre => Has_Element (C, I);

      function Element (C : Container; I : Natural) return Integer is
        (0)
          with Annotate => (GNATprove, Iterable_For_Proof, "Element"), -- @ITERABLE_ANNOTATION:FAIL
          Pre => Has_Element (C, I);
   end Bad_Element_Primitive;

   --  Test that we are using Element in quantified expressions. The definition
   --  of Constant_Reference is hidden, so the assertion can only be proved if
   --  Element is used instead.

   package Test_Hidden is
      type Int_Acc is access Integer;
      type Data_Array is array (Positive range <>) of not null Int_Acc;
      type Container (Max : Natural) is record
         Content : Data_Array (1 .. Max);
      end record with
        Iterable =>
          (First => First,
           Next => Next,
           Has_Element => Has_Element,
           Constant_Reference => Constant_Reference);

      function First (C : Container) return Natural is (1);
      function Next (C : Container; I : Natural) return Natural is
        (if I in 1 .. C.Max - 1 then I + 1 else 0);
      function Has_Element (C : Container; I : Natural) return Boolean is
        (I in 1 .. C.Max);
      function Constant_Reference (C : Container; I : Natural) return not null access constant Integer
        with Pre => Has_Element (C, I),
        Import, Global => null;

      function Element (C : Container; I : Natural) return Integer is
        (C.Content (I).all)
          with Annotate => (GNATprove, Iterable_For_Proof, "Element"), -- @ITERABLE_ANNOTATION:FAIL
          Pre => Has_Element (C, I);
   end Test_Hidden;
   use Test_Hidden;

   X : Container (10) := (Max => 10, Content => (others => new Integer'(0)));
begin
   pragma Assert (for all E of X => E = 0); -- @ASSERT:PASS
end;
