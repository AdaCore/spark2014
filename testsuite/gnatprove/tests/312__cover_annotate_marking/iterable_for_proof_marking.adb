procedure Iterable_Marking with SPARK_Mode is

   package Not_In_SPARK with SPARK_Mode => Off is
      type T is new Integer;
   end Not_In_SPARK;

   --  KO when container is in SPARK, but contains is not.

   package A is
      type T is (Container) with
        Iterable => (First       => First,
                     Next        => Next,
                     Has_Element => Has_Element,
                     Element     => Element);
      function First (X : T) return T is (X);
      function Next (X : T; Y : T) return T is (Y);
      function Has_Element (X : T; Y : T) return Boolean is (False);
      function Element (X : T; Y : T) return T is (Y);
      function Contains (X : T; Y : T) return Boolean with SPARK_Mode => Off;
      pragma Annotate (GNATprove, Iterable_For_Proof, "contains", Contains);
   end A;
   package body A with SPARK_Mode => Off is
      function Contains (X : T; Y : T) return Boolean is (False);
   end A;

   --  Completely ignored if container fully out of SPARK.

   package A_OK is
      function Contains (X : Not_In_SPARK.T; Y : Not_In_SPARK.T) return Boolean
        with SPARK_Mode => Off;
      function Model (X : Not_In_SPARK.T) return Not_In_SPARK.T
        with SPARK_Mode => Off;
      pragma Annotate (GNATprove, Iterable_For_Proof, "contains", Contains);
      pragma Annotate (GNATprove, Iterable_For_Proof, "model", Model);
   private
      pragma SPARK_Mode (Off);
      function Contains (X : Not_In_SPARK.T; Y : Not_In_SPARK.T) return Boolean is (False);
      function Model (X : Not_In_SPARK.T) return Not_In_SPARK.T is (X);
   end A_OK;

   --  KO if Element primitive not in SPARK for Contains container.

   package B is
      type T is (Container) with
        Iterable => (First       => First,
                     Next        => Next,
                     Has_Element => Has_Element,
                     Element     => Element);
      function First (X : T) return T is (X);
      function Next (X : T; Y : T) return T is (X);
      function Has_Element (X : T; Y : T) return Boolean is (False);
      function Contains (X : T; Y : T) return Boolean is (False);
      function Element (X : T; Y : T) return Not_In_SPARK.T with SPARK_Mode => Off;
      pragma Annotate (GNATprove, Iterable_For_Proof, "contains", Contains);
   private
      pragma SPARK_Mode (Off);
      function Element (X : T; Y : T) return Not_In_SPARK.T is (0);
   end B;

   --  KO (* 2) if Element primitives not in SPARK for models containers.

   package C is
      type Concrete is (Conc) with
        Iterable => (First       => First,
                     Next        => Next,
                     Has_Element => Has_Element,
                     Element     => Element);
      type Abstracted is (Abst) with
        Iterable => (First       => First_2,
                     Next        => Next_2,
                     Has_Element => Has_Element_2,
                     Element     => Element_2);
      function First_2 (X : Abstracted) return Integer is (0);
      function Next_2 (X : Abstracted; Y : Integer) return Integer is (0);
      function Has_Element_2 (X : Abstracted; Y : Integer) return Boolean is (False);
      function Element_2 (X : Abstracted; Y : Integer) return Integer is (0);

      function First (X : Concrete) return Integer is (0);
      function Next (X : Concrete; Y : Integer) return Integer is (0);
      function Has_Element (X : Concrete; Y : Integer) return Boolean is (False);
      function Model (X : Concrete) return Abstracted is (Abst);
      function Element (X : Concrete; Y : Integer) return Not_In_SPARK.T with SPARK_Mode => Off;
      pragma Annotate (GNATprove, Iterable_For_Proof, "model", Model);
   private
      pragma SPARK_Mode (Off);
      function Element (X : Concrete; Y : Integer) return Not_In_SPARK.T is (0);
   end C;

   package D is
      type Concrete is (Conc) with
        Iterable => (First       => First,
                     Next        => Next,
                     Has_Element => Has_Element,
                     Element     => Element);
      type Abstracted is (Abst) with
        Iterable => (First       => First_2,
                     Next        => Next_2,
                     Has_Element => Has_Element_2,
                     Element     => Element_2);
      function First_2 (X : Abstracted) return Integer is (0);
      function Next_2 (X : Abstracted; Y : Integer) return Integer is (0);
      function Has_Element_2 (X : Abstracted; Y : Integer) return Boolean is (False);
      function Element_2 (X : Abstracted; Y : Integer) return Not_In_SPARK.T with SPARK_Mode => Off;

      function First (X : Concrete) return Integer is (0);
      function Next (X : Concrete; Y : Integer) return Integer is (0);
      function Has_Element (X : Concrete; Y : Integer) return Boolean is (False);
      function Model (X : Concrete) return Abstracted is (Abst);
      function Element (X : Concrete; Y : Integer) return Integer is (0);
      pragma Annotate (GNATprove, Iterable_For_Proof, "model", Model);
   private
      pragma SPARK_Mode (Off);
      function Element_2 (X : Abstracted; Y : Integer) return Not_In_SPARK.T is (0);
   end D;

   --  Iterable_For_Proof with a non-sensical argument
   X : constant Integer := 0;
   pragma Annotate (GNATprove, Iterable_For_Proof, "contains", 0);
   pragma Annotate (GNATprove, Iterable_For_Proof, "contains", X);

begin
   null;
end Iterable_Marking;
