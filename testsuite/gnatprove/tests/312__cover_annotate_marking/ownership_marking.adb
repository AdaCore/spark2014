procedure Ownership_Marking with SPARK_Mode is
   package Out_Of_Spark with SPARK_Mode => Off is
      type T is new Integer;
      function Is_Reclaimed (X : T) return Boolean is (False);
   end Out_Of_Spark;

   --  Ownership annotation for out-of-Spark types are essentially ignored.

   pragma Annotate (GNATprove, Ownership, Out_Of_Spark.T);
   pragma Annotate
     (GNATprove, Ownership, "is_reclaimed", Out_Of_SPARK.Is_Reclaimed);

   --  However, if type is in SPARK, function must be as well.

   package Bad_Reclamation is
      type T is private;
      function Is_Reclaimed (X : T) return Boolean with SPARK_Mode => Off;
      pragma Annotate (GNATprove, Ownership, "is_reclaimed", Is_Reclaimed);
   private
      pragma SPARK_Mode (Off);
      type T is new Integer;
      function Is_Reclaimed (X : T) return Boolean is (True);
   end Bad_Reclamation;

   package Multiple_Ownership is
      type T is private;
      pragma Annotate (GNATprove, Ownership, T);
      pragma Annotate (GNATprove, Ownership, "needs_reclamation", T);
   private
      pragma SPARK_Mode (Off);
      type T is new Integer;
   end Multiple_Ownership;

   --  Covers passing over other 4-arguments
   --  pragmas when looking for reclamation functions

   package Find_Other_Pragmas is
      type Owned is private with
        Annotate => (GNATprove, Ownership, "needs_reclamation");
      type T is (Container) with
        Iterable => (First       => First,
                     Next        => Next,
                     Has_Element => Has_Element,
                     Element     => Element);
      function First (X : T) return T is (X);
      function Next (X : T; Y : T) return T is (Y);
      function Has_Element (X : T; Y : T) return Boolean is (False);
      function Contains (X : T; Y : T) return Boolean is (False);
      function Element (X : T; Y : T) return T is (Y);
      pragma Annotate (GNATprove, Iterable_For_Proof, "contains", Contains);
   private
      pragma SPARK_Mode (Off);
      type Owned is new Integer;
   end Find_Other_Pragmas;

   package Go_Over_Other_Pragmas is
      type Owned is private with
        Annotate => (GNATprove, Ownership, "needs_reclamation");
      type T is (Container) with
        Iterable => (First       => First,
                     Next        => Next,
                     Has_Element => Has_Element,
                     Element     => Element);
      function First (X : T) return T is (X);
      function Next (X : T; Y : T) return T is (Y);
      function Has_Element (X : T; Y : T) return Boolean is (False);
      function Contains (X : T; Y : T) return Boolean is (False);
      function Element (X : T; Y : T) return T is (Y);
      pragma Annotate (GNATprove, Iterable_For_Proof, "contains", Contains);
      function Is_Reclaimed (X : Owned) return Boolean is (True);
      pragma Annotate (GNATprove, Ownership, "is_reclaimed", Is_Reclaimed);
   private
      pragma SPARK_Mode (Off);
      type Owned is new Integer;
   end Go_Over_Other_Pragmas;

begin
   null;
end Ownership_Marking;
