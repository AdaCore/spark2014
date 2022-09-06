procedure Test_Illegal with SPARK_Mode is

   function P (X : Integer) return Boolean with
     Ghost,
     Import,
     Global => null,
     Annotate => (GNATprove, Always_Return);

   function F1 (X : Integer) return Integer is (X);

   function Lemma_F1 (X : Integer) return Boolean with
     Ghost,
     Import,
     Global => null,
     Annotate => (GNATprove, Always_Return),
     Annotate => (GNATprove, Automatic_Instantiation),
     Post => Lemma_F1'Result and then P (X);

   function F2 (X : Integer) return Integer is (X);

   procedure Lemma_F2 (X : Integer) with
     Import,
     Global => null,
     Annotate => (GNATprove, Always_Return),
     Annotate => (GNATprove, Automatic_Instantiation),
     Post => P (X);

   function F3 (X : Integer) return Integer is (X);

   G : Integer;

   procedure Lemma_F3 (X : Integer) with
     Ghost,
     Import,
     Global => (In_Out => G),
     Annotate => (GNATprove, Always_Return),
     Annotate => (GNATprove, Automatic_Instantiation),
     Post => P (X);

   function F4 (X : Integer) return Integer is (X);

   procedure Lemma_F4 (X : in out Integer) with
     Ghost,
     Import,
     Global => null,
     Annotate => (GNATprove, Always_Return),
     Annotate => (GNATprove, Automatic_Instantiation),
     Post => P (X);

   function F5 (X : Integer) return Integer is (X);

   procedure Lemma_F5 (X : out Integer) with
     Ghost,
     Import,
     Global => null,
     Annotate => (GNATprove, Always_Return),
     Annotate => (GNATprove, Automatic_Instantiation),
     Post => P (X);

   function F6 (X : Integer) return Integer is (X);

   procedure Lemma_F6 (X : access Integer) with
     Ghost,
     Import,
     Global => null,
     Annotate => (GNATprove, Always_Return),
     Annotate => (GNATprove, Automatic_Instantiation),
     Post => P (X.all);

   function F7 (X : Integer) return Integer is (X);

   package Nested is
      procedure Lemma_F7 (X : Integer) with
        Ghost,
        Import,
        Global => null,
        Annotate => (GNATprove, Always_Return),
        Annotate => (GNATprove, Automatic_Instantiation),
        Post => P (X);
   end Nested;

   function F8 (X : Integer) return Integer is (X) with Volatile_Function;

   procedure Lemma_F8 (X : Integer) with
     Ghost,
     Import,
     Global => null,
     Annotate => (GNATprove, Always_Return),
     Annotate => (GNATprove, Automatic_Instantiation),
     Post => P (X);

   function F9 (X : Integer) return Integer is (X) with Volatile_Function;

   procedure Not_Lemma_F9 (X : Integer) with
     Ghost,
     Import,
     Global => null,
     Annotate => (GNATprove, Always_Return),
     Post => P (X);

   procedure Lemma_F9 (X : Integer) with
     Ghost,
     Import,
     Global => null,
     Annotate => (GNATprove, Always_Return),
     Annotate => (GNATprove, Automatic_Instantiation),
     Post => P (X);

   function F10 (X : Integer) return Integer is (X) with Volatile_Function;

   procedure Not_Lemma_F10 (X : Integer) with
     Import,
     Global => null,
     Annotate => (GNATprove, Always_Return),
     Post => P (X);

   procedure Lemma_F10 (X : Integer) with
     Ghost,
     Import,
     Global => null,
     Annotate => (GNATprove, Always_Return),
     Annotate => (GNATprove, Automatic_Instantiation),
     Post => P (X);

   function F11 (X : Integer) return Integer is (X) with Volatile_Function;

   type Unused is new Integer;

   procedure Lemma_F11 (X : Integer) with
     Ghost,
     Import,
     Global => null,
     Annotate => (GNATprove, Always_Return),
     Annotate => (GNATprove, Automatic_Instantiation),
     Post => P (X);

begin
   null;
end Test_Illegal;
