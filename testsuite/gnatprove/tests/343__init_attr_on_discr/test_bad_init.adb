procedure Test_Bad_Init with SPARK_Mode is

   type R (D : Integer := 1) is record
      A, B : Integer;
   end record
     with Relaxed_Initialization;

   subtype S is R;

   subtype S_1 is R (1);

   type RR is record
      F : R;
   end record;

   G1 : R;
   G2 : R;

   --  'Initialized is only allowed on discriminants of quantified variables

   procedure On_Entities (X : R; Y : out R) with
     Global => (Input => G1, Output => G2);

   procedure On_Entities (X : R; Y : out R) is
   begin
      pragma Assert (G1.D'Initialized and G2.D'Initialized);
      pragma Assert (X.D'Initialized and Y.D'Initialized);
      Y := G1;
      G2 := X;
   end On_Entities;

   --  'Initialized is only allowed on discriminants of conversions if the type is not constrained

   function On_Conversion (X, Y, Z : RR) return Boolean is
     (S (X.F).D'Initialized -- OK
      and S_1 (Y.F).D'Initialized -- No
      and S (S_1 (S (Y.F))).D'Initialized) -- No
   with Ghost;

   --  'Initialized is allowed on discriminants of 'Old if it is allowed on discriminants of its prefix

   procedure On_Attribute (X : RR; Y : in out RR; Z : in out R) with
     Post => Y.F'Old.D'Initialized -- OK
     and Z'Old.D'Initialized; -- No

   procedure On_Attribute (X : RR; Y : in out RR; Z : in out R) is
   begin
      Y := X;
      Z := X.F;
   end On_Attribute;

   --  'Initialized is not allowed on discriminants of functions calls and
   --  aggregates, their discriminants are always initialized.

   function F return R with
     Import,
     Global => null;

   function On_Functions_And_Aggregates return Boolean is
     (F.D'Initialized and R'(1, 2, 3).D'Initialized)
   with Ghost;


begin
   null;
end Test_Bad_Init;
