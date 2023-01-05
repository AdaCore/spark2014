procedure Relaxed_Private (R : Integer) with SPARK_Mode is

   --  Test that initialization is enforced on copy

   procedure Test_Private_Scalar is
      package Nested is
         type Priv_Scalar is private;
         C : constant Priv_Scalar;
         procedure In_Out_Relaxed (X : in out Priv_Scalar) with
           Relaxed_Initialization => X,
           Global => null,
           Annotate => (GNATProve, Always_Return),
           Import;
         procedure Out_Relaxed (X : out Priv_Scalar) with
           Relaxed_Initialization => X,
           Global => null,
           Annotate => (GNATProve, Always_Return),
           Import;

      private
         pragma SPARK_Mode (Off);
         type Priv_Scalar is new Integer;
         C : constant Priv_Scalar := 0;
      end Nested;
      use Nested;

      procedure Test (No_Init : out Priv_Scalar; Init : in out Priv_Scalar) with --@INIT_BY_PROOF:FAIL
        Relaxed_Initialization => (No_Init, Init),
        Global => R
      is
      begin
         --  Init is initialized

         In_Out_Relaxed (Init); --@INIT_BY_PROOF:NONE

         --  No_Init is not initialized

         if R = 0 then
            In_Out_Relaxed (No_Init); --@INIT_BY_PROOF:FAIL
         elsif R = 1 then
            Out_Relaxed (No_Init); --@INIT_BY_PROOF:NONE
            In_Out_Relaxed (No_Init); --@INIT_BY_PROOF:PASS
         end if;

         --  No_Init should be initialized on exit
      end Test;

      type My_Rec is record
         F, G : Priv_Scalar;
      end record;
      procedure In_Out_Rec (X : in out My_Rec) with
        Global => null,
        Annotate => (GNATProve, Always_Return),
        Import;
      procedure Out_Rec (X : out My_Rec) with
        Global => null,
        Annotate => (GNATProve, Always_Return),
        Import;
      procedure In_Out_Rec_Relaxed (X : in out My_Rec) with
        Relaxed_Initialization => X,
        Global => null,
        Annotate => (GNATProve, Always_Return),
        Import;
      procedure Out_Rec_Relaxed (X : out My_Rec) with
        Relaxed_Initialization => X,
        Global => null,
        Annotate => (GNATProve, Always_Return),
        Import;

      Default : Priv_Scalar with Relaxed_Initialization;
      Init    : Priv_Scalar := C with Relaxed_Initialization;
      Comp    : My_Rec with Relaxed_Initialization;

   begin
      --  Failed check when reading an uninitialized value

      if R = 0 then
         In_Out_Relaxed (Default);  --@INIT_BY_PROOF:FAIL
         In_Out_Relaxed (Default);  --@INIT_BY_PROOF:PASS

      --  Checks pass when reading a value initialized at declaration

      elsif R = 1 then
         In_Out_Relaxed (Init);  --@INIT_BY_PROOF:PASS
         In_Out_Relaxed (Init);  --@INIT_BY_PROOF:PASS

         --  Uninitialized value cannot be copied

         Init := Default;  --@INIT_BY_PROOF:FAIL

      --  Check pass if Default is initialized

      elsif R = 2 then
         Default := Init;
         In_Out_Relaxed (Default);  --@INIT_BY_PROOF:PASS
         In_Out_Relaxed (Default);  --@INIT_BY_PROOF:PASS

      --  No checks on OUT parameters, Default is initialized after the call

      elsif R = 3 then
         Out_Relaxed (Default);  --@INIT_BY_PROOF:NONE
         In_Out_Relaxed (Default);  --@INIT_BY_PROOF:PASS
         In_Out_Relaxed (Default);  --@INIT_BY_PROOF:PASS

      --  No checks on relaxed composite parameters

      elsif R = 4 then
         In_Out_Rec_Relaxed (Comp);  --@INIT_BY_PROOF:NONE
      elsif R = 5 then
         Out_Rec_Relaxed (Comp);  --@INIT_BY_PROOF:NONE

      --  No checks on OUT composite parameters

      elsif R = 6 then
         Out_Rec (Comp);  --@INIT_BY_PROOF:NONE

      --  Failed initialization check on uninitialized composite object

      elsif R = 7 then
         In_Out_Rec (Comp);  --@INIT_BY_PROOF:FAIL

      --  Complete initialization by component

      elsif R = 8 then
         Out_Relaxed (Comp.F);
         Out_Relaxed (Comp.G);
         In_Out_Rec (Comp);  --@INIT_BY_PROOF:PASS

      --  Partial initialization

      elsif R = 9 then
         Out_Relaxed (Comp.G);
         In_Out_Rec (Comp);  --@INIT_BY_PROOF:FAIL
      end if;
   end Test_Private_Scalar;

   --  Test that DIC is taken into account

   procedure Test_Private_Scalar_Init is
      package Nested is
         type Priv_Scalar is private with
           Default_Initial_Condition;
         C : constant Priv_Scalar;
         procedure In_Out_Relaxed (X : in out Priv_Scalar) with
           Relaxed_Initialization => X,
           Global => null,
           Annotate => (GNATProve, Always_Return),
           Import;

      private
         pragma SPARK_Mode (Off);
         type Priv_Scalar is new Integer;
         C : constant Priv_Scalar := 0;
      end Nested;
      use Nested;

      Default : Priv_Scalar with Relaxed_Initialization;

   begin
      --  Check pass when reading a default value

      if R = 0 then
         In_Out_Relaxed (Default);  --@INIT_BY_PROOF:PASS
      end if;
   end Test_Private_Scalar_Init;

   --  Same test with an ownership type

   procedure Test_Private_Scalar_Ownership is
      package Nested is
         type Priv_Scalar is private with
           Annotate => (GNATprove, Ownership);
         function C return Priv_Scalar with
           Global => null,
           Annotate => (GNATProve, Always_Return),
           Import;
         procedure In_Out_Relaxed (X : in out Priv_Scalar) with
           Relaxed_Initialization => X,
           Global => null,
           Annotate => (GNATProve, Always_Return),
           Import;
         procedure Out_Relaxed (X : out Priv_Scalar) with
           Relaxed_Initialization => X,
           Global => null,
           Annotate => (GNATProve, Always_Return),
           Import;

      private
         pragma SPARK_Mode (Off);
         type Priv_Scalar is new Integer;
      end Nested;
      use Nested;

      procedure Test (No_Init : out Priv_Scalar; Init : in out Priv_Scalar) with --@INIT_BY_PROOF:FAIL
        Relaxed_Initialization => (No_Init, Init),
        Global => R
      is
      begin
         --  Init is initialized

         In_Out_Relaxed (Init); --@INIT_BY_PROOF:NONE

         --  No_Init is not initialized

         if R = 0 then
            In_Out_Relaxed (No_Init); --@INIT_BY_PROOF:FAIL
         elsif R = 1 then
            Out_Relaxed (No_Init); --@INIT_BY_PROOF:NONE
            In_Out_Relaxed (No_Init); --@INIT_BY_PROOF:PASS
         end if;

         --  No_Init should be initialized on exit
      end Test;

      type My_Rec is record
         F, G : Priv_Scalar;
      end record;
      procedure In_Out_Rec (X : in out My_Rec) with
        Global => null,
        Annotate => (GNATProve, Always_Return),
        Import;
      procedure Out_Rec (X : out My_Rec) with
        Global => null,
        Annotate => (GNATProve, Always_Return),
        Import;
      procedure In_Out_Rec_Relaxed (X : in out My_Rec) with
        Relaxed_Initialization => X,
        Global => null,
        Annotate => (GNATProve, Always_Return),
        Import;
      procedure Out_Rec_Relaxed (X : out My_Rec) with
        Relaxed_Initialization => X,
        Global => null,
        Annotate => (GNATProve, Always_Return),
        Import;

      Default : Priv_Scalar with Relaxed_Initialization;
      Init    : Priv_Scalar := C with Relaxed_Initialization;
      Comp    : My_Rec with Relaxed_Initialization;

   begin
      --  Failed check when reading an uninitialized value

      if R = 0 then
         In_Out_Relaxed (Default);  --@INIT_BY_PROOF:FAIL
         In_Out_Relaxed (Default);  --@INIT_BY_PROOF:PASS

      --  Checks pass when reading a value initialized at declaration

      elsif R = 1 then
         In_Out_Relaxed (Init);  --@INIT_BY_PROOF:PASS
         In_Out_Relaxed (Init);  --@INIT_BY_PROOF:PASS

         --  Uninitialized value cannot be copied

         Init := Default;  --@INIT_BY_PROOF:FAIL

      --  Check pass if Default is initialized

      elsif R = 2 then
         Default := Init;
         In_Out_Relaxed (Default);  --@INIT_BY_PROOF:PASS
         In_Out_Relaxed (Default);  --@INIT_BY_PROOF:PASS

      --  No checks on OUT parameters, Default is initialized after the call

      elsif R = 3 then
         Out_Relaxed (Default);  --@INIT_BY_PROOF:NONE
         In_Out_Relaxed (Default);  --@INIT_BY_PROOF:PASS
         In_Out_Relaxed (Default);  --@INIT_BY_PROOF:PASS

      --  No checks on relaxed composite parameters

      elsif R = 4 then
         In_Out_Rec_Relaxed (Comp);  --@INIT_BY_PROOF:NONE
      elsif R = 5 then
         Out_Rec_Relaxed (Comp);  --@INIT_BY_PROOF:NONE

      --  No checks on OUT composite parameters

      elsif R = 6 then
         Out_Rec (Comp);  --@INIT_BY_PROOF:NONE

      --  Failed initialization check on uninitialized composite object

      elsif R = 7 then
         In_Out_Rec (Comp);  --@INIT_BY_PROOF:FAIL

      --  Complete initialization by component

      elsif R = 8 then
         Out_Relaxed (Comp.F);
         Out_Relaxed (Comp.G);
         In_Out_Rec (Comp);  --@INIT_BY_PROOF:PASS

      --  Partial initialization

      elsif R = 9 then
         Out_Relaxed (Comp.G);
         In_Out_Rec (Comp);  --@INIT_BY_PROOF:FAIL
      end if;
   end Test_Private_Scalar_Ownership;

   procedure Test_Private_Scalar_Init_Ownership is
      package Nested is
         type Priv_Scalar is private with
           Default_Initial_Condition,
           Annotate => (GNATprove, Ownership);
         C : constant Priv_Scalar;
         procedure In_Out_Relaxed (X : in out Priv_Scalar) with
           Relaxed_Initialization => X,
           Global => null,
           Annotate => (GNATProve, Always_Return),
           Import;

      private
         pragma SPARK_Mode (Off);
         type Priv_Scalar is new Integer;
         C : constant Priv_Scalar := 0;
      end Nested;
      use Nested;

      Default : Priv_Scalar with Relaxed_Initialization;

   begin
      --  Checks pass when reading a default value

      if R = 0 then
         In_Out_Relaxed (Default);  --@INIT_BY_PROOF:PASS
      end if;
   end Test_Private_Scalar_Init_Ownership;

   --  Same test with a private type with predicates

   procedure Test_Private_Predicate is
      package Nested is
         type Priv_With_Pred is private;
         C : constant Priv_With_Pred;
         procedure In_Out_Relaxed (X : in out Priv_With_Pred) with
           Relaxed_Initialization => X,
           Global => null,
           Annotate => (GNATProve, Always_Return),
           Import;
         procedure Out_Relaxed (X : out Priv_With_Pred) with
           Relaxed_Initialization => X,
           Global => null,
           Annotate => (GNATProve, Always_Return),
           Import;

      private
         pragma SPARK_Mode (Off);
         type Priv_With_Pred is record
            F, G : Integer;
         end record with
           Predicate => F < G;
         C : constant Priv_With_Pred := (0, 1);
      end Nested;
      use Nested;

      procedure Test (No_Init : out Priv_With_Pred; Init : in out Priv_With_Pred) with --@INIT_BY_PROOF:FAIL
        Relaxed_Initialization => (No_Init, Init),
        Global => R
      is
      begin
         --  Init is initialized

         In_Out_Relaxed (Init); --@INIT_BY_PROOF:NONE

         --  No_Init is not initialized

         if R = 0 then
            In_Out_Relaxed (No_Init); --@INIT_BY_PROOF:FAIL
         elsif R = 1 then
            Out_Relaxed (No_Init); --@INIT_BY_PROOF:NONE
            In_Out_Relaxed (No_Init); --@INIT_BY_PROOF:PASS
         end if;

         --  No_Init should be initialized on exit
      end Test;

      type My_Rec is record
         F, G : Priv_With_Pred;
      end record;
      procedure In_Out_Rec (X : in out My_Rec) with
        Global => null,
        Annotate => (GNATProve, Always_Return),
        Import;
      procedure Out_Rec (X : out My_Rec) with
        Global => null,
        Annotate => (GNATProve, Always_Return),
        Import;
      procedure In_Out_Rec_Relaxed (X : in out My_Rec) with
        Relaxed_Initialization => X,
        Global => null,
        Annotate => (GNATProve, Always_Return),
        Import;
      procedure Out_Rec_Relaxed (X : out My_Rec) with
        Relaxed_Initialization => X,
        Global => null,
        Annotate => (GNATProve, Always_Return),
        Import;

      Default : Priv_With_Pred with Relaxed_Initialization;
      Init    : Priv_With_Pred := C with Relaxed_Initialization;
      Comp    : My_Rec with Relaxed_Initialization;

   begin
      --  Failed check when reading an uninitialized value

      if R = 0 then
         In_Out_Relaxed (Default);  --@INIT_BY_PROOF:FAIL
         In_Out_Relaxed (Default);  --@INIT_BY_PROOF:PASS

      --  Checks pass when reading a value initialized at declaration

      elsif R = 1 then
         In_Out_Relaxed (Init);  --@INIT_BY_PROOF:PASS
         In_Out_Relaxed (Init);  --@INIT_BY_PROOF:PASS

         --  Uninitialized value cannot be copied

         Init := Default;  --@INIT_BY_PROOF:FAIL

      --  Check pass if Default is initialized

      elsif R = 2 then
         Default := Init;
         In_Out_Relaxed (Default);  --@INIT_BY_PROOF:PASS
         In_Out_Relaxed (Default);  --@INIT_BY_PROOF:PASS

      --  No checks on OUT parameters, Default is initialized after the call

      elsif R = 3 then
         Out_Relaxed (Default);  --@INIT_BY_PROOF:NONE
         In_Out_Relaxed (Default);  --@INIT_BY_PROOF:PASS
         In_Out_Relaxed (Default);  --@INIT_BY_PROOF:PASS

      --  No checks on relaxed composite parameters

      elsif R = 4 then
         In_Out_Rec_Relaxed (Comp);  --@INIT_BY_PROOF:NONE
      elsif R = 5 then
         Out_Rec_Relaxed (Comp);  --@INIT_BY_PROOF:NONE

      --  No checks on OUT composite parameters

      elsif R = 6 then
         Out_Rec (Comp);  --@INIT_BY_PROOF:NONE

      --  Failed initialization check on uninitialized composite object

      elsif R = 7 then
         In_Out_Rec (Comp);  --@INIT_BY_PROOF:FAIL

      --  Complete initialization by component

      elsif R = 8 then
         Out_Relaxed (Comp.F);
         Out_Relaxed (Comp.G);
         In_Out_Rec (Comp);  --@INIT_BY_PROOF:PASS

      --  Partial initialization

      elsif R = 9 then
         Out_Relaxed (Comp.G);
         In_Out_Rec (Comp);  --@INIT_BY_PROOF:FAIL
      end if;
   end Test_Private_Predicate;

   procedure Test_Private_Predicate_Init is
      package Nested is
         type Priv_With_Pred is private with
           Default_Initial_Condition;
         C : constant Priv_With_Pred;
         procedure In_Out_Relaxed (X : in out Priv_With_Pred) with
           Relaxed_Initialization => X,
           Global => null,
           Annotate => (GNATProve, Always_Return),
           Import;

      private
         pragma SPARK_Mode (Off);
         type Priv_With_Pred is new Integer;
         C : constant Priv_With_Pred := 0;
      end Nested;
      use Nested;

      Default : Priv_With_Pred with Relaxed_Initialization;

   begin
      --  Checks pass when reading a default value

      if R = 0 then
         In_Out_Relaxed (Default);  --@INIT_BY_PROOF:PASS
      end if;
   end Test_Private_Predicate_Init;

   --  WITNESS : Same test with a private type whose full view is a record

   procedure Test_Private_Record is
      package Nested is
         type Priv_Rec is private;
         C : constant Priv_Rec;
         procedure In_Out_Relaxed (X : in out Priv_Rec) with
           Relaxed_Initialization => X,
           Global => null,
           Annotate => (GNATProve, Always_Return),
           Import;
         procedure Out_Relaxed (X : out Priv_Rec) with
           Relaxed_Initialization => X,
           Global => null,
           Annotate => (GNATProve, Always_Return),
           Import;

      private
         pragma SPARK_Mode (Off);
         type Priv_Rec is record
            F, G : Integer;
         end record;
         C : constant Priv_Rec := (0, 1);
      end Nested;
      use Nested;

      procedure Test (No_Init : out Priv_Rec; Init : in out Priv_Rec) with --@INIT_BY_PROOF:NONE
        Relaxed_Initialization => (No_Init, Init),
        Global => R
      is
      begin
         --  No initialization checks on relaxed parameters on records

         In_Out_Relaxed (Init); --@INIT_BY_PROOF:NONE

         if R = 0 then
            In_Out_Relaxed (No_Init); --@INIT_BY_PROOF:NONE
         elsif R = 1 then
            Out_Relaxed (No_Init); --@INIT_BY_PROOF:NONE
            In_Out_Relaxed (No_Init); --@INIT_BY_PROOF:NONE
         end if;
      end Test;

      type My_Rec is record
         F, G : Priv_Rec;
      end record;
      procedure In_Out_Rec (X : in out My_Rec) with
        Global => null,
        Annotate => (GNATProve, Always_Return),
        Import;
      procedure Out_Rec (X : out My_Rec) with
        Global => null,
        Annotate => (GNATProve, Always_Return),
        Import;
      procedure In_Out_Rec_Relaxed (X : in out My_Rec) with
        Relaxed_Initialization => X,
        Global => null,
        Annotate => (GNATProve, Always_Return),
        Import;
      procedure Out_Rec_Relaxed (X : out My_Rec) with
        Relaxed_Initialization => X,
        Global => null,
        Annotate => (GNATProve, Always_Return),
        Import;

      Default : Priv_Rec with Relaxed_Initialization;
      Init    : Priv_Rec := C with Relaxed_Initialization;
      Comp    : My_Rec with Relaxed_Initialization;

   begin
      --  No initialization checks on relaxed parameters on records

      if R = 0 then
         In_Out_Relaxed (Default);  --@INIT_BY_PROOF:NONE
         In_Out_Relaxed (Default);  --@INIT_BY_PROOF:NONE

      elsif R = 1 then
         In_Out_Relaxed (Init);  --@INIT_BY_PROOF:NONE
         In_Out_Relaxed (Init);  --@INIT_BY_PROOF:NONE
         Init := Default;  --@INIT_BY_PROOF:NONE

      elsif R = 2 then
         Default := Init;
         In_Out_Relaxed (Default);  --@INIT_BY_PROOF:NONE
         In_Out_Relaxed (Default);  --@INIT_BY_PROOF:NONE

      elsif R = 3 then
         Out_Relaxed (Default);  --@INIT_BY_PROOF:NONE
         In_Out_Relaxed (Default);  --@INIT_BY_PROOF:NONE
         In_Out_Relaxed (Default);  --@INIT_BY_PROOF:NONE

      elsif R = 4 then
         In_Out_Rec_Relaxed (Comp);  --@INIT_BY_PROOF:NONE
      elsif R = 5 then
         Out_Rec_Relaxed (Comp);  --@INIT_BY_PROOF:NONE

      elsif R = 6 then
         Out_Rec (Comp);  --@INIT_BY_PROOF:NONE

      --  Failed initialization check on uninitialized composite object

      elsif R = 7 then
         In_Out_Rec (Comp);  --@INIT_BY_PROOF:FAIL

      --  Initialization by component is not done as the OUT parameter of
      --  Out_Relaxed does not need to be initialized on exit.

      elsif R = 8 then
         Out_Relaxed (Comp.F);
         Out_Relaxed (Comp.G);
         In_Out_Rec (Comp);  --@INIT_BY_PROOF:FAIL

      elsif R = 9 then
         Out_Relaxed (Comp.G);
         In_Out_Rec (Comp);  --@INIT_BY_PROOF:FAIL
      end if;
   end Test_Private_Record;
begin
   null;
end Relaxed_Private;
