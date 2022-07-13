procedure Test_Move with SPARK_Mode is

   function Rand (X : Integer) return Boolean with
     Import,
     Global => null,
     Annotate => (GNATprove, Always_Return);

   package Nested is
      type T is private with
        Default_Initial_Condition,
        Annotate => (GNATprove, Ownership);
      type U is tagged private with
        Default_Initial_Condition,
        Annotate => (GNATprove, Ownership);
   private
      pragma SPARK_Mode (Off);
      type T is null record;
      type U is tagged null record;
   end Nested;
   use Nested;

   package Nested_Ext is
      type V is new U with record
         F : Integer := 0;
      end record;
   end Nested_Ext;
   use Nested_Ext;

   procedure Test1 with
     Global => null
   is
      type Two_T is record
         F1, F2 : T;
      end record;

      function Read (X : Two_T) return Boolean with
        Import,
        Global => null,
        Annotate => (GNATprove, Always_Return);

      X : Two_T;
      Y : Two_T := X;

   begin
      if Rand (0) then
         pragma Assert (Read (X)); -- Error
      elsif Rand (1) then
         pragma Assert (Read (Y));
      end if;

      X.F1 := Y.F1;

      if Rand (2) then
         pragma Assert (Read (X)); -- Error
      elsif Rand (3) then
         pragma Assert (Read (Y)); -- Error
      end if;

      X.F2 := Y.F2;

      if Rand (4) then
         pragma Assert (Read (X));
      elsif Rand (5) then
         pragma Assert (Read (Y)); -- Error
      end if;
   end Test1;

   procedure Test2 with
     Global => null
   is
      type Two_U is record
         F1, F2 : U;
      end record;

      function Read (X : Two_U) return Boolean with
        Import,
        Global => null,
        Annotate => (GNATprove, Always_Return);

      X : Two_U;
      Y : Two_U := X;

   begin
      if Rand (0) then
         pragma Assert (Read (X)); -- Error
      elsif Rand (1) then
         pragma Assert (Read (Y));
      end if;

      X.F1 := Y.F1;

      if Rand (2) then
         pragma Assert (Read (X)); -- Error
      elsif Rand (3) then
         pragma Assert (Read (Y)); -- Error
      end if;

      X.F2 := Y.F2;

      if Rand (4) then
         pragma Assert (Read (X));
      elsif Rand (5) then
         pragma Assert (Read (Y)); -- Error
      end if;
   end Test2;

   procedure Test3 with
     Global => null
   is
      type Two_V is record
         F1, F2 : V;
      end record;

      function Read (X : Two_V) return Boolean with
        Import,
        Global => null,
        Annotate => (GNATprove, Always_Return);

      procedure Havoc (X : in out Two_V) with
        Import,
        Global => null,
        Annotate => (GNATprove, Always_Return);

      X : Two_V;
      Y : Two_V := X;

   begin
      Havoc (Y);

      X.F1.F := 1;
      X.F2.F := 2;

      if Rand (0) then
         pragma Assert (X.F1.F = 0);
         pragma Assert (X.F2.F = 0);
         pragma Assert (Read (X)); -- Error
      elsif Rand (1) then
         pragma Assert (Read (Y));
      end if;

      X.F1 := Y.F1;

      if Rand (2) then
         pragma Assert (X.F1.F = 0);
         pragma Assert (X.F2.F = 0);
         pragma Assert (Read (X)); -- Error
      elsif Rand (3) then
         pragma Assert (Y.F1.F = 0);
         pragma Assert (Y.F2.F = 0);
         pragma Assert (Read (Y)); -- Error
      end if;

      X.F2 := Y.F2;

      if Rand (4) then
         pragma Assert (Read (X));
      elsif Rand (5) then
         pragma Assert (Y.F1.F = 0);
         pragma Assert (Y.F2.F = 0);
         pragma Assert (Read (Y)); -- Error
      end if;
   end Test3;

begin
   null;
end Test_Move;
