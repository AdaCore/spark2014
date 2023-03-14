procedure Test_Ownership_Illegal with SPARK_Mode is
   pragma Annotate (GNATprove, Ownership); --  << KO, expect 3 or 4 params
   pragma Annotate (GNATprove, Ownership, "U", "U", "U"); --  << KO, expect 3 or 4 params
   pragma Annotate (GNATprove, Ownership, "U", "U"); --  << KO, last param should be an entity

   function F return Boolean with
     Import,
     Annotate => (GNATprove, Ownership, True); --  << KO, 3rd param should be a string

   procedure P2 with
     Import,
     Annotate => (GNATprove, Ownership); --  << KO, only on types or functions

   type Int is range -100 .. 100 with
     Annotate => (GNATprove, Ownership); --  << KO, only on private types

   package Nested1 is
      type T is private with
        Annotate => (GNATprove, Ownership); --  << KO, full view shall not be in SPARK
   private
      type T is null record;
   end Nested1;

   package Nested2 is
      type T1 is private with
        Annotate => (GNATprove, Ownership, "Needs_Reclamation"); --  << OK
      type T2 is tagged private with
        Annotate => (GNATprove, Ownership, "Needs_Reclamation"); --  << OK
      function P1 (X : T2) return Boolean with
        Import,
        Annotate => (GNATprove, Ownership, "Is_Reclaimed"); --  << KO, class wide type expected
      function P2 (X : T2'Class) return Boolean with
        Import,
        Annotate => (GNATprove, Ownership, "Is_Reclaimed"); --  << OK
      type T3 (D : Boolean) is private with
        Annotate => (GNATprove, Ownership); --  << OK
   private
      pragma SPARK_Mode (Off);
      type T1 is null record;
      type T2 is tagged null record;
      type T3 (D : Boolean) is null record;
   end Nested2;
   use Nested2;

   package Nested3 is
      subtype S is T1 with
        Annotate => (GNATprove, Ownership); --  << KO, only on new types
      type T4 is private with
        Annotate => (GNATprove, Ownership, "U"); --  << KO, wrong 3rd param
      type T5 is new T2 with record
         F : Integer;
      end record with
        Annotate => (GNATprove, Ownership); --  << KO, only on new types
      type T6 is new T2 with private with
        Annotate => (GNATprove, Ownership); --  << KO, only on new types
   private
      pragma SPARK_Mode (Off);
      type T4 is null record;
      type T6 is new T2 with null record;
   end Nested3;

   function F_out (X : T1) return Boolean with
     Import,
     Annotate => (GNATprove, Ownership, "Needs_Reclamation"); -- << KO, needs to be in same list of declaration as type

   package Nested4 is

      type T7 is private with
        Annotate => (GNATprove, Ownership, "Needs_Reclamation"); --  << OK

      package Inner is
         function F0 (X : T7) return Boolean with
           Import,
           Annotate => (GNATprove, Ownership, "Needs_Reclamation"); --  << KO, not in same list of declarations as type
      end Inner;

      function F1 (X : T7) return Boolean with
        Import,
        Annotate => (GNATprove, Ownership); --  << KO, third parameter required

      function F2 (X : T7) return Boolean with
        Import,
        Annotate => (GNATprove, Ownership, "U"); --  << KO, third parameter should be Needs_Reclamation or Is_Reclaimed

      function F3 (X : T7) return Boolean with
        Import,
        Annotate => (GNATprove, Ownership, "Needs_Reclamation"); --  << OK

      function F4 (X : T7) return Boolean with
        Import,
        Annotate => (GNATprove, Ownership, "Is_Reclaimed"); --  << KO, not 2 ownership functions with same type

      function F5 (X : T7) return Integer with
        Import,
        Annotate => (GNATprove, Ownership, "Is_Reclaimed"); --  << KO, ownership function should return boolean

      function F6 return Boolean with
        Import,
        Annotate => (GNATprove, Ownership, "Is_Reclaimed"); --  << KO, ownership function should have 1 parameter

      function F7 (X, Y : T7) return Boolean with
        Import,
        Annotate => (GNATprove, Ownership, "Is_Reclaimed"); --  << KO, ownership function should have 1 parameter

      function F8 (X : Integer) return Boolean with
        Import,
        Annotate => (GNATprove, Ownership, "Is_Reclaimed"); --  << KO, parameter of ownership function shall have ownership

      function F9 (X : T3) return Boolean with
        Import,
        Annotate => (GNATprove, Ownership, "Is_Reclaimed"); --  << KO, parameter of ownership function shall need reclamation

      G : Boolean := True;

      function F10 (X : T7) return Boolean with
        Import,
        Global => (Input => G),
        Annotate => (GNATprove, Ownership, "Is_Reclaimed"); --  << KO, ownership function shall not access global data
   private
      pragma SPARK_Mode (Off);
      type T7 is null record;
   end Nested4;

begin
   null;
end;
