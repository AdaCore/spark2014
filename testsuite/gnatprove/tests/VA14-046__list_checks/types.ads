with Ada.Containers;

package Types with SPARK_Mode is
   type T is private;

   function "=" (X, Y : T) return Boolean with
     Import,
     Global => null,
     Annotate => (GNATprove, Always_Return);

   function Equivalent (X, Y : T) return Boolean with
     Import,
     Global => null,
     Annotate => (GNATprove, Always_Return);

   function "<" (X, Y : T) return Boolean with
     Import,
     Global => null,
     Annotate => (GNATprove, Always_Return);

   function Hash (X : T) return Ada.Containers.Hash_Type with
     Import,
     Global => null,
     Annotate => (GNATprove, Always_Return);

   function F (X : T) return T with
     Import,
     Global => null,
     Annotate => (GNATprove, Always_Return);
private
   pragma SPARK_Mode (Off);
   type T is new Integer;
end Types;
