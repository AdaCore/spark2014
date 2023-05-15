with Ada.Containers;

package Types with SPARK_Mode is
   type T is private;

   function "=" (X, Y : T) return Boolean with
     Import,
     Global => null;


   function Equivalent (X, Y : T) return Boolean with
     Import,
     Global => null;


   function "<" (X, Y : T) return Boolean with
     Import,
     Global => null;


   function Hash (X : T) return Ada.Containers.Hash_Type with
     Import,
     Global => null;


   function F (X : T) return T with
     Import,
     Global => null;

private
   pragma SPARK_Mode (Off);
   type T is new Integer;
end Types;
