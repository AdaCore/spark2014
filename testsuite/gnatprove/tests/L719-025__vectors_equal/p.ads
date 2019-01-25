with Ada.Containers.Formal_Vectors;
with Ada.Containers; use Ada.Containers;
package P is pragma SPARK_Mode (On);

   type Element_Type is new Integer range 1 .. 100;

   type Index_Type is new Integer range 1 .. 100;

   package My_Vectors is new Ada.Containers.Formal_Vectors
     (Index_Type, Element_Type);
   use My_Vectors; use Formal_Model;

   procedure Nearly_Identity_1 (L : in out Vector; I : Extended_Index) with
     Pre => Length (L) < L.Capacity and
     First_Index (L) <= I and I <= Last_Index (L) + 1,
     Post => Model (L) = Model (L)'Old;

   procedure Nearly_Identity_2 (L : in out Vector; I : Index_Type) with
     Pre => First_Index (L) <= I and I = Last_Index (L),
     Post => Model (L) = Model (L)'Old;

   procedure Identity_Swap (L : in out Vector; I1, I2 : Index_Type) with
     Pre => First_Index (L) <= I1 and I1 <= Last_Index (L) and
        First_Index (L) <= I2 and I2 <= Last_Index (L),
     Post => Model (L) = Model (L)'Old;

end P;
