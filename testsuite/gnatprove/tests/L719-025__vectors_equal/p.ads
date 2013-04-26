with Ada.Containers.Formal_Vectors;
with Ada.Containers; use Ada.Containers;
package P is

   type Element_Type is new Integer range 1 .. 100;

   type Index_Type is new Integer range 1 .. 100;

   function My_Eq (I1 : Element_Type; I2 : Element_Type) return Boolean is
     (I1 = I2);

   package My_Vectors is new Ada.Containers.Formal_Vectors
     (Index_Type, Element_Type, My_Eq);
   use My_Vectors;

   procedure Identity_1 (L : in out Vector; Cu : in out Cursor) with
     Pre => Length (L) < L.Capacity and
     (Has_Element (L, Cu) or Cu = No_Element),
     Post => L = L'Old and Cu = No_Element;

   procedure Identity_2 (L : in out Vector; Cu : in out Cursor) with
     Pre => Has_Element (L, Cu),
     Post => L = L'Old;

   procedure Identity_Swap (L : in out Vector; Cu1 : Cursor; Cu2 : Cursor) with
     Pre => Has_Element (L, Cu1) and Has_Element (L, Cu2),
     Post => L = L'Old;

end P;
