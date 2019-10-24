generic
   Size : Natural;
package Test
with
   Abstract_State => State
is

   subtype Index_Type is Natural range 0 .. Size;

private

   function Root return Index_Type;

   Count : array (Index_Type) of Natural
     := (others => 0)
   with
      Part_Of => State;

   procedure Clear (I : Index_Type)
   with
      Post => Root = Root'Old;

end Test;
