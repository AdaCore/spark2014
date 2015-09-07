--private with Parent.Private1;
package Parent.Public1 is

   type Pub_Array1 is private;

   -- Can't use resources from private sibling here
   -- type Pub_Array3 is array (1 .. 3) of Parent.Private1.Private_Int;

   procedure Process (Value : in out Pub_Array1);

private
   type Pub_Array1 is array (1 .. 3) of Parent_Int;
   -- The next line uses a type from the visible part of a private sibling
   --type Pub_Array2 is array (1 .. 3) of Parent.Private1.Private_Int;
end Parent.Public1;
