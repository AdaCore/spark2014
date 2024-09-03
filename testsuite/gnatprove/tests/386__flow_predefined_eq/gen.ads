generic
   type Element_Type (<>) is private;
   with function "=" (Left, Right : Element_Type) return Boolean is <>;
package Gen is
   procedure Test (Param : Element_Type) with Post => False;
end Gen;
