generic
   type Index is (<>);
   type Item is private;
package Gen is

   type List is array (Index range <>) of Item;

   function Ident (T : List) return List;

end Gen;
