generic
   type Element_Type is abstract tagged private;
package Named_Lists is

   type Named_Element is new Element_Type with null record;

end Named_Lists;
