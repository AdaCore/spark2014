generic
   type Element_Context_Type is private;
   with procedure Element_Initialize (Context : out Element_Context_Type);
   with function Element_Valid (Context : Element_Context_Type) return Boolean;
package Generic_Bar with
  SPARK_Mode
 is

   procedure Initialize_Element (Context : out Element_Context_Type) with
     Post => Element_Valid (Context) and then Context in Element_Context_Type;

   function Valid_Element (Context : Element_Context_Type) return Boolean;

end Generic_Bar;
