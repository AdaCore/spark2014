package body Generic_Bar with
  SPARK_Mode
 is

   procedure Initialize_Element (Context : out Element_Context_Type) is
   begin
      Element_Initialize (Context);
   end Initialize_Element;

   function Valid_Element (Context : Element_Context_Type) return Boolean is
      (Element_Valid (Context));

end Generic_Bar;
