with Formal_Vectors;
package Use_Formal_Vectors with SPARK_Mode is

   type Element_Type is not null access Integer;
   subtype Element_Model is Integer;
   function Model (X : Element_Type) return Element_Model is (X.all);
   function "=" (X, Y : Element_Type) return Boolean is (X.all = Y.all);
   function Copy (X : Element_Type) return Element_Type
     with Post => Model (Copy'Result) = Model (X), Annotate => (GNATprove, Always_Return);

   package My_Vect is new Formal_Vectors
     (Element_Type  => Element_Type,
      Element_Model => Element_Model);

end Use_Formal_Vectors;
