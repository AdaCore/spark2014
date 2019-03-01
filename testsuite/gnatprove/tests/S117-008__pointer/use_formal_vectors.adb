package body Use_Formal_Vectors with SPARK_Mode is

   function Copy (X : Element_Type) return Element_Type is
      Res : constant Element_Type := new Integer'(X.all);
   begin
      return Res;
   end Copy;

end Use_Formal_Vectors;
