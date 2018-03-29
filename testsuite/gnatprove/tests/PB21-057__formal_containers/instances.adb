with Ada.Text_IO; use Ada.Text_IO;

package body Instances with SPARK_Mode => Off Is

   procedure Fold_Lasts (V : in out Vectors.Vector)
   is
   begin
      Replace_Element
        (V,
         Length (V) - 1,
         Element (V, Length (V) - 1) + Element (V, Length (V)));
      Delete_Last(V);
   end Fold_Lasts;


   protected body Data is
      procedure Push (V : Integer) is
      begin
         Append (Vect, V);
      end Push;

      procedure Add (V : Integer) is
      begin
         Replace_Element(Vect, 1, Element (Vect, 1) + V);
         Put_Line (Element (Vect, 1)'Img);
      end Add;
   end Data;

   task body T is
   begin
      Data.Add (1);
   end T;

end Instances;
