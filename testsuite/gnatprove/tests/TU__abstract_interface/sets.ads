package Sets
  with SPARK_Mode => On
Is
   subtype Element_Type is Natural;

   type Set is abstract tagged null record;

   function Empty return Set is abstract;

   function Union (Left, Right : Set) return Set is abstract;

   function Intersection (Left, Right : Set) return Set is abstract;

   function Unit_Set(Element : Element_Type) return Set is abstract;

   procedure Take(Element :    out Element_Type;
                  From    : in out Set) is abstract;
end Sets;
