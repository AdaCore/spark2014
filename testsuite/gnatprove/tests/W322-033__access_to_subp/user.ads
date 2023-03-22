pragma Ada_2022;
pragma SPARK_Mode;
package User is

   type Ptr is access all Integer;

   function State (I : Integer) return Boolean
   with
      Ghost,
      Import,
      Global   => null,
      Annotate => (GNATprove, Always_Return);

   type T is access function (P : Ptr) return Integer with
     Post => State (P.all);

   function Func (P : Ptr) return Integer;

   X : T := Func'Access;

end User;
