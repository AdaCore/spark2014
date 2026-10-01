generic
   type Element is private;
package Gen
  with SPARK_Mode, Preelaborate
is
   type Pair is record
      First  : Element;
      Second : Element;
   end record;
   function Make (A, B : Element) return Pair is ((First => A, Second => B));
   function Get_First  (P : Pair) return Element is (P.First);
   function Get_Second (P : Pair) return Element is (P.Second);
end Gen;
