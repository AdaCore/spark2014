package InvertInjection is

   N : constant Natural := 100;
   subtype Element is Natural range 1 .. 100;
   type ElementArray is array (Element) of Element;

   procedure Invert (A : ElementArray; B : in out ElementArray)
   with
     Pre  => (for all I in Element'Range =>
                (for all J in Element'Range => (if A (I) = A (J) then I = J)))
               and
             (for all I in Element'Range =>
                not (for all J in Element'Range => (A (J) /= I))),
     Post => (for all I in Element'Range =>
                (for all J in Element'Range => (if B (I) = B (J) then I = J)));

end InvertInjection;
