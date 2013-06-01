with Super;

package Toto is
   type Bounded_String is private;

   function Length (Source : Bounded_String) return Natural;

private

   type Bounded_String is new Super.Super_String;

   function Length
     (Source : Bounded_String) return Natural
      renames Super_Length;

end Toto;
