with Gen; use Gen;

package Pkg is
   type T2 is private;

   package Nested is
      procedure Swap_T2 (X : in out T2);
   end;
private
   type T2 is new T1 with null record
      with Type_Invariant => T2.Aaa < T2.Bbb;
end;
