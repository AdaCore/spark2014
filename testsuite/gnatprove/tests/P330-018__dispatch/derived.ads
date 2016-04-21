with Object; use Object;

package Derived is

   type D is new T with null record;

   function Is_Valid (X : D) return Boolean is (not X.B);

end Derived;
