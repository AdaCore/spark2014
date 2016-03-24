with Object; use Object;

package Derived is

   type D is new T with null record;

   procedure Create (X : out D) with
     Post'Class => not X.B;

end Derived;
