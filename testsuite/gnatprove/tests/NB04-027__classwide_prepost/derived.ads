with Object; use Object;

package Derived is pragma Elaborate_Body;

   type D is new T with null record;

   procedure Create (X : out D) with
     Post'Class => not X.B;

   function Is_Valid (X : D) return Boolean is (not X.B);

   procedure Do_Stuff (X : in out D);

end Derived;
