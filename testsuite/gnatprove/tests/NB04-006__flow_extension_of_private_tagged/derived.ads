with Base; use Base;
package Derived is pragma Elaborate_Body;
   type Derived_T is new Base_T with record
      B : Boolean;
   end record;
   overriding function Make (B : Boolean) return Derived_T;
end Derived;
