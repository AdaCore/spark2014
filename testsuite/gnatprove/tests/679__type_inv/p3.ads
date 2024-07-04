package P3 is
   type I is private;
   function OK (X : I) return Boolean;
private
   type I is new Integer with Type_Invariant => I /= 0, Default_Value => 1;
   function OK (X : I) return Boolean is (X /= 0);
end P3;
