package body Renaming is

   function A (X : Integer) return Boolean is (X /= 0) with Pre => X /= 0;

   function B (X : Integer) return Boolean renames A;

   function C (X : Integer) return Boolean is (B (X));

end Renaming;
