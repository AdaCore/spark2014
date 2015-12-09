package Renaming is

   function B (X : Integer) return Boolean with Pre => X /= 0;

   function C (X : Integer) return Boolean with Pre => X /= 0;

end Renaming;
