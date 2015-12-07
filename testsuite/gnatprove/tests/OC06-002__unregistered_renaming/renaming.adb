package body Renaming is

   function A return Boolean is (True);

   function B return Boolean renames A;

   function C return Boolean is (B);

end Renaming;
