package body Ex is


   function Get_Int (I : Integer) return Integer is
   begin
      return (I + 1);
   end Get_Int;

   procedure Bug (X : in out Integer) is
   begin
      X := X + Get_Int (4);
   end Bug;

end Ex;
