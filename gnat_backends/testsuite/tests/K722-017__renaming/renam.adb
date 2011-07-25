package body Renam is

   procedure O (M : out Integer)
   is
      PM : Integer renames M;

      function F return Integer
      is
      begin
         PM := 1;
         return PM;
      end F;
   begin
      null;
   end O;

   procedure P (M : Integer)
   is
      PM : Integer renames M;

      function F return Integer
      is
      begin
         return PM;
      end F;
   begin
      null;
   end P;

end Renam;
