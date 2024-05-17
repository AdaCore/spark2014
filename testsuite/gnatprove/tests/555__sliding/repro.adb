procedure Repro
  with SPARK_Mode
is

   package Pkg is
      type T (<>) is private;
      procedure Outside (X : out T);
   private
      type T is array (Integer range <>) of Boolean;
   end;

   package body Pkg is
      procedure Inside (X : out T) with Depends => (X => X) is
      begin
         X := (others => False);
      end;

      procedure Outside (X : out T) renames Inside;
   end;

begin
   null;
end;
