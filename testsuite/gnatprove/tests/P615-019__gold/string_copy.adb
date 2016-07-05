package body String_Copy is

   procedure Copy (Dest : out String; Src : in String) is
   begin
      if Dest'Length < Src'Length then
         raise Constraint_Error;
      end if;
      --  copies Src into Dest here
   end Copy;

   procedure Copy2 (Dest : out String; Src : in String) is
   begin
      Copy (Dest, Src);
   end Copy2;

end String_Copy;
