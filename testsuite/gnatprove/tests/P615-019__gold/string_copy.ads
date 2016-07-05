package String_Copy is

   procedure Copy (Dest : out String; Src : in String);
   --  Copy Src into Dest. Require Dest length to be no less than Src length,
   --  otherwise an exception is raised.

   procedure Copy2 (Dest : out String; Src : in String)
     with Pre => Dest'Length >= Src'Length;
   --  Copy Src into Dest.

end String_Copy;
