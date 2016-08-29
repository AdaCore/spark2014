package Sh_Buffers is

   type Text_Position is private;
   --  Represent a position in a buffer.

   Null_Text_Position : constant Text_Position;
   --  An invalid text position

private
   type Text_Position is record
      Offset : Natural;
      Line   : Natural;
   end record;

   Null_Text_Position : constant Text_Position := (0, 0);

end Sh_Buffers;
