-- Bus Dumping
with Ada.Text_Io;
separate(Bus)
procedure Dump(M : in out Message)
is
   package Integer_Io is new Ada.Text_IO.Integer_Io(Bus.Word);
   W : Bus.Word;
begin
   Ada.Text_Io.Put_Line("valid=" & Boolean'Image(M.Valid) &
                        "  fresh=" & Boolean'Image(M.Fresh));
   for Idx in Word_Index loop
      W := M.Data(Idx);
      Integer_Io.Put(Item => W,
                         Width => 9,
                         Base => 16);
      if (Idx mod 4 = 0) or Idx = Word_Index'Last then
         Ada.Text_Io.Put_Line(" ");
      end if;
   end loop;
end Dump;
