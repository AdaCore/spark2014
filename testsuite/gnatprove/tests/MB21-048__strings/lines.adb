package body Lines is
   pragma SPARK_Mode(On);
   function Last_Lines
     (S : String; Size : Natural) return String
   is
      Pos : Integer := S'Last;
      Newline_Found : Integer := 0;
   begin
      if S = "" then
         return "";
      end if;

      --  The last line might end or not with a LF character
      if S (Pos) = ASCII.LF then
         Pos := Pos - 1;
      end if;

      while Newline_Found < Size and then Pos >= S'First loop
         pragma Loop_Invariant (Pos in S'Range);
         if S (Pos) = ASCII.LF then
            Newline_Found := Newline_Found + 1;
         end if;
         Pos := Pos - 1;
      end loop;

      --  Ignore last LF found
      if Newline_Found = Size then
         Pos := Pos + 1;
      end if;

      return S (Pos + 1 .. S'Last);
   end Last_Lines;
end Lines;
