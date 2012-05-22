package body S is

   function Contains (Table : IntArray; Value : Integer) return Boolean is
   begin
      for Index in Table'Range loop
         pragma Assert (for all J in Table'First .. Index - 1 =>
                          Table (J) /= Value);

         if Table(Index) = Value then
            return True;
         end if;
      end loop;

      return False;
   end Contains;

   procedure Test_Index is
      T : Integer := 0;
   begin
      for Index in 1 .. 10 loop
         pragma Assert (T = Index - 1);
         T := Index;
      end loop;
      pragma Assert (T = 10);
      T := 11;
      for Index in reverse 1 .. 10 loop
         pragma Assert (T = Index + 1);
         T := Index;
      end loop;
      pragma Assert (T = 1);
   end Test_Index;

   procedure Move (Dest, Src : out IntArray) is
      Src_Old : constant IntArray := Src;
   begin
      for Index in Dest'Range loop
         pragma Assert ((for all J in Dest'First .. Index - 1 =>
                          Dest (J) = Src_Old (J)) and
                        (for all J in Index .. Dest'Last =>
                          Src (J) = Src_Old (J)));

         Dest (Index) := Src (Index);
         Src (Index) := 0;
      end loop;
   end Move;

   procedure Move2 (Dest, Src : out IntArray) is
      Src_Old : constant IntArray := Src;
   begin
      for Index in reverse Dest'Range loop
         pragma Assert ((for all J in Index + 1 .. Dest'Last =>
                          Dest (J) = Src_Old (J)) and
                        (for all J in Dest'First .. Index =>
                          Src (J) = Src_Old (J)));

         Dest (Index) := Src (Index);
         Src (Index) := 0;
      end loop;
   end Move2;
end S;

