package body S is

   function Contains (Table : IntArray; Value : Integer) return Boolean is
   begin
      for Index in Table'Range loop
         pragma Loop_Invariant (for all J in Table'First .. Index - 1 =>
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
         pragma Loop_Invariant (T = Index - 1);
         T := Index;
      end loop;
      pragma Assert (T = 10);
      T := 11;
      for Index in reverse 1 .. 10 loop
         pragma Loop_Invariant (T = Index + 1);
         T := Index;
      end loop;
      pragma Assert (T = 1);
   end Test_Index;

   procedure Move (Dest : out IntArray; Src : in out IntArray) is
   begin
      for Index in Dest'Range loop
         Dest (Index) := Src (Index);
         Src (Index) := 0;

         pragma Loop_Invariant ((for all J in Dest'First .. Index =>
                                   Dest (J) = Src'Loop_Entry (J)) and
                                  (for all J in Index + 1 .. Dest'Last =>
                                     Src (J) = Src'Loop_Entry (J)));
      end loop;
   end Move;

   procedure Move2 (Dest : out IntArray; Src : in out IntArray) is
   begin
      for Index in reverse Dest'Range loop
         Dest (Index) := Src (Index);
         Src (Index) := 0;

         pragma Loop_Invariant ((for all J in Index .. Dest'Last =>
                                   Dest (J) = Src'Loop_Entry (J)) and
                                  (for all J in Dest'First .. Index - 1 =>
                                     Src (J) = Src'Loop_Entry (J)));
      end loop;
   end Move2;
end S;

