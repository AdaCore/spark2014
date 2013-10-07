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

  procedure Move (Dest : out IntArray; Src : in out IntArray) is
     Src_Old : constant Intarray := Src;
  begin
     for Index in Dest'Range loop
        Dest (Index) := Src (Index);
        Src (Index) := 0;

        pragma Loop_Invariant ((for all J in Dest'First .. Index =>
                          Dest (J) = Src_Old (J)) and
                         (for all J in Index + 1 .. Dest'Last =>
                            Src (J) = Src_Old (J)));
     end loop;
  end Move;

end S;

