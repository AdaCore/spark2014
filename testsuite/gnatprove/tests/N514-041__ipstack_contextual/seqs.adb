procedure Seqs is
   function Seq_Le (X, Y : Integer) return Boolean;
   function Seq_Le (X, Y : Integer) return Boolean is (X <= Y);
   X, Y : Integer := 0;
begin
   pragma Assert (Seq_Le (X, Y));
end Seqs;
