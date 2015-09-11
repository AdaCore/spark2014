package body Integrity_Proved is

   Max : Natural := 0;  --  max value seen
   Snd : Natural := 0;  --  second max value seen

   function Invariant return Boolean is (Snd <= Max);

end Integrity_Proved;
