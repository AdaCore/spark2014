pragma Unevaluated_Use_Of_Old(Allow);
procedure String_Old with SPARK_Mode is
   procedure Do_Nothing (S : in out String) with
     Contract_Cases =>
       (True => (for all Idx in S'Range => S(Idx) = S(S'Range)'Old(Idx)));

   procedure Do_Nothing (S : in out String) is
   begin
      null;
   end Do_Nothing;

   S : String := "hello world!";
begin
   Do_Nothing (S);
end String_Old;
