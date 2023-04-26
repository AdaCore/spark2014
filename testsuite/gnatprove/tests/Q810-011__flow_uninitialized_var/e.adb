procedure E (Arg : Boolean) with No_Return is
   Uninitialized : Boolean;
   procedure Crash (Reason : Boolean) with
     Exceptional_Cases => (others => False),
     No_Return,
     Global => null;

   pragma Import (C, Crash);

begin
   Crash (Uninitialized and Arg);
end E;
