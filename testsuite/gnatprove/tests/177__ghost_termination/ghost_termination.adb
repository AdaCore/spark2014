procedure Ghost_Termination with SPARK_Mode is
   function Rand (I : Integer) return Boolean with
     Global => null,
     Import;

   E : exception;

   procedure Term (I : Integer) with
     Ghost,
     Always_Terminates => True;

   procedure Term (I : Integer) is
   begin
      null;
   end Term;

   procedure Non_Term with
     Ghost,
     No_Return,
     Exceptional_Cases => (others => False),
     Always_Terminates => False;

   procedure Non_Term is
   begin
      loop
         null;
      end loop;
   end Non_Term;

   procedure Conditional_Non_Term (B : Boolean) with
     Ghost,
     Post => not B,
     Always_Terminates => not B;

   procedure Conditional_Non_Term (B : Boolean) is
   begin
      if B then
         loop
            null;
         end loop;
      end if;
   end Conditional_Non_Term;

   procedure Ghost_Caller with Ghost, Global => null;

   procedure Ghost_Caller is
   begin
      if Rand (1) then
         Conditional_Non_Term (True);
      else
         Non_Term;
      end if;
   end Ghost_Caller;

   procedure Non_Ghost_Caller_OK with Pre => Rand (1), Global => null;

   procedure Non_Ghost_Caller_OK is
   begin
      if Rand (1) then
         Conditional_Non_Term (False);
      else
         pragma Assert (False);
         Non_Term;
      end if;
   end Non_Ghost_Caller_OK;

   procedure Non_Ghost_Caller_Bad with Global => null;

   procedure Non_Ghost_Caller_Bad is
   begin
      if Rand (1) then
         Conditional_Non_Term (Rand (2)); -- call might not terminate (proof) @TERMINATION:FAIL
      else
         Non_Term; -- call might not terminate (flow)
      end if;
   end Non_Ghost_Caller_Bad;

   procedure Non_Ghost_Caller_Bad_2 with Global => null,
     Always_Terminates => not Rand (1);

   procedure Non_Ghost_Caller_Bad_2 is
   begin
      if Rand (1) then
         Conditional_Non_Term (Rand (2)); -- call might not terminate (proof)  @TERMINATION:FAIL
      else
         Non_Term; -- call might not terminate (flow)  @TERMINATION:FAIL
      end if;
   end Non_Ghost_Caller_Bad_2;

   type F is not null access function return Integer with Ghost;
   function Z return Integer is (0) with Ghost;

   V : F := Z'Access with Ghost;

   procedure Ghost_Caller_Fun with Ghost, Global => V;

   procedure Ghost_Caller_Fun is
   begin
      Term (V.all);
   end Ghost_Caller_Fun;

   procedure Non_Ghost_Caller_Fun with Global => V;

   procedure Non_Ghost_Caller_Fun is
   begin
      Term (V.all); -- call might not terminate (flow)  @TERMINATION:FAIL
   end Non_Ghost_Caller_Fun;

begin
   null;
end;
