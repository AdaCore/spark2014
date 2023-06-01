procedure Ghost_Exceptions with SPARK_Mode is
   function Rand (I : Integer) return Boolean with
     Global => null,
     Import;

   E : exception;

   procedure Conditional_Raise (B : Boolean) with
     Ghost,
     Post => not B,
     Exceptional_Cases => (E => B);

   procedure Conditional_Raise (B : Boolean) is
   begin
      if B then
         raise E;
      end if;
   end Conditional_Raise;

   procedure Ghost_Caller (X : out Integer) with Ghost, Global => null;

   procedure Ghost_Caller (X : out Integer) is
   begin
      Conditional_Raise (True);
      pragma Assert (False);
   exception
      when E =>
         X := 0;
   end Ghost_Caller;

   procedure Non_Ghost_Caller_OK (X : out Integer) with Global => null;

   procedure Non_Ghost_Caller_OK (X : out Integer) is
   begin
      Conditional_Raise (False);
      X := 0;
   end Non_Ghost_Caller_OK;

   procedure Non_Ghost_Caller_Bad (X : out Integer) with Global => null;

   procedure Non_Ghost_Caller_Bad (X : out Integer) is
   begin
      Conditional_Raise (Rand (1)); -- @RAISE:FAIL
      X := 0;
   exception
      when E =>
         null;
   end Non_Ghost_Caller_Bad;

begin
   null;
end;
