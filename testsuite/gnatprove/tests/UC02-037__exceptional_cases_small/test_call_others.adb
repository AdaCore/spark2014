procedure Test_Call_Others
  with
    SPARK_Mode => On
is

   E1 : exception;
   E2 : exception;
   E3 : exception;

   procedure No_E1_Bad (A : Boolean) with
     No_Return,
     Exceptional_Cases => (E1 => False, others => True);

   procedure No_E1_Bad (A : Boolean) is
   begin
      if A then
         raise E1;
      else
         raise E2;
      end if;
   end No_E1_Bad;

   procedure No_E1_Ok (A : Boolean) with
     No_Return,
     Exceptional_Cases => (E1 => False, others => True);

   procedure No_E1_Ok (A : Boolean) is
   begin
      if A then
         raise E3;
      else
         raise E2;
      end if;
   end No_E1_Ok;

   procedure No_E1_Bad_2 (A : Boolean) with
     No_Return,
     Exceptional_Cases => (E1 => False, E2 => not A, others => True);

   procedure No_E1_Bad_2 (A : Boolean) is
   begin
      if A then
         raise E1;
      else
         raise E2;
      end if;
   end No_E1_Bad_2;

   procedure No_E1_Ok_2 (A : Boolean) with
     No_Return,
     Exceptional_Cases => (E1 => False, E2 => not A, others => True);

   procedure No_E1_Ok_2 (A : Boolean) is
   begin
      if A then
         raise E3;
      else
         raise E2;
      end if;
   end No_E1_Ok_2;

   procedure Raise_Anything (A, B : Boolean) with
     No_Return,
     Exceptional_Cases => (others => True);

   procedure Raise_Anything (A, B : Boolean) is
   begin
      if A then
         raise E1;
      elsif B then
         raise E2;
      else
         raise E3;
      end if;
   end Raise_Anything;

   procedure No_E1_Bad_3 (A : Boolean) with
     No_Return,
     Exceptional_Cases => (E1 => not A, others => True);

   procedure No_E1_Bad_3 (A : Boolean) is
   begin
      if A then
         Raise_Anything (True, True);
      else
         raise E2;
      end if;
   end No_E1_Bad_3;

   procedure No_E1_Ok_3 (A : Boolean) with
     No_Return,
     Exceptional_Cases => (E1 => A, others => True);

   procedure No_E1_Ok_3 (A : Boolean) is
   begin
      if A then
         Raise_Anything (True, True);
      else
         raise E2;
      end if;
   end No_E1_Ok_3;

begin
   null;
end;
