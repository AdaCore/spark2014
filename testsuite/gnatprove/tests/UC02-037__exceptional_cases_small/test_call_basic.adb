procedure Test_Call_Basic
  with
    SPARK_Mode => On
is

   E1 : exception;
   E2 : exception;
   E3 : exception;

   procedure Raise_E1_E2_Or_E3 (A, B : Boolean) with
     No_Return,
     Exceptional_Cases => (E1 => A and B, E2 => not B, E3 => not A);

   procedure Raise_E1_E2_Or_E3 (A, B : Boolean) is
   begin
      if not B then
         raise E2;
      elsif not A then
         raise E3;
      else
         raise E1;
      end if;
   end Raise_E1_E2_Or_E3;

   procedure Raise_E1_Only_Bad_1 (B : Boolean) with
     No_Return,
     Exceptional_Cases => (E1 => True);

   procedure Raise_E1_Only_Bad_1 (B : Boolean) is
   begin
      Raise_E1_E2_Or_E3 (B, True);
   end Raise_E1_Only_Bad_1;

   procedure Raise_E1_Only_1 (B : Boolean) with
     No_Return,
     Pre => B,
     Exceptional_Cases => (E1 => True);

   procedure Raise_E1_Only_1 (B : Boolean) is
   begin
      Raise_E1_E2_Or_E3 (B, True);
   end Raise_E1_Only_1;

   procedure Raise_E1_Only_Bad_2 (B : Boolean) with
     No_Return,
     Exceptional_Cases => (E1 => True);

   procedure Raise_E1_Only_Bad_2 (B : Boolean) is
   begin
      if B then
         raise E1;
      else
         raise E2;
      end if;
   end Raise_E1_Only_Bad_2;

   procedure Raise_E1_Only_2 (B : Boolean) with
     No_Return,
     Exceptional_Cases => (E1 => True);

   procedure Raise_E1_Only_2 (B : Boolean) is
   begin
      if B then
         Raise_E1_E2_Or_E3 (B, True);
      else
         raise E1;
      end if;
   end Raise_E1_Only_2;

   procedure Raise_E1_Or_E2_Bad_1 (A, B : Boolean) with
     No_Return,
     Exceptional_Cases => (E1 | E2 => True);

   procedure Raise_E1_Or_E2_Bad_1 (A, B : Boolean) is
   begin
      Raise_E1_E2_Or_E3 (A, B);
   end Raise_E1_Or_E2_Bad_1;

   procedure Raise_E1_Or_E2_1 (A, B : Boolean) with
     No_Return,
     Pre => A,
     Exceptional_Cases => (E1 | E2 => True);

   procedure Raise_E1_Or_E2_1 (A, B : Boolean) is
   begin
      Raise_E1_E2_Or_E3 (A, B);
   end Raise_E1_Or_E2_1;

   procedure Raise_E1_Or_E2_Bad_2 (A, B : Boolean) with
     No_Return,
     Exceptional_Cases => (E1 | E2 => True);

   procedure Raise_E1_Or_E2_Bad_2 (A, B : Boolean) is
   begin
      if not B then
         raise E2;
      elsif not A then
         raise E3;
      else
         raise E1;
      end if;
   end Raise_E1_Or_E2_Bad_2;

   procedure Raise_E1_Or_E2_2 (A, B : Boolean) with
     No_Return,
     Exceptional_Cases => (E1 | E2 => True);

   procedure Raise_E1_Or_E2_2 (A, B : Boolean) is
   begin
      if A then
         Raise_E1_E2_Or_E3 (A, B);
      else
         raise E1;
      end if;
   end Raise_E1_Or_E2_2;

begin
   null;
end;
