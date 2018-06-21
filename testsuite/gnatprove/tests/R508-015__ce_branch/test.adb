package body Test with SPARK_Mode
is

   function Test_If (A : Integer) return Integer
     with Post => Test_If'Result = 522 --  @COUNTEREXAMPLE
   is
      B : Integer;
   begin
      if A > 3 then
         B := 5;
      elsif A < - 18 then
         B := 18;
      else
         B := 82;
      end if;
      return B;
   end Test_If;

   function Test_Case  (A : Integer) return Integer
     with Post => Test_Case'Result = 522 --  @COUNTEREXAMPLE
   is
      B : Integer;
   begin
      case A is
         when 3 =>
            B := 5;
         when -53 .. -18 =>
            B := 18;
         when 32  .. 48 | 89 =>
            B := 55;
         when others =>
            B := 142;
      end case;
      return B;
   end Test_Case;


   function Test_If_2 (A : Integer) return Integer
     with Post => Test_If_2'Result = 1 --  @COUNTEREXAMPLE
   is
      B : Integer := 0;
   begin
      B := (if A /= 3 Then
               B - 1
            else
               B - 2);
      return B;
   end Test_If_2;

end Test;
