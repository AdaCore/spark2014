package body Test_Stack with SPARK_Mode is

   procedure Push (S : in out My_Stack; E : Integer) is
   begin
      S.Content (S.Top + 1) := E;
      S.Top := S.Top + 1;
   end Push;

   procedure Bad_Push (S : in out My_Stack; E : Integer) is
   begin
      S.Top := S.Top + 1; --@PREDICATE_CHECK:FAIL
      S.Content (S.Top) := E;
   end Bad_Push;

   procedure Pop (S : in out My_Stack; E : out Integer) is
   begin
      E := S.Content (S.Top);
      S.Top := S.Top - 1;
   end Pop;

end;
