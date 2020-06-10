procedure Test_Inline with SPARK_Mode is
   function F1 (X : Integer) return Integer with Import,
     Annotate => (GNATprove, Inline_For_Proof);
   function F2 (X : Integer) return Integer with Import,
     Annotate => (GNATprove, Inline_For_Proof),
     Post => F2'Result + 1 = 15;
   function F3 (X : Integer) return Integer with Import,
     Annotate => (GNATprove, Inline_For_Proof),
     Post => F3'Result = 14;
   pragma Postcondition (F3'Result + 1 = 15);
begin
   null;
end Test_Inline;
