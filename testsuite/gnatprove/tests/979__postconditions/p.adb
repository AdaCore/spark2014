procedure P with SPARK_Mode is
   procedure Double_Post_1 (X : out Integer) with
     Post => X >= 0; -- @POSTCONDITION:FAIL
   pragma Postcondition (X <= 100);
   procedure Double_Post_1 (X : out Integer) is
   begin
      X := -10;
   end Double_Post_1;

   procedure Double_Post_2 (X : out Integer) with
     Post => X >= 0;
   pragma Postcondition (X <= 100); -- @POSTCONDITION:FAIL
   procedure Double_Post_2 (X : out Integer) is
   begin
      X := 200;
   end Double_Post_2;
begin
   null;
end;
