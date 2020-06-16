procedure Test_CodePeer_Init with SPARK_Mode is
   type R is record
      X : Integer;
   end record;

   procedure Bad (X : out R) with
     Relaxed_Initialization => X,
     Post => X'Initialized --@POSTCONDITION:FAIL
   is
   begin
      null;
   end Bad;
begin
   null;
end Test_CodePeer_Init;
