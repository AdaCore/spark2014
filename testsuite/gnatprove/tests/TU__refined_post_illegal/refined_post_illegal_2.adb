package body Refined_Post_Illegal_2
  with SPARK_Mode
is
   procedure P1 (Par : out Integer)
     with Refined_Post => Par > 10
     --  Refined_Post should imply abstract Post but in this
     --  case it does not.
   is
   begin
      Par := 11;
   end P1;


   function F1 return Boolean is (True);


   procedure Calls_F1 is
      Temp : Boolean := F1;
   begin
      pragma Assert (not Temp);  --  This should not be provable
      null;
   end Calls_F1;


   procedure P2 (Par1, Par2 : Integer ; Par3 : out Integer)
     with Refined_Post => Par3 > 0
   is
   begin
      --  Both the abstract Post and the Refined_Post are
      --  true but the Pre and the Refined_Post are not
      --  strong enough to imply the abstract Post.
      if Par2 > Par1 then
         Par3 := Par1 * Par2;
      else
         Par3 := Par1 * Par1;
      end if;
   end P2;
end Refined_Post_Illegal_2;
