procedure Main with SPARK_Mode is

   type R is record
      F, G : Integer;
   end record;

   type RR is new R with Relaxed_Initialization;

   type RR_Access is access RR;

   P1 : RR_Access := new RR'(others => 1);
   O  : RR;
   P2 : RR_Access := new RR'(O);
begin
   pragma Assert (P1 /= null);
   pragma Assert (P2 /= null);
   pragma Assert (P1.all'Initialized);
   pragma Assert (P2.all'Initialized); --  @ASSERT:FAIL
end Main;
