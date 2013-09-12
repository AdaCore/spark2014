procedure CXD4006 is
   pragma SPARK_Mode (Off);
   task Distributor is
      entry Nb_waiting;
   end Distributor;

   procedure Await_Arrival is
   begin
      Distributor.Nb_waiting;
   end Await_Arrival;

   task body Distributor is
   begin
      null;
   end Distributor;

   protected Priority_Normal is
    procedure Check;
  private
    Count : Integer := 0;
  end Priority_Normal;

  protected body Priority_Normal is
    procedure Check is
    begin
       null;
    end Check;
  end Priority_Normal;

  procedure Assert_High_Priority is
  begin
    Priority_Normal.Check;
  end Assert_High_Priority;


begin
   null;
end CXD4006;
